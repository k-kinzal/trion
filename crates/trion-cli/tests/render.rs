//! `trion doc`: a verified package as one self-contained document.

mod common;
use common::*;

const MANIFEST: &str = "[package]\nname = \"p\"\n";

/// The document of a package of one file. A document is written of a
/// verified package only, so `terms` names the terms of the statements that
/// the file does not define: each is declared primitive in a file of its own.
fn render_with(namespace: &str, terms: &[&str], spec: &str) -> String {
    let declared: String = terms.iter().map(|term| format!("primitive {term}\n")).collect();
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", spec), ("terms.trion", &format!("namespace {namespace}\n{declared}"))]);
    let r = f.trion(&["doc"]);
    assert_eq!(r.code, 0, "{}{}", r.stderr, f.trion(&["verify"]).stdout);
    r.stdout
}

fn render(terms: &[&str], spec: &str) -> String {
    render_with("p", terms, spec)
}

/// The text of the document without its tags.
fn text_of(html: &str) -> String {
    let mut out = String::new();
    let mut in_tag = false;
    for c in html.chars() {
        match c {
            '<' => in_tag = true,
            '>' => in_tag = false,
            other if !in_tag => out.push(other),
            _ => {}
        }
    }
    out
}

#[test]
fn a_package_reads_as_one_document_in_its_authored_order() {
    let spec = "namespace p.room\n\nsection \"Room types\"\n\nA room means a space. Each room has one door.\n[ROOM-OPEN] The API shall open the room.\n\nThe API shall log the door.\n\nsection \"Members\"\n\n[MEMBER] The API shall list the members.\n";
    let html = render_with("p.room", &["API", "door", "member"], spec);
    assert!(html.starts_with("<!DOCTYPE html>"), "{html}");
    assert!(html.contains("edition test"), "{html}");
    // Sections are headings, and the contents link to them in order.
    let types = html.find(">Room types</h3>").expect("a heading");
    let members = html.find(">Members</h3>").expect("a second heading");
    assert!(types < members);
    assert!(html.contains("<a href=\"#sec-a-trion-room-types\">Room types</a>"), "{html}");
    assert!(html.contains("<a href=\"#sec-a-trion-members\">Members</a>"));
    // Neighbouring sentences stay one paragraph; a blank line starts another.
    let paragraphs: Vec<&str> = html.split("<p class=\"para\">").skip(1).map(|p| p.split("</p>").next().unwrap()).collect();
    assert_eq!(paragraphs.len(), 3, "{paragraphs:?}");
    assert_eq!(paragraphs[0].matches("class=\"st\"").count(), 3, "{}", paragraphs[0]);
    assert!(text_of(paragraphs[0]).contains("A room means a space."));
    assert!(text_of(paragraphs[0]).contains("ROOM-OPEN The API shall open the room."));
    // An identifier is an anchor that links to its statement.
    assert!(html.contains("id=\"ROOM-OPEN\""));
    assert!(html.contains("<a class=\"id\" href=\"#ROOM-OPEN\">ROOM-OPEN</a>"));
    assert!(html.contains("namespace <code>p.room</code>"));
}

#[test]
fn explicit_scopes_and_action_lists_keep_their_nesting() {
    let spec = "For each request R:\n    When the API receives R:\n        [LOG] The API shall log R. The API shall count R.\n\n[DO] When the bell rings, the API shall perform the following actions in order:\n    [DO/stop] stop;\n    perform all of the following actions:\n        log the stop;\n        notify the owner;\nnote \"A note with <b> & more.\"\n";
    let html = render(&["API", "bell", "owner", "stop"], spec);
    let outer = html.find("<div class=\"scope-head\">For each request R:</div>").expect("the outer scope");
    let inner = html.find("<div class=\"scope-head\">When the API receives R:</div>").expect("the inner scope");
    let statement = html.find("id=\"LOG\"").expect("the statement");
    assert!(outer < inner && inner < statement);
    assert_eq!(html.matches("<div class=\"scope\"").count(), 2);
    // An ordered list is ordered, and a nested list keeps its operator.
    let list = &html[html.find("<ol class=\"acts\">").expect("an ordered list")..];
    assert!(list.contains("id=\"DO/stop\""), "{list}");
    assert!(list.contains("<span class=\"op\">perform all of the following actions:</span>"), "{list}");
    assert!(list.contains("<ul class=\"acts\">"));
    assert!(text_of(list).contains("notify the owner;"));
    // Text is escaped.
    assert!(html.contains("A note with &lt;b&gt; &amp; more."), "{html}");
    assert!(!html.contains("<b> &"));
}

#[test]
fn a_term_links_to_its_definition_and_shows_it() {
    let spec = "[ROOM] A room means a space with a door.\n[OPEN] The API shall open the rooms.\n    detailed by [SHUT]\n[SHUT] The API shall close the room.\n";
    let html = render(&[], spec);
    // Every occurrence links to the defining statement and carries its text.
    let link = "<a class=\"term defined\" href=\"#ROOM\" title=\"A room means a space with a door.\">";
    assert!(html.contains(&format!("{link}rooms</a>")), "{html}");
    assert!(html.contains(&format!("{link}room</a>")), "{html}");
    // A term that statements only use is derived, and the glossary says so.
    let glossary = &html[html.find("id=\"glossary\"").expect("a glossary")..];
    assert!(glossary.contains("<small>defined"), "{glossary}");
    assert!(text_of(glossary).contains("A room means a space with a door."));
    assert!(glossary.contains("defined at <a href=\"#ROOM\">"), "{glossary}");
    assert!(html.contains("class=\"term derived\""), "{html}");
    assert!(glossary.contains("<small>derived"), "{glossary}");
    // A word inside a quoted string is data.
    let quoted = render(&["API"], "[ROOM] A room means a space.\n[SAY] The API shall print \"room\".\n");
    assert!(quoted.contains("print &quot;room&quot;."), "{quoted}");
}

const DIAGRAMS: &str = "[C] concept:\n    [C/customer] each order -> has -> exactly one customer;\n    each order -> contains -> one or more items;\n\n[F] When the checker receives a result R, the checker shall follow this flow:\n    step inspect: read R;\n    step good: publish R;\n    step bad: reject R;\n    start inspect\n    choose after inspect:\n        when R is valid -> good\n        otherwise -> bad\n    finish good\n    finish bad\n";

#[test]
fn a_diagram_is_drawn_as_a_figure() {
    let html = render(&["checker", "result"], DIAGRAMS);
    let figures: Vec<&str> = html.split("<svg ").skip(1).map(|s| s.split("</svg>").next().unwrap()).collect();
    assert_eq!(figures.len(), 2, "{html}");
    // The concept graph: one node for each type, one labelled edge for each line.
    let concept = figures[0];
    for node in ["order", "customer", "item"] {
        assert_eq!(concept.matches(&format!("<text class=\"name\"") ).count(), 3, "{concept}");
        assert!(concept.contains(&format!(">{node}</text>")), "{node}: {concept}");
    }
    assert!(concept.contains(">has exactly one</text>"), "{concept}");
    assert!(concept.contains(">contains one or more</text>"), "{concept}");
    assert_eq!(concept.matches("<path class=\"wire\"").count(), 2);
    // The flowchart: a start, the steps with their actions, a choice with its guards, a finish.
    let flow = figures[1];
    for label in [">inspect</text>", ">read R</text>", ">good</text>", ">bad</text>", ">R is valid</text>", ">otherwise</text>"] {
        assert!(flow.contains(label), "{label}: {flow}");
    }
    assert_eq!(flow.matches("<polygon").count(), 1, "{flow}");
    assert_eq!(flow.matches("<circle class=\"ring\"").count(), 1, "{flow}");
    // start, step to choice, two guarded edges, two finishes
    assert_eq!(flow.matches("<path class=\"wire\"").count(), 6, "{flow}");
}

#[test]
fn a_figure_stands_beside_the_controlled_english_it_means() {
    let html = render(&["checker", "result"], DIAGRAMS);
    let concept = &html[html.find("<figure class=\"diagram concept\"").unwrap()..];
    let concept = &concept[..concept.find("</figure>").unwrap()];
    assert!(concept.contains("<details open><summary>Controlled English of this diagram</summary>"), "{concept}");
    let words = text_of(concept);
    assert!(words.contains("Each order has exactly one customer."), "{words}");
    assert!(words.contains("Each order contains one or more items."), "{words}");
    // An identified edge is a statement that can be linked.
    assert!(concept.contains("id=\"C/customer\""), "{concept}");
    let flow = &html[html.find("<figure class=\"diagram flow\"").unwrap()..];
    let flow = &flow[..flow.find("</figure>").unwrap()];
    let expansion = &flow[flow.find("<pre class=\"expansion\">").expect("an expansion")..];
    assert!(expansion.contains("When the checker receives a result, the checker shall"), "{expansion}");
    assert!(flow.contains("<summary>Authored notation</summary>"));
}

#[test]
fn a_statement_shows_its_warnings_and_sources() {
    let requirement = "The API stops.\n";
    let source = source_block("R", "requirement", "r.txt", requirement, "", &[("STOP", "The API stops.")]);
    let spec = format!("{source}primitive API\n[A] The API shall stop.\n    cite R#STOP\n[B] The API shall start.\n    unsourced \"Nobody asked.\"\n");
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", &spec), ("r.txt", requirement)]);
    let r = f.trion(&["doc"]);
    assert_eq!(r.code, 0, "{}{}", r.stderr, f.trion(&["verify"]).stdout);
    let html = r.stdout;
    // The verdict of the whole package, with the bounds of the result.
    let status = html.split("id=\"status\"").nth(1).expect("a status").split("</section>").next().unwrap();
    assert!(status.starts_with("><strong>consistent</strong>: 2 statements shown; the package is verified with 1 warnings"), "{status}");
    assert!(text_of(status).contains("within traces of 3 moments"), "{status}");
    assert!(status.contains("source R: 100.00% cited"), "{status}");
    // A warning stands on its statement, and on no other.
    let of = |id: &str| html.split(&format!("class=\"st\" id=\"{id}\"")).nth(1).expect("the statement").split("</p>").next().unwrap().to_string();
    assert!(of("B").contains("<span class=\"badge warn\"") && of("B").contains(">unsourced</span>"), "{}", of("B"));
    assert!(!of("A").contains("class=\"badge"), "{}", of("A"));
    // Sources: the quoted text of a citation, and the reason of a statement without one.
    assert!(html.contains("<span class=\"mark cite\" title=\"R#STOP: The API stops.\">"), "{html}");
    assert!(html.contains("<span class=\"mark unsourced\" title=\"Nobody asked.\">unsourced</span>"), "{html}");
}

#[test]
fn the_document_needs_nothing_but_itself() {
    let html = render(&["checker", "result"], DIAGRAMS);
    for outside in ["<script", "<link", "<img", "<iframe", " src=", "@import", "url(http", "https://"] {
        assert!(!html.contains(outside), "{outside}");
    }
    // The only address is the name of the SVG vocabulary.
    assert_eq!(html.matches("http://").count(), html.matches("xmlns=\"http://www.w3.org/2000/svg\"").count());
    assert!(html.contains("<style>"));
    assert!(html.contains("prefers-color-scheme: dark"));
    // The same package renders to the same bytes.
    assert_eq!(html, render(&["checker", "result"], DIAGRAMS));
}

#[test]
fn each_element_names_its_file_and_line() {
    let spec = "section \"S\"\n\n[A] The API shall stop. The bell shall\nring.\nWhen the door opens:\n    [B] The API shall log the door.\n";
    let html = render(&["API", "bell", "door"], spec);
    // The fixture puts the namespace line first, so the section is on line 2.
    assert!(html.contains("id=\"sec-a-trion-s\" data-file=\"a.trion\" data-line=\"2\">S</h3>"), "{html}");
    assert!(html.contains("id=\"A\" data-file=\"a.trion\" data-line=\"4\""), "{html}");
    // The second sentence begins on the line of the first one, so its column tells them apart.
    let second = &html[html.find("id=\"s-a-trion-4-").expect("a statement named by line and column")..];
    assert!(second[..60].contains("data-file=\"a.trion\" data-line=\"4\""), "{}", &second[..60]);
    assert!(html.contains("<div class=\"scope\" data-file=\"a.trion\" data-line=\"6\">"), "{html}");
    assert!(html.contains("id=\"B\" data-file=\"a.trion\" data-line=\"7\""), "{html}");
}

#[test]
fn one_file_can_be_rendered_and_written_to_a_file() {
    let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", "primitive API\nprimitive bell\n[A] The API shall stop.\n"), ("sub/b.trion", "[B] The bell shall ring.\n")]);
    let whole = f.trion(&["doc"]).stdout;
    assert!(whole.contains("id=\"A\"") && whole.contains("id=\"B\""), "{whole}");
    // Files follow the order of their includes.
    assert!(whole.find("id=\"file-a-trion\"").unwrap() < whole.find("id=\"file-sub-b-trion\"").unwrap());
    let r = f.trion(&["doc", "--file", "sub/b.trion", "--out", "out/b.html"]);
    assert_eq!((r.code, r.stdout.as_str()), (0, ""), "{}", r.stderr);
    let one = f.read("out/b.html");
    assert!(one.contains("id=\"B\"") && !one.contains("id=\"A\""), "{one}");
    assert!(one.contains("<title>p: sub/b.trion</title>"));
    let missing = f.trion(&["doc", "--file", "nowhere.trion"]);
    assert_eq!(missing.code, 2, "{}", missing.stderr);
    assert!(missing.stderr.contains("no file of package `p` is `nowhere.trion`"), "{}", missing.stderr);
}

#[test]
fn a_refinement_is_linked_from_both_of_its_sides() {
    let spec = "[TOP] The API shall keep each record.\n    detailed by [SAVE], [LOAD]\n[SAVE] The API shall save each record.\n[LOAD] The API shall load each record.\n";
    let html = render(&[], spec);
    let top = html.split("id=\"TOP\"").nth(1).unwrap().split("</p>").next().unwrap();
    assert!(top.contains("detailed by <a href=\"#SAVE\">SAVE</a>, <a href=\"#LOAD\">LOAD</a>"), "{top}");
    let save = html.split("id=\"SAVE\"").nth(1).unwrap().split("</p>").next().unwrap();
    assert!(save.contains("details <a href=\"#TOP\">TOP</a>"), "{save}");
    // The refinement line is no sentence of the document.
    assert!(!text_of(&html).contains("detailed by [SAVE]. "), "{html}");
}

#[test]
fn the_glossary_names_primitives_and_the_statements_that_relate_a_term() {
    let spec = "primitive account\nA guest means a user without an account.\n[IN] Each guest is a visitor.\n[OUT] No guest is a member.\n[A] The guest shall log in.\n[B] The user shall open an account.\n";
    let html = render(&["user"], spec);
    let glossary = html.split("id=\"glossary\"").nth(1).expect("a glossary");
    let entry = |term: &str| glossary.split(&format!(">{term} <small>")).nth(1).unwrap_or_else(|| panic!("no entry {term}: {glossary}")).split("</dd>").next().unwrap().to_string();
    assert!(entry("guest").starts_with("defined"), "{}", entry("guest"));
    assert!(entry("guest").contains("related by:") && entry("guest").contains("Each guest is a visitor.") && entry("guest").contains("No guest is a member."), "{}", entry("guest"));
    assert!(entry("account").starts_with("primitive"), "{}", entry("account"));
}

#[test]
fn a_package_that_is_not_verified_has_no_document() {
    // A contradiction and a statement that constrains nothing: neither is shown as if it were verified.
    for spec in ["primitive API\n[A] The API shall stop.\n[B] The API shall not stop.\n", "[LONE] The gadget shall frobnicate the widget.\n"] {
        let f = Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", spec)]);
        let r = f.trion(&["doc", "--out", "out/p.html"]);
        assert_eq!((r.code, r.stdout.as_str()), (2, ""), "{}", r.stderr);
        assert!(r.stderr.contains("the package is not verified (gate check)"), "{}", r.stderr);
        assert!(!f.path().join("out/p.html").exists(), "a document was written");
    }
}

#[test]
fn a_priority_is_shown_on_the_winner_and_on_the_loser() {
    let spec = "[OPEN] The door shall be open.\n[ALARM] While the alarm is active, the door shall be closed.\n    overrides [OPEN]\n[S] The API should log the call.\n    weight 3\n[D] The API shall accept the request.\n    default\n";
    let html = render(&["API", "call", "request"], spec);
    let of = |id: &str| html.split(&format!("id=\"{id}\"")).nth(1).unwrap().split("</p>").next().unwrap().to_string();
    assert!(of("ALARM").contains("overrides <a href=\"#OPEN\">OPEN</a>"), "{}", of("ALARM"));
    assert!(of("OPEN").contains("overridden by <a href=\"#ALARM\">ALARM</a>"), "{}", of("OPEN"));
    // The condition under which the loser yields is told with the mark.
    assert!(of("OPEN").contains("does not apply where Val(alarm, active)"), "{}", of("OPEN"));
    assert!(of("S").contains(">weight 3<"), "{}", of("S"));
    assert!(of("D").contains(">default<"), "{}", of("D"));
    let status = html.split("id=\"status\"").nth(1).unwrap().split("</section>").next().unwrap();
    assert!(status.contains("priorities: ALARM overrides OPEN"), "{status}");
    // The priority lines are no sentences of the document.
    let text = text_of(&html);
    assert!(!text.contains("overrides [OPEN]. ") && !text.contains("default. "), "{text}");
}

#[test]
fn the_status_says_how_far_the_situations_were_examined() {
    let apart = "[J1] When a user sends a message, the API shall store the message.\n[J2] When a user deletes a message, the API shall log the message.\n";
    let html = render(&["user", "message", "API"], apart);
    let status = html.split("id=\"status\"").nth(1).unwrap().split("</section>").next().unwrap().to_string();
    assert!(status.contains("situations: each of the 1 largest situations of the 2 conditions was examined") && status.contains("the statements can all be kept in each situation"), "{status}");
    // The control declarations are shown as declarations.
    let declared = "environment user\nsystem API\n[E2] When the user sends a message, the API shall store the message.\n";
    let html = render(&["user", "message", "API"], declared);
    assert!(html.contains("<code>environment user</code>") && html.contains("<code>system API</code>"), "{html}");
    assert!(!html.contains("<script"));
}
