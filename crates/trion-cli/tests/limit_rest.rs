//! Bound objects, counted occurrences, the game of one round and relations
//! between runs: limits of the reading that are crossed.

mod common;
use common::*;
use serde_json::Value;

fn package(text: &str) -> Fixture {
    Fixture::new(&[("trion.toml", "[package]\nname = \"x\"\n"), ("a.trion", text)])
}

fn check_with(flags: &[&str], text: &str) -> Value {
    let mut args = vec!["verify", "--json"];
    args.extend(flags);
    package(text).trion(&args).json()
}

fn check(text: &str) -> Value {
    check_with(&[], text)
}

fn codes(text: &str) -> Vec<String> {
    report_codes(&check(text))
}

/// As `codes`, reading the diagnostics of the analysis alone: no finding of
/// another list of the report is read, so an empty result is no success.
#[allow(dead_code)]
fn codes_of_the_analysis(text: &str) -> Vec<String> {
    analysis_codes(&check(text))
}

fn model(text: &str) -> String {
    package(text).inspect(&["model"]).stdout
}

#[test]
fn an_object_that_a_response_introduces_is_one_thing_of_its_binding() {
    let shared = "[D]\nWhen the checker completes an analysis A,\nthe checker shall perform the following actions in order:\n    create an analysis report R for A;\n    retain R;\n";
    let text = model(shared);
    let mark = text.split("create ").nth(1).and_then(|rest| rest.split(' ').next()).unwrap().to_string();
    // The mark names the variable and the statement, so the binding is the statement's own.
    assert_eq!(mark, "#R@D/2", "{text}");
    assert!(text.contains(&format!("retain {mark} analysis report")), "{text}");
    // What is forbidden of every analysis report is forbidden of that one.
    assert_eq!(codes(&format!("{shared}\n[E]\nThe checker shall not retain an analysis report.\n")), ["contradiction"]);
    // Two bindings of one type and one letter are two objects; nothing makes them one or keeps them apart.
    let apart = "[D1]\nWhen the bell rings, the checker shall create a report R and shall retain R.\n\n[D2]\nWhen the bell rings, the checker shall create a report R and shall not retain R.\n";
    assert!(codes(apart).is_empty(), "{:?}", codes(apart));
    // In one statement the object is one: it cannot be retained and not retained.
    let one = "[D3]\nWhen the bell rings, the checker shall create a report R, shall retain R, and shall not retain R.\n";
    assert!(!codes(one).is_empty());
    // An object of a condition stays every object of its type.
    assert_eq!(codes("[G1]\nWhen the checker completes an analysis A, the checker shall log A.\n\n[G2]\nWhen the checker completes an analysis B, the checker shall not log B.\n"), ["contradiction"]);
    // An author reads the type, and a generated view writes the variable again.
    let f = package(shared);
    let expansion = f.inspect(&["expand"]).stdout;
    assert!(expansion.contains("create an analysis report for the analysis;") && !expansion.contains('#'), "{expansion}");
    let view = f.inspect(&["diagram", "flow", "D"]).stdout;
    assert!(view.contains("step s1: create an analysis report R for the analysis;") && view.contains("step s2: retain R;"), "{view}");
}

#[test]
fn how_often_an_action_occurs_is_a_quantity_of_its_activation() {
    let text = model("[C1]\nWhen a request fails, the API shall retry the request at most 3 times.\n");
    assert!(text.contains("Act(API|retry request)") && text.contains("API|retry request occurrences ≤ 3 times"), "{text}");
    assert_eq!(codes("[C1]\nWhen a request fails, the API shall retry the request at most 3 times.\n\n[C2]\nWhen a request fails, the API shall retry the request at least 5 times.\n"), ["contradiction"]);
    assert!(codes("[C1]\nWhen a request fails, the API shall retry the request at most 3 times.\n\n[C3]\nWhen a request fails, the API shall retry the request twice.\n").is_empty());
    // The count is no part of the action: a prohibition of the action meets it.
    assert_eq!(codes("[C3]\nWhen a request fails, the API shall retry the request twice.\n\n[C4]\nWhen a request fails, the API shall not retry the request.\n"), ["contradiction"]);
    let report = check("[C3]\nWhen a request fails, the API shall retry the request twice.\n");
    assert!(report["opaque"].as_array().unwrap().is_empty(), "{report}");
}

#[test]
fn a_deadline_is_measured_from_the_occurrence_that_a_noun_names() {
    let retry = "[R1]\nWhen a request fails, the API shall retry the request.\n\n";
    let named = format!("{retry}[O1]\nWhen the timer expires, the API shall respond within 5 seconds of the last retry.\n");
    assert!(codes_of_the_analysis(&named).is_empty(), "{:?}", codes_of_the_analysis(&named));
    let text = model(&named);
    assert!(text.contains("Act(API|respond)") && !text.contains("respond of last retry"), "{text}");
    assert!(text.contains("measured from last retry"), "{text}");
    // No event of the package is a failure, so the deadline has nothing to be measured from.
    let report = check("[O2]\nWhen the timer expires, the API shall respond within 5 seconds of the last failure.\n");
    assert_eq!(analysis_codes(&report), ["UNRESOLVED_TEMPORAL_SCOPE"], "{report}");
    assert!(report["diagnostics"][0]["message"].as_str().unwrap().contains("no event of the package is an occurrence of `failure`"));
    // `fail` is the verb of `failure`.
    assert!(codes_of_the_analysis("[O3]\nWhen a request fails, the API shall log the request.\n\n[O4]\nWhen the timer expires, the API shall respond within 5 seconds of the last failure.\n").is_empty());
    // An origin at the first or the next occurrence is read: `temporal_order.rs` tests what it says.
    let first = format!("{retry}[O5]\nWhen the timer expires, the API shall respond within 5 seconds of the first retry.\n");
    assert!(codes_of_the_analysis(&first).is_empty(), "{:?}", codes_of_the_analysis(&first));
    assert!(model(&first).contains("measured from first retry"));
}

const THREE: &str = "[K]\nThe mode is fast, slow, or off.\n\n[A]\nWhile the door is open, the mode shall be fast.\n\n[B]\nWhile the alarm is active, the mode shall be slow.\n\n[C]\nWhile the lamp is lit, the API shall log the mode.\n";

#[test]
fn the_statements_are_kept_in_each_situation_or_the_situation_is_a_conflict() {
    let examined = |report: &serde_json::Value| report["consistency"]["situations"].as_str().unwrap_or_default().to_string();
    // The door can be open while the alarm is active, and then the mode cannot be both.
    let met = check(THREE);
    assert_eq!(met["consistency"]["verdict"], "inconsistent");
    assert!(examined(&met).contains("the statements cannot all be kept in 1 situation(s)"), "{met}");
    let conflict = met["diagnostics"].as_array().unwrap().iter().find(|d| d["code"] == "contradiction").unwrap_or_else(|| panic!("{met}"));
    let named: Vec<&str> = conflict["refs"].as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap()).collect();
    assert_eq!(named, ["A", "B"], "{met}");
    // Conditions that a statement without a modal verb excludes are no situation.
    let excluded = format!("{THREE}\n[X]\nWhile the door is open, the alarm is never active.\n");
    let settled = check(&excluded);
    assert!(!report_codes(&settled).contains(&"contradiction".to_string()), "{settled}");
    assert_eq!(settled["consistency"]["verdict"], "consistent");
    assert!(examined(&settled).contains("the statements can all be kept in each situation"), "{settled}");
    // The situations are not listed: thirty conditions are decided by one question.
    let many: String = (0..30).map(|i| format!("[M{i}]\nWhile the gate is `s{i}`, the API shall log the gate.\n\n")).collect();
    let beyond = check(&many);
    assert!(examined(&beyond).contains("every situation was examined through 1 questions, without listing the situations") && examined(&beyond).contains("the statements can all be kept in each situation"), "{}", examined(&beyond));
    // Conditions on states that do not exclude each other have a situation
    // for each combination; statements that share no response are answered apart.
    let apart: String = ["door", "lamp", "valve", "pump", "gate", "fan", "bell", "horn", "lock", "vent", "hatch", "relay"].iter().enumerate().map(|(i, part)| format!("[K{i}]\nThe {part} is open or closed.\n\n[A{i}]\nWhile the {part} is open, the API shall raise the {part} flag.\n\n[B{i}]\nWhile the {part} is closed, the API shall clear the {part} flag.\n\n")).collect();
    let product = check(&apart);
    assert_eq!(product["consistency"]["verdict"], "consistent", "{}", examined(&product));
    // A conflict among many conditions is found all the same.
    let lost = check(&format!("{many}{THREE}"));
    let conflicts: Vec<&serde_json::Value> = lost["diagnostics"].as_array().unwrap().iter().filter(|d| d["code"] == "contradiction").collect();
    assert_eq!(conflicts.len(), 1, "{lost}");
    let named: Vec<&str> = conflicts[0]["refs"].as_array().unwrap().iter().map(|r| r["id"].as_str().unwrap()).collect();
    assert_eq!(named, ["A", "B"], "{lost}");
    // A search that the decision limit ends decides nothing.
    let cut = check_with(&["--decision-limit", "1"], &many);
    assert_eq!(cut["consistency"]["verdict"], "unknown", "{cut}");
}

#[test]
fn the_same_response_for_the_same_request_is_a_function() {
    let h1 = "[H1]\nThe API shall return the same response for the same request.\n";
    let report = check(h1);
    assert!(report["inexpressible"].as_array().unwrap().is_empty() && report["opaque"].as_array().unwrap().is_empty(), "{report}");
    let two = format!("{h1}\n[H2]\nThe API shall return two responses for each request.\n");
    // No request exists, so nothing has two responses.
    assert!(codes(&two).is_empty());
    assert_eq!(codes(&format!("{two}\nThere is a request.\n")), ["contradiction"]);
    assert!(codes(&format!("{h1}\n[H3]\nThe API shall return one response for each request.\n\nThere is a request.\n")).is_empty());
    // A relation between runs that is not this shape is still reported.
    let other = check("[H4]\nThe API shall respond deterministically.\n");
    assert_eq!(other["inexpressible"].as_array().unwrap().len(), 1, "{other}");
}

#[test]
fn a_share_of_a_declared_population_is_a_quantity() {
    let q1 = "[Q1]\nWhen a request arrives, the API shall respond within 200 ms for 99.9 percent of requests.\n";
    // Without a measure the proportion has no reading.
    let bare = check(q1);
    assert_eq!(analysis_codes(&bare), ["UNSUPPORTED_SEMANTICS"], "{bare}");
    assert!(bare["diagnostics"][0]["message"].as_str().unwrap().contains("declare `measure requests`"));
    // Old behaviour: with the measure alone the share was a quantity
    // between 0 and 100 that nothing tied to a behaviour, and the package
    // was verified. A share is a count of the activations of its
    // statement, and only a statement about declared individuals has
    // activations to count.
    let uncounted = check(&format!("measure requests\n\n{q1}"));
    assert!(uncounted["opaque"].as_array().unwrap().iter().any(|d| d["code"] == "UNSUPPORTED_SEMANTICS" && d["message"].as_str().unwrap().contains("(`share-of-representative`)")), "{uncounted}");
    let measured = format!("individuals request\nmeasure requests\n\n{q1}");
    assert!(codes_of_the_analysis(&measured).is_empty(), "{:?}", codes_of_the_analysis(&measured));
    let text = model(&measured);
    assert!(text.contains("API|respond within 200 ms share of requests ≥ 99.9 percent"), "{text}");
    // The bound is on the share: the other requests have no deadline.
    assert!(!text.contains("elapsed"), "{text}");
    assert_eq!(codes_of_the_analysis(&format!("{measured}\n[Q2]\nWhen a request arrives, the API shall respond within 200 ms for at most 90 percent of requests.\n")), ["contradiction"]);
    assert!(codes_of_the_analysis(&format!("{measured}\n[Q3]\nWhen a request arrives, the API shall respond within 200 ms for at most 99.95 percent of requests.\n")).is_empty());
    // The requests that are answered within 200 ms are among those that are
    // answered within 500 ms: the two shares are shares of one population,
    // and the smaller deadline has no greater share. Each deadline had a
    // quantity of its own that nothing related, and the two bounds were kept.
    let wider = format!("{measured}\n[Q5]\nWhen a request arrives, the API shall respond within 500 ms for at most 90 percent of requests.\n");
    assert_eq!(codes_of_the_analysis(&wider), ["contradiction"], "{:?}", codes_of_the_analysis(&wider));
    // A larger share within the larger deadline fits, and so does any share within a smaller one.
    assert!(codes_of_the_analysis(&format!("{measured}\n[Q6]\nWhen a request arrives, the API shall respond within 500 ms for at least 99.95 percent of requests.\n")).is_empty());
    assert!(codes_of_the_analysis(&format!("{measured}\n[Q7]\nWhen a request arrives, the API shall respond within 100 ms for at most 90 percent of requests.\n")).is_empty());
    // A response at all is a response within any deadline or after it.
    assert_eq!(codes_of_the_analysis(&format!("{measured}\n[Q8]\nWhen a request arrives, the API shall respond for at most 90 percent of requests.\n")), ["contradiction"]);
    // The shares of another population are shares of other cases.
    assert!(codes_of_the_analysis(&format!("individuals upload\nmeasure uploads\n\n{measured}\n[Q9]\nWhen an upload arrives, the API shall respond within 500 ms for at most 90 percent of uploads.\n")).is_empty());
    // A share lies between 0 and 100 percent.
    assert_eq!(codes_of_the_analysis("individuals request\nmeasure requests\n\n[Q4]\nWhen a request arrives, the API shall respond for at least 120 percent of requests.\n"), ["contradiction"]);
    // A time after `for` is still a duration.
    assert!(model("[W]\nWhen a request arrives, the API shall wait for 5 seconds.\n").contains("duration"));
}
