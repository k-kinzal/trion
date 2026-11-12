//! What passes the check is read entirely: a word of logic, time, order or
//! number that stands in an open place of the syntax tree is read by a rule
//! or the statement is rejected, whatever atom its words end up in.

mod common;
use common::*;

const HEAD: &str = "primitive server\nprimitive message\nprimitive client\nprimitive block\nprimitive header\n\n";

fn check(text: &str) -> serde_json::Value {
    Fixture::new(&[("a.trion", &format!("{HEAD}{text}"))]).trion(&["verify", "--json", "a.trion"]).json()
}

fn model(text: &str) -> String {
    Fixture::new(&[("a.trion", &format!("{HEAD}{text}"))]).inspect(&["model", "a.trion"]).stdout
}

fn unread(text: &str) -> Vec<String> {
    check(text)["opaque"].as_array().unwrap().iter().map(|d| d["message"].as_str().unwrap().to_string()).collect()
}

fn rejected(text: &str, word: &str) -> bool {
    unread(text).iter().any(|m| m.contains(&format!("`{word}`")))
}

#[test]
fn a_function_word_in_any_open_place_is_rejected_or_changes_the_model() {
    let base = "[A]\nThe server shall send the message to the client.\n";
    let plain = model(base);
    // Each sentence puts one word of logic, time, order or number in one open
    // place: before a head, as a head, inside a predicate, as a manner.
    let cases = [
        ("The server shall send the first message to the client.", "first"),
        ("The server shall send the message to the previous client.", "previous"),
        ("The server shall send the message to another client.", "another"),
        ("The server shall send a single message to the client.", "single"),
        ("The server shall send multiple messages to the client.", "multiple"),
        ("The server shall periodically send the message to the client.", "periodically"),
        ("The server shall send the message repeatedly to the client.", "repeatedly"),
        ("The first server shall send the message to the client.", "first"),
        ("The server is still ready.", "still"),
        ("The server shall send the message to the client alone.", "alone"),
    ];
    for (sentence, word) in cases {
        let text = format!("[A]\n{sentence}\n");
        let read = model(&text) != plain || sentence.contains(" is ");
        assert!(read, "{sentence}");
        assert!(rejected(&text, word), "`{word}` passes unread in: {sentence}\n{:?}", unread(&text));
    }
}

#[test]
fn the_subject_of_a_statement_is_checked_as_its_action_is() {
    // The name of an action was scanned for unread words; the subject was not.
    assert!(rejected("[A]\nThe later server shall send the message.\n", "later"));
    assert!(rejected("[A]\nWhen the last server stops, the client shall send the message.\n", "last"));
}

#[test]
fn an_order_of_occurrences_is_rejected_where_it_is_not_read() {
    // The temporal shape reads a counted run, an order of occurrences and an adverb of time.
    assert!(unread("[A]\nThe server shall send the message twice in a row.\n").is_empty());
    assert!(model("[A]\nThe server shall send the message twice in a row.\n").contains("in a row: the longest run of completions"));
    // Where the shape has no reading for them, the statement is rejected with the reason.
    let codes = |text: &str| report_codes(&check(text));
    assert_eq!(codes("[A]\nThe server shall send the message in a row.\n"), ["UNRESOLVED_TEMPORAL_SCOPE"]);
    assert_eq!(codes("primitive retry\n\n[A]\nThe server shall send the message after the first retry.\n"), ["UNRESOLVED_TEMPORAL_SCOPE"]);
    assert_eq!(codes("[A]\nThe server shall immediately send the message.\n"), ["UNRESOLVED_TEMPORAL_SCOPE"]);
    // An order word that names no occurrence of a response is still unread.
    assert!(rejected("[A]\nThe server shall send the later message.\n", "later"));
    // `eventually` adds nothing to an obligation without a deadline.
    assert!(unread("[A]\nThe server shall eventually send the message.\n").is_empty());
}

#[test]
fn a_phrase_after_a_subject_noun_restricts_the_noun() {
    // `a block introduced by a header` is `a block that is introduced by a header`.
    let short = model("[A]\nEach block introduced by a header shall end.\n");
    let long = model("[A]\nEach block that is introduced by a header shall end.\n");
    assert_eq!(short, long);
    let short = model("[A]\nEach message inside a block shall end.\n");
    let long = model("[A]\nEach message that is inside a block shall end.\n");
    assert_eq!(short, long);
    assert!(unread("[A]\nEach block introduced by a header shall end.\n").is_empty());
}

#[test]
fn an_adverb_before_the_verb_is_the_manner_of_the_verb() {
    // `securely` is no verb: the action is `store`, and storing securely is storing.
    let model = model("[A]\nThe server shall securely store the message.\n\n[B]\nThe server shall not store the message.\n");
    assert!(model.contains("store securely message"), "{model}");
    assert!(!model.contains("securely store"), "{model}");
    let report = check("[A]\nThe server shall securely store the message.\n\n[B]\nThe server shall not store the message.\n");
    assert!(report_codes(&report).contains(&"contradiction".to_string()), "{report}");
    // A verb in `-ly` stays a verb.
    assert!(model_of_apply().contains("apply"), "{}", model_of_apply());
}

fn model_of_apply() -> String {
    model("[A]\nThe server shall apply the message.\n")
}

#[test]
fn more_than_and_fewer_than_count_as_a_determiner() {
    let more = model("[A]\nWhen the server receives more than one message, the server shall stop.\n");
    let fewer = model("[A]\nWhen the server receives fewer than 3 messages, the server shall stop.\n");
    let condition = |model: &str| model.lines().find(|l| l.contains("assume:")).map(str::to_string);
    assert!(condition(&more).is_some_and(|c| c.contains("at least 2")), "{more}");
    assert!(condition(&fewer).is_some_and(|c| c.contains("at most 2")), "{fewer}");
    assert!(unread("[A]\nWhen the server receives more than one message, the server shall stop.\n").is_empty());
}

#[test]
fn a_nominal_predicate_names_classes() {
    let model = model("[A]\nEach message is a part of a block or a header.\n");
    assert!(model.contains('∨'), "{model}");
    assert!(unread("[A]\nEach message is a part of a block or a header.\n").is_empty());
}

#[test]
fn an_order_word_is_read_inside_a_declared_term() {
    let text = "A first message means a message of a sequence that no message of that sequence precedes.\n\n[A]\nThe server shall send the first message.\n";
    assert!(unread(text).is_empty(), "{:?}", unread(text));
    assert!(rejected("[A]\nThe server shall send the first message.\n", "first"));
}

#[test]
fn a_purpose_is_rejected() {
    let messages = unread("[A]\nThe server shall send the message so that the client stops.\n");
    assert!(messages.iter().any(|m| m.contains("so that")), "{messages:?}");
    let messages = unread("[A]\nThe server shall send the message, in order to stop the client.\n");
    assert!(messages.iter().any(|m| m.contains("in order to")), "{messages:?}");
}
