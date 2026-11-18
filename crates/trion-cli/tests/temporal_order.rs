//! Words of time and order are read on the bounded trace: an origin at the
//! first or the next occurrence, an order between a completion and an
//! occurrence, `immediately`, `always` and a count `in a row`. What the trace
//! cannot read is rejected with the reason. The formulas themselves are
//! tested in `trion-language/src/reading/temporal.rs`.

mod common;
use common::*;
use serde_json::Value;

const HEAD: &str = "primitive API\nprimitive request\nprimitive timer\nprimitive report\nprimitive door\n\n";
const RETRY: &str = "[R]\nWhen a request fails, the API shall retry the request.\n\n";

fn package(text: &str) -> Fixture {
    Fixture::new(&[("trion.toml", "[package]\nname = \"x\"\n"), ("a.trion", &format!("{HEAD}{text}"))])
}

fn check(text: &str) -> Value {
    package(text).verify(&["--json"]).json()
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

fn rules(text: &str) -> String {
    package(text).inspect(&["model", "--rules"]).stdout
}

#[test]
fn a_deadline_names_the_first_or_the_next_occurrence_as_its_origin() {
    let first = format!("{RETRY}[O]\nWhen the timer expires, the API shall respond within 5 seconds of the first retry.\n");
    assert!(codes_of_the_analysis(&first).is_empty(), "{:?}", codes_of_the_analysis(&first));
    let text = model(&first);
    // The order word is no part of the action and no term of its own.
    assert!(text.contains("Act(API|respond)") && text.contains("measured from first retry"), "{text}");
    let next = format!("{RETRY}[O]\nWhen the timer expires, the API shall respond within 5 seconds of the next retry.\n");
    assert!(codes_of_the_analysis(&next).is_empty(), "{:?}", codes_of_the_analysis(&next));
    assert!(model(&next).contains("measured from next retry"));
    // The two origins give two formulas.
    let unrolled = |text: &str| package(text).inspect(&["model", "--unrolled"]).stdout;
    assert_ne!(unrolled(&first).replace("first", "next"), unrolled(&next));
    // An occurrence that no event of the package is has no origin.
    assert_eq!(codes_of_the_analysis("[O]\nWhen the timer expires, the API shall respond within 5 seconds of the next retry.\n"), ["UNRESOLVED_TEMPORAL_SCOPE"]);
}

#[test]
fn a_time_bound_before_after_bounds_the_delay_of_the_response() {
    let delayed = format!("{RETRY}[O]\nWhen the timer expires, the API shall respond at least 2 seconds after the first failure.\n");
    assert!(codes(&delayed).is_empty(), "{:?}", codes(&delayed));
    let text = model(&delayed);
    // The bound is a bound on the time of the action, not an object of the verb.
    assert!(text.contains("API|respond elapsed ≥ 2000 ms") && !text.contains("respond at least"), "{text}");
    assert!(text.contains("completion at least 2 seconds measured from first failure"), "{text}");
    assert!(rules(&delayed).contains("role-delay"));
    // A delay and a deadline of one action are bounds of one quantity.
    let both = "[A]\nWhen the timer expires, the API shall respond at least 10 seconds after the timer expires.\n\n[B]\nWhen the timer expires, the API shall respond within 5 seconds.\n";
    assert!(model(both).contains("API|respond elapsed ≥ 10000 ms"));
}

#[test]
fn a_completion_and_an_occurrence_are_ordered_on_the_trace() {
    let at_once = "[A]\nWhen the timer expires, the API shall immediately respond.\n\n";
    // The response completes at the next moment, so nothing completes before it.
    let before = format!("{at_once}[B]\nWhen the timer expires, the API shall log the request before the API responds.\n");
    assert_eq!(codes(&before), ["contradiction"]);
    let after = format!("{at_once}[B]\nWhen the timer expires, the API shall log the request after the API responds.\n");
    assert!(codes(&after).is_empty(), "{:?}", codes(&after));
    // Without `immediately` the response may complete later, and the log before it.
    let later = "[A]\nWhen the timer expires, the API shall respond.\n\n[B]\nWhen the timer expires, the API shall log the request before the API responds.\n";
    assert!(codes(later).is_empty(), "{:?}", codes(later));
    // The occurrence that a noun names by its order is the completion of the action of the package.
    let first = "[A]\nWhen the timer expires, the API shall immediately retry the request.\n\n[B]\nWhen the timer expires, the API shall log the request before the first retry.\n";
    assert_eq!(codes(first), ["contradiction"]);
    let last = "[A]\nWhen the timer expires, the API shall immediately retry the request.\n\n[B]\nWhen the timer expires, the API shall log the request after the last retry.\n";
    assert!(codes(last).is_empty(), "{:?}", codes(last));
    let text = model(first);
    assert!(text.contains("Act(API|log request)") && !text.contains("first retry)"), "{text}");
    assert!(text.contains("before event first retry: the response completes before the occurrence"), "{text}");
    assert!(rules(first).contains("order-of-occurrence"));
}

#[test]
fn a_word_of_time_without_a_reading_is_rejected_with_the_reason() {
    let message = |text: &str| {
        let report = check(text);
        assert_eq!(analysis_codes(&report), ["UNRESOLVED_TEMPORAL_SCOPE"], "{report}");
        report["diagnostics"][0]["message"].as_str().unwrap().to_string()
    };
    assert!(message("[A]\nWhen the timer expires, the API shall log the request before the first retry.\n").contains("no event of the package is an occurrence of `retry`"));
    assert!(message("[A]\nWhen the timer expires, the API should not log the request before the API sends the report.\n").contains("a permission or advice with `before` has no reading"));
    assert!(message("[A]\nWhen the timer expires, the API may log the request before the API sends the report.\n").contains("a permission or advice with `before` has no reading"));
    assert!(message("[A]\nWhile the door is open, the API shall log the request before the API sends the report.\n").contains("a statement under `While` has no activation"));
    assert!(message("[A]\nThe API shall immediately respond.\n").contains("the statement has no trigger"));
    assert!(message("[A]\nWhen the timer expires, the API shall not always respond.\n").contains("forbids nothing"));
    assert!(message("[A]\nWhen the timer expires, the API should not immediately respond.\n").contains("has no reading"));
    assert!(message("[A]\nWhen the timer expires, the API shall not retry the request at most 2 times in a row.\n").contains("forbids a run of a stated length"));
    // A bare noun after `before` names an occurrence, whatever stands around the statement.
    assert!(message("[A]\nWhen the timer expires, the API shall log the request before the header.\n").contains("no event of the package is an occurrence of `header`"));
    assert!(message("[A]\nWhen the timer expires, the API shall retry the request in a row.\n").contains("the action has no count"));
    assert!(message(&format!("{RETRY}[A]\nWhen the timer expires, the API shall log the request before the last retry.\n")).contains("known only when the trace ends"));
}

#[test]
fn always_is_a_completion_at_each_moment() {
    let never_after = "[B]\nWhen the door opens, the API shall not log the request.\n";
    // An action that is done at some moment may be done before the door
    // opens: [B] forbids the log only at the moments after the opening
    // (spec/semantics/core.md, section 4). A system that logs at the first
    // moment keeps both statements whenever the environment opens the door,
    // so the package is consistent. This test asserted a contradiction while
    // consistency was read from one situation at one moment, in which both
    // statements apply and the log of [A] had to come after the opening;
    // over whole behaviours that reading was wrong.
    let once = check(&format!("[A]\nThe API shall log the request.\n\n{never_after}"));
    assert!(report_codes(&once).is_empty(), "{once}");
    assert_eq!(verdicts(&once).get("consistency").map(String::as_str), Some("proved"), "{once}");
    // `always` requires the log at each moment, the moments after an opening as well.
    let always = check(&format!("[A]\nThe API shall always log the request.\n\n{never_after}"));
    assert_eq!(report_codes(&always), ["contradiction"], "{always}");
    assert_eq!(verdicts(&always).get("consistency").map(String::as_str), Some("refuted"), "{always}");
    let text = model("[A]\nThe API shall always log the request.\n");
    assert!(text.contains("Act(API|log request)") && text.contains("always: completes at every moment after the activation"), "{text}");
    assert!(rules("[A]\nThe API shall always log the request.\n").contains("timing-always"));
}

#[test]
fn a_count_in_a_row_is_read_as_a_run_of_completions() {
    let twice = "[A]\nWhen the timer expires, the API shall retry the request twice in a row.\n";
    let report = check(twice);
    assert!(report_codes(&report).is_empty() && report["opaque"].as_array().unwrap().is_empty(), "{report}");
    let text = model(twice);
    assert!(text.contains("Act(API|retry request)") && !text.contains("request in"), "{text}");
    assert!(text.contains("in a row: the longest run of completions at moments that follow each other = 2"), "{text}");
    assert!(rules(twice).contains("occurrences-in-a-row"));
    // The run is in the unrolled formula: two completions at moments that follow each other.
    let unrolled = package(twice).inspect(&["model", "--unrolled"]).stdout;
    assert!(unrolled.contains("API|retry request@1") && unrolled.contains("API|retry request@2"), "{unrolled}");
    assert_ne!(unrolled, package("[A]\nWhen the timer expires, the API shall retry the request twice.\n").inspect(&["model", "--unrolled"]).stdout);
}

#[test]
fn two_completions_cannot_each_come_before_the_other_in_the_rest_of_the_trace_either() {
    // Each of two actions completes before the other after one expiry of
    // the timer: no order of the two completions keeps both statements. The
    // rest of the trace stands for the later moments, and the first
    // completion of each action there has a time: the order is an order of
    // these times. This test asserted that the cycle is not refuted, because
    // the rest ordered nothing; a model that places both completions in the
    // rest is a model of no trace.
    let cycle = "[A]\nWhen the timer expires, the API shall log the request before the API sends the report.\n\n[B]\nWhen the timer expires, the API shall send the report before the API logs the request.\n";
    let report = check(cycle);
    assert_eq!(analysis_codes(&report), ["contradiction"], "{report}");
    // A behaviour in which the timer never expires keeps both, and the
    // environment decides whether it expires: a system that accepts every
    // input cannot avoid the expiry, so the package is inconsistent.
    assert_eq!(verdicts(&report).get("consistency").map(String::as_str), Some("refuted"), "{report}");
    assert!(report["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "contradiction" && d["message"].as_str().unwrap().contains("Event(timer expire@")), "{report}");
    // `after` asks for an occurrence of the same activation before each
    // completion. Until work item W06 an occurrence at the moment of the
    // activation counted as one, so a report and a log at the moment of the
    // expiry stood before a later log and a later report, and this test
    // asserted that the cycle is kept. What happens at the moment of the
    // trigger beside the trigger answers nothing that the trigger opens
    // (spec/semantics/core.md, section 4): an occurrence belongs to an
    // activation when it opens it or lies after it, and then the two
    // completions cannot each come after the other (acceptance case A04b).
    let after = "[A]\nWhen the timer expires, the API shall log the request after the API sends the report.\n\n[B]\nWhen the timer expires, the API shall send the report after the API logs the request.\n";
    assert_eq!(codes_of_the_analysis(after), ["contradiction"], "{:?}", codes_of_the_analysis(after));
    // The event that opens the activation is an occurrence of it: a
    // response after the trigger itself is an ordinary response.
    assert!(codes_of_the_analysis("[A]\nWhen the API sends the report, the API shall log the request after the API sends the report.\n").is_empty());
    // One `after` alone is kept.
    assert!(codes_of_the_analysis("[A]\nWhen the timer expires, the API shall log the request after the API sends the report.\n\n[B]\nWhen the timer expires, the API shall send the report.\n").is_empty());
    // One order alone is kept, in the rest as well.
    assert!(codes_of_the_analysis("[A]\nWhen the timer expires, the API shall log the request before the API sends the report.\n\n[B]\nWhen the timer expires, the API shall send the report.\n").is_empty());
    // Opposite orders after different triggers are no cycle where the
    // triggers come at different moments. The environment decides both and
    // nothing keeps them apart: where they come at one moment, an
    // occurrence after it belongs to both activations, and the orders form
    // a cycle (acceptance case A05). This asserted no finding while
    // consistency let the system avoid that situation.
    let apart = "primitive bell\n\n[A]\nWhen the timer expires, the API shall log the request before the API sends the report.\n\n[B]\nWhen the bell rings, the API shall send the report before the API logs the request.\n";
    let report = check(apart);
    assert_eq!(analysis_codes(&report), ["contradiction"], "{report}");
    let found = report["diagnostics"].as_array().unwrap().iter().find(|d| d["code"] == "contradiction").unwrap()["message"].as_str().unwrap().to_string();
    let moment = |event: &str| found.split(&format!("Event({event}@")).nth(1).and_then(|rest| rest.split(')').next()).map(str::to_string);
    assert!(moment("bell ring").is_some() && moment("bell ring") == moment("timer expire"), "{found}");
    // An order without an activation says nothing of the first moment: that
    // the environment may act there first is a question of realizability.
    let report = check("primitive room, user, message\n\n[C1]\nThe API shall lock the room before the user sends a message.\n\n[C0]\nWhen the user sends a message, the API shall store the message.\n");
    assert_eq!(analysis_codes(&report), ["unrealizable"], "{report}");
    assert_eq!(verdicts(&report).get("consistency").map(String::as_str), Some("proved"), "{report}");
}

#[test]
fn a_bare_noun_after_before_is_an_occurrence_alone_and_in_the_package() {
    let alone = "[B]\nWhen the timer expires, the API shall log the request before the retry.\n";
    let within = format!("{RETRY}{alone}");
    let line = |text: &str| model(text).lines().find(|l| l.contains("action API|log request")).unwrap().to_string();
    // The reading is the same; only the package can say whether the occurrence has an event.
    assert_eq!(line(alone), line(&within));
    assert!(line(alone).contains("before event retry: the response completes before the occurrence"), "{}", line(alone));
    assert!(!model(alone).contains("log request before retry"), "{}", model(alone));
    assert_eq!(codes(alone), ["UNRESOLVED_TEMPORAL_SCOPE"]);
    assert!(codes(&within).is_empty(), "{:?}", codes(&within));
}

#[test]
fn a_prohibition_with_an_order_phrase_forbids_the_named_moments_only() {
    // Forbidden until the first retry: a trace with a retry and a later report satisfies both.
    let until = format!("{RETRY}[P]\nThe API shall not send the report before the first retry.\n\n[Q]\nThe API shall send the report.\n");
    assert!(codes(&until).is_empty(), "{:?}", codes(&until));
    assert!(model(&until).contains("before event first retry: the action is forbidden until the occurrence"), "{}", model(&until));
    // Where no retry ever completes, the report is forbidden at every moment and in the rest.
    let never = "[N]\nThe API shall not retry the request.\n\n[P]\nThe API shall not send the report before the first retry.\n\n[Q]\nThe API shall send the report.\n";
    assert_eq!(codes(never), ["contradiction"]);
    // Forbidden from the first retry on: a report that a retry requires comes too late.
    let from = "[R]\nWhen the timer expires, the API shall immediately retry the request.\n\n[P]\nThe API shall not send the report after the first retry.\n\n[Q]\nWhen the API retries the request, the API shall send the report.\n";
    assert_eq!(codes(from), ["contradiction"]);
    // Before the retry the report is free.
    let free = "[R]\nWhen the timer expires, the API shall retry the request.\n\n[P]\nThe API shall not send the report after the first retry.\n\n[Q]\nThe API shall send the report.\n";
    assert!(codes(free).is_empty(), "{:?}", codes(free));
    // A clause states the occurrence as well as a noun does.
    let clause = "[N]\nThe API shall not retry the request.\n\n[P]\nThe API shall not send the report before the API retries the request.\n\n[Q]\nThe API shall send the report.\n";
    assert_eq!(codes(clause), ["contradiction"]);
}

#[test]
fn a_prohibition_with_immediately_or_a_run_forbids_the_named_moments_only() {
    let not_at_once = "[P]\nWhen the timer expires, the API shall not immediately respond.\n\n";
    let later = format!("{not_at_once}[Q]\nWhen the timer expires, the API shall respond.\n");
    assert!(codes(&later).is_empty(), "{:?}", codes(&later));
    let at_once = format!("{not_at_once}[Q]\nWhen the timer expires, the API shall immediately respond.\n");
    assert_eq!(codes(&at_once), ["contradiction"]);
    let no_run = "[P]\nThe API shall not send the report twice in a row.\n\n";
    let twice = format!("{no_run}[Q]\nThe API shall send the report twice.\n");
    assert!(codes(&twice).is_empty(), "{:?}", codes(&twice));
    let every = format!("{no_run}[Q]\nThe API shall always send the report.\n");
    assert_eq!(codes(&every), ["contradiction"]);
}

#[test]
fn after_once_upon_and_on_open_the_frame_of_when() {
    // Written before the run from the rule: `After`, `Once`, `Upon` and
    // `On` open the frame of `When`, so the statement applies at each
    // occurrence of the event. A prohibition of the same action under the
    // same event is then a contradiction, and a prohibition of another
    // action is none. Until now only a parse test and a form-name test
    // covered these openers.
    const HEAD: &str = "primitive API\nprimitive job\nprimitive startup\nprimitive receipt\nprimitive token\n\n";
    let verify = |text: &str| Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", &format!("{HEAD}{text}"))]).verify(&["--json"]).json();
    for (opener, when) in [
        ("After the job ends,", "When the job ends,"),
        ("Once the job ends,", "When the job ends,"),
        ("On startup,", "When startup occurs,"),
        ("Upon receipt of a token,", "When receipt of a token occurs,"),
    ] {
        let against = verify(&format!("[A]\n{opener} the API shall stop.\n\n[B]\n{when} the API shall not stop.\n"));
        assert_eq!(report_codes(&against), ["contradiction"], "{opener}{against}");
        let beside = verify(&format!("[A]\n{opener} the API shall stop.\n\n[B]\n{when} the API shall not start.\n"));
        assert_verified(&beside);
    }
}

#[test]
fn an_opener_of_time_takes_one_event_as_when_does() {
    // Old behaviour: the one-event rule covered `When` and `If` only, and
    // `After the job ends and the timer expires,` was accepted and read as
    // two events of one moment. The conjunction of two occurrences has no
    // single reading under any opener, so the rule now covers each of them.
    const HEAD: &str = "primitive API\nprimitive job\nprimitive timer\n\n";
    let verify = |text: &str| Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", &format!("{HEAD}{text}"))]).verify(&["--json"]);
    for opener in ["After", "Once", "When", "If"] {
        let run = verify(&format!("[A]\n{opener} the job ends and the timer expires, the API shall stop.\n"));
        assert_eq!(run.code, 1, "{opener}");
        let report = run.json();
        assert!(report["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "parse-sentence" && d["message"].as_str().unwrap().contains("takes one event")), "{opener}{report}");
    }
    // One event with a state, and alternatives, stay accepted.
    for text in ["[A]\nAfter the job ends and the timer is active, the API shall stop.\n", "[A]\nAfter the job ends or the timer expires, the API shall stop.\n"] {
        let report = verify(text).json();
        assert!(!report_codes(&report).contains(&"parse-sentence".to_string()), "{text}{report}");
    }
}
