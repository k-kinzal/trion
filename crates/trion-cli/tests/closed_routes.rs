//! Routes by which a package was verified with a part of its meaning left
//! out (`spec/semantics/README.md`, "Not stopped yet" ).
//! Each test states what the sentence means and gives two packages that the
//! meaning tells apart. The expectations were written from the meaning
//! before the first run.

mod common;
use common::*;
use serde_json::Value;

const HEAD: &str = "primitive API\nprimitive door\nprimitive alarm\n\n";

fn verify(text: &str) -> Value {
    Fixture::new(&[("trion.toml", MANIFEST), ("a.trion", &format!("{HEAD}{text}"))]).verify(&["--json"]).json()
}

fn contradicts(report: &Value) -> bool {
    report["diagnostics"].as_array().unwrap().iter().any(|d| d["code"] == "contradiction")
}

#[test]
fn an_enumeration_says_that_its_subject_has_one_of_the_values() {
    // `The door is open or closed.` says that the door is open or that it is
    // closed, at each moment. Old behaviour: the statement closed the
    // domain (no other value, no two values at once) and did not say that
    // the door has a value, so forbidding each value was consistent.
    const DOOR: &str = "[D]\nThe door is open or closed.\n\n";
    let both = verify(&format!("{DOOR}[A]\nWhile the alarm is active, the door shall not be open.\n\n[B]\nWhile the alarm is active, the door shall not be closed.\n"));
    assert!(contradicts(&both), "{both}");
    let one = verify(&format!("{DOOR}[A]\nWhile the alarm is active, the door shall not be open.\n"));
    assert_verified(&one);
    // Each spelling of the list says the same.
    for door in ["The door is one of open and closed.", "The door is open, closed or ajar."] {
        let each = verify(&format!("[D]\n{door}\n\n[A]\nWhile the alarm is active, the door shall not be open.\n\n[B]\nWhile the alarm is active, the door shall not be closed.\n\n[C]\nWhile the alarm is active, the door shall not be ajar.\n"));
        assert!(contradicts(&each), "{door}{each}");
    }
}

#[test]
fn a_necessary_condition_forbids_the_action_where_it_fails() {
    // `shall stop only when the door is open` forbids stopping while the
    // door is not open. Old behaviour: the contract was `(Act ∧ ¬Forbid ∧
    // ¬Discouraged) → open`, which a completion that is marked forbidden
    // satisfied without the condition: the first package was consistent.
    const ONLY: &str = "[A]\nThe API shall stop only when the door is open.\n\n";
    let done = verify(&format!("{ONLY}[B]\nThe API stops.\n\n[C]\nThe door is never open.\n"));
    assert!(contradicts(&done), "{done}");
    let required = verify(&format!("[D]\nThe door is open or closed.\n\n{ONLY}[B]\nWhile the door is closed, the API shall stop.\n"));
    assert!(contradicts(&required), "{required}");
    // Inside the condition the action stays free, and it is not required.
    assert_verified(&verify(&format!("{ONLY}[B]\nWhile the door is open, the API shall stop.\n")));
    assert_verified(&verify(&format!("{ONLY}[B]\nWhile the door is open, the API shall start.\n")));
    // `exactly when` is the necessary condition and the sufficient one.
    let exact = verify("[A]\nThe API shall stop exactly when the door is open.\n\n[B]\nThe API stops.\n\n[C]\nThe door is never open.\n");
    assert!(contradicts(&exact), "{exact}");
    let unmet = verify("[A]\nThe API shall stop exactly when the door is open.\n\n[B]\nWhile the door is open, the API shall not stop.\n");
    assert!(contradicts(&unmet), "{unmet}");
}

#[test]
fn a_prohibition_confined_by_a_necessary_condition_is_not_read() {
    // No rule says what `shall not stop only when the door is open` leaves
    // of the action where the door is not open. It was read as `Forbid →
    // open`, which not forbidding satisfies.
    for text in ["[A]\nThe API shall not stop only when the door is open.\n", "[A]\nThe API shall not stop exactly when the door is open.\n"] {
        let report = verify(text);
        let named = report["opaque"].as_array().unwrap().iter().any(|d| d["code"] == "UNSUPPORTED_SEMANTICS" && d["message"].as_str().unwrap().contains("(`condition-only-if-denied`)"));
        assert!(named, "{text}{report}");
        assert!(unverified(&report).contains(&"UNSUPPORTED_SEMANTICS".to_string()), "{report}");
    }
    assert_verified(&verify("[A]\nWhile the door is open, the API shall not stop.\n\n[B]\nWhile the door is open, the API shall start.\n"));
}
