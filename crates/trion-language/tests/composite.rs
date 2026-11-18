//! Composite vocabulary: a sentence abbreviates the simple sentences that
//! it expands to, or it is refused where distribution would change it.

use trion_language::syntax::ast::{Core, NpGroup, VpGroup};
use trion_language::syntax::composite::{expand, is_simple};
use trion_language::syntax::parse;

/// The texts of the sentences that a sentence expands to, or why it has none.
fn expanded(text: &str) -> Result<Vec<String>, String> {
    let sentence = parse(text).expect("the text is one sentence").sentences.remove(0);
    expand(&sentence).map(|parts| parts.into_iter().map(|part| part.source).collect()).map_err(|refused| refused.reason)
}

fn texts(parts: &[&str]) -> Result<Vec<String>, String> {
    Ok(parts.iter().map(|part| part.to_string()).collect())
}

#[test]
fn a_simple_sentence_expands_to_itself() {
    for text in ["The API shall store the message.", "When the door closes, the API shall stop.", "The API shall either accept the request or reject the request.", "When the door closes and the key is present, the API shall stop.", "A gate means a door that is open."] {
        assert_eq!(expanded(text), texts(&[text]), "{text}");
        assert!(is_simple(&parse(text).unwrap().sentences[0]), "{text}");
    }
}

#[test]
fn verb_phrases_joined_by_and_are_one_sentence_each() {
    assert_eq!(expanded("The API shall store the message and log the message."), texts(&["The API shall store the message.", "The API shall log the message."]));
    assert_eq!(expanded("The API shall notify the customer and shall not create an order."), texts(&["The API shall notify the customer.", "The API shall not create an order."]));
    assert_eq!(expanded("The API shall store the message and log the message and notify the client."), texts(&["The API shall store the message.", "The API shall log the message.", "The API shall notify the client."]));
}

#[test]
fn each_part_keeps_the_conditions_of_the_sentence() {
    assert_eq!(expanded("When the door closes, the API shall store the message and log the message, unless the key is present."), texts(&["When the door closes, the API shall store the message, unless the key is present.", "When the door closes, the API shall log the message, unless the key is present."]));
}

#[test]
fn subjects_objects_and_role_phrases_joined_by_and_are_one_sentence_each() {
    assert_eq!(expanded("The API and the gateway shall stop."), texts(&["The API shall stop.", "The gateway shall stop."]));
    assert_eq!(expanded("The API shall store the message and the call."), texts(&["The API shall store the message.", "The API shall store the call."]));
    assert_eq!(expanded("The API shall send the message to the client and the auditor."), texts(&["The API shall send the message to the client.", "The API shall send the message to the auditor."]));
    // Every joint of the sentence is distributed.
    assert_eq!(expanded("The API and the gateway shall store the message and log the call."), texts(&["The API shall store the message.", "The gateway shall store the message.", "The API shall log the call.", "The gateway shall log the call."]));
}

#[test]
fn whole_clauses_joined_by_and_are_one_sentence_each() {
    assert_eq!(expanded("The API shall stop, and the gateway shall log the call."), texts(&["The API shall stop.", "The gateway shall log the call."]));
}

#[test]
fn or_under_not_denies_each_and_or_without_not_is_one_requirement() {
    assert_eq!(expanded("The API shall not store or log the message."), texts(&["The API shall not store the message.", "The API shall not log the message."]));
    assert_eq!(expanded("The API shall store the message or log the message."), texts(&["The API shall store the message or log the message."]));
    assert_eq!(expanded("The API shall store the message or the call."), texts(&["The API shall store the message or the call."]));
}

#[test]
fn a_counted_subject_is_not_repeated() {
    for text in ["Some user shall log in and log out.", "No user shall store the message and the call."] {
        let refused = expanded(text).unwrap_err();
        assert!(refused.contains("is counted"), "{text}: {refused}");
    }
    // Each subject of a list is counted in its own sentence.
    assert_eq!(expanded("Some user and each admin shall stop."), texts(&["Some user shall stop.", "Each admin shall stop."]));
}

#[test]
fn a_clause_about_the_whole_claim_is_not_distributed() {
    for (text, clause) in [("The API shall store the message and log the message only when the door is open.", "only when"), ("The API shall store the message and log the message exactly when the door is open.", "exactly when")] {
        let refused = expanded(text).unwrap_err();
        assert!(refused.contains(clause) && refused.contains("as a whole"), "{text}: {refused}");
    }
}

#[test]
fn a_measure_after_the_last_verb_phrase_is_not_guessed() {
    let refused = expanded("The API shall validate the request and send the response within 5 seconds.").unwrap_err();
    assert!(refused.contains("within 5 seconds") && refused.contains("written once"), "{refused}");
    // Stated in each verb phrase, it bounds each.
    assert_eq!(expanded("The API shall validate the request within 5 seconds and send the response within 5 seconds."), texts(&["The API shall validate the request within 5 seconds.", "The API shall send the response within 5 seconds."]));
}

#[test]
fn a_part_that_names_what_another_part_introduces_is_not_a_sentence_of_its_own() {
    for text in ["The API shall create a report and send the report.", "The system shall notify a member of the room and notify a second member of the room.", "The API shall issue two tokens and revoke the tokens."] {
        let refused = expanded(text).unwrap_err();
        assert!(refused.contains("another part names it"), "{text}: {refused}");
    }
    // What the conditions introduce stands in each part.
    assert_eq!(expanded("When a user posts a message, the system shall store the message and notify the user."), texts(&["When a user posts a message, the system shall store the message.", "When a user posts a message, the system shall notify the user."]));
    // Parts that introduce things of one kind each speak of their own.
    assert_eq!(expanded("The API shall create a report and send a report."), texts(&["The API shall create a report.", "The API shall send a report."]));
    // Parts that name the same thing speak of the same thing.
    assert_eq!(expanded("The API shall store the message and log the message."), texts(&["The API shall store the message.", "The API shall log the message."]));
}

#[test]
fn sentences_without_a_modal_verb_abbreviate_in_the_same_way() {
    assert_eq!(expanded("Each room has a name and an owner."), texts(&["Each room has a name.", "Each room has an owner."]));
    assert_eq!(expanded("The door and the window are open."), texts(&["The door is open.", "The window is open."]));
    assert_eq!(expanded("The doors and the windows are open."), texts(&["The doors are open.", "The windows are open."]));
    // A list of values is one description, and a definition is one sentence.
    assert_eq!(expanded("The colour is red, green, or blue."), texts(&["The colour is red, green, or blue."]));
    assert_eq!(expanded("An author means a person or a program that writes a specification."), texts(&["An author means a person or a program that writes a specification."]));
}

#[test]
fn and_under_not_is_not_guessed() {
    // Denying two things together is not denying each: the sentence is refused.
    for text in ["The API shall not store the message and the call.", "The API shall not send the report to the client and the auditor."] {
        let refused = expanded(text).unwrap_err();
        assert!(refused.contains("each of them or all of them together"), "{text}: {refused}");
    }
    // Between verb phrases the sentence is refused where it is read: only
    // there is it seen whether the modal verb is written before each phrase.
    for text in ["The API shall not store the message and log the call.", "When the door opens and the key is present, the API shall not store the message and log the call.", "The API shall not store the message and shall not log the call and notify the client."] {
        let refused = parse(text).unwrap_err().to_string();
        assert!(refused.contains("each of them or all of them together"), "{text}: {refused}");
    }
    // `or` joins the phrases that are each denied, whatever else `and` joins.
    assert_eq!(expanded("When the door opens and the key is present, the API shall not store or log the message."), texts(&["When the door opens and the key is present, the API shall not store the message.", "When the door opens and the key is present, the API shall not log the message."]));
    // `or` under `not` denies each, and so does a modal verb before each phrase.
    assert_eq!(expanded("The API shall not store the message or the call."), texts(&["The API shall not store the message.", "The API shall not store the call."]));
    assert_eq!(expanded("The API shall not store the message and shall not log the call."), texts(&["The API shall not store the message.", "The API shall not log the call."]));
    assert_eq!(expanded("The API shall notify the customer and shall not create an order."), texts(&["The API shall notify the customer.", "The API shall not create an order."]));
    // Each subject of a list is denied the action: `not` stands in the verb phrase.
    assert_eq!(expanded("The API and the gateway shall not stop."), texts(&["The API shall not stop.", "The gateway shall not stop."]));
}

#[test]
fn a_sentence_with_composite_vocabulary_is_not_simple() {
    for text in ["The API shall store the message and log the message.", "The API and the gateway shall stop.", "Each room has a name and an owner.", "The door and the window are open.", "There is a gateway and a proxy."] {
        assert!(!is_simple(&parse(text).unwrap().sentences[0]), "{text}");
    }
}

#[test]
fn a_role_that_is_no_measure_belongs_to_its_verb_phrase() {
    // A place, a recipient or a means after the last verb phrase is a part
    // of that phrase: only a measure is refused there.
    assert_eq!(expanded("The API shall stop the pump and send the report to the client."), texts(&["The API shall stop the pump.", "The API shall send the report to the client."]));
    assert_eq!(expanded("The API shall store the message and log the call in the journal."), texts(&["The API shall store the message.", "The API shall log the call in the journal."]));
}

#[test]
fn verb_phrases_of_a_relation_are_one_sentence_each() {
    assert_eq!(expanded("Each room has a name and contains a door."), texts(&["Each room has a name.", "Each room contains a door."]));
    // A relation denies nothing: one that is made to deny a verb phrase is refused.
    let mut sentence = parse("Each room has a name and contains a door.").unwrap().sentences.remove(0);
    let Core::Relation { vp: VpGroup::All { negated, .. }, .. } = &mut sentence.core else { panic!("{:?}", sentence.core) };
    negated[1] = true;
    assert!(expand(&sentence).unwrap_err().reason.contains("is no relation"));
}

#[test]
fn what_a_part_names_is_found_in_a_role_as_in_an_object() {
    // The thing that the first part introduces is named in a role of the second.
    let refused = expanded("The API shall create a report and send the summary to the report.").unwrap_err();
    assert!(refused.contains("another part names it") && refused.contains("`report`"), "{refused}");
    // And among the objects of one verb.
    let refused = expanded("The API shall issue a token and revoke the key and the token.").unwrap_err();
    assert!(refused.contains("another part names it") && refused.contains("`token`"), "{refused}");
}

#[test]
fn a_part_whose_text_is_not_read_as_the_part_is_refused() {
    // The text of each part is read again, and it has to be read as the
    // part. A subject that is made a word of the language is not: `The
    // shall shall stop.` is no sentence.
    let mut sentence = parse("The API and the gateway shall stop.").unwrap().sentences.remove(0);
    let Core::Deontic { subject: NpGroup::Coordinated { items, .. }, .. } = &mut sentence.core else { panic!("{:?}", sentence.core) };
    items[1].head = "shall".to_string();
    let refused = expand(&sentence).unwrap_err().reason;
    assert!(refused.contains("is not read as the requirement that it abbreviates"), "{refused}");
}
