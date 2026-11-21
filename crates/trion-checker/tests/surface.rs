//! The text of a statement against its tree: the second reading of the
//! text agrees with the tree that the parser makes, refuses a tree that
//! brackets the words otherwise, and says where a text is outside its
//! grammar.

use std::collections::BTreeSet;
use trion_checker::surface::{check, Read};
use trion_language::parse_sentence;
use trion_language::syntax::ast::*;

fn nouns() -> BTreeSet<String> {
    ["user", "room", "message", "system", "member", "owner", "author", "administrator", "mode", "postings"].iter().map(|noun| noun.to_string()).collect()
}

#[test]
fn the_text_of_a_plain_statement_is_read_as_its_tree() {
    for text in [
        "While a room is open, when a member of the room posts a message to the room, the system shall store the message within 2 seconds, unless the mode of the room is maintenance.",
        "The system shall not notify the author of a message about the message before the system stores the message.",
        "While a user is not the owner of a room and the user is not an administrator, the user shall not archive the room.",
        "When a user posts a message to a room, the system shall store the message within 2 seconds for at least 99 percent of postings.",
        "Each room has exactly one owner.",
        "The owner of each room is a member of the room.",
        "A room is open or archived.",
        "An administrator may archive each room.",
        "When a user that is a member of a room posts a message to the room, the system shall store the message.",
        "The system shall store each message that a member of a room posts to the room.",
        "When a user posts a message to a room whose mode is maintenance, the system shall reject the message.",
        "When a user posts a message to a room, the system shall notify two members of the room.",
        "No user shall archive a room.",
    ] {
        let sentence = parse_sentence(text).unwrap_or_else(|error| panic!("{text}: {error:?}"));
        assert_eq!(check(text, &sentence, &nouns()), Read::Agrees, "{text}");
    }
}

/// The tree that an earlier parser made of a relative clause before the
/// verb of a condition: `that is a` as the clause, `member` as the verb and
/// `room posts a` as words of the name of the message. The words of the
/// text are all in it, in their order, and it brackets them otherwise.
#[test]
fn a_tree_that_brackets_the_words_otherwise_is_refused() {
    let text = "When a user that is a member of a room posts a message to the room, the system shall store the message.";
    let mut sentence = parse_sentence(text).unwrap();
    let trigger = sentence.frames.trigger.as_mut().unwrap();
    let clause = &mut trigger.clause.items[0];
    let NpGroup::Single(subject) = &mut clause.subject else { panic!("one subject") };
    let Some(relative) = subject.relative.as_mut() else { panic!("a relative clause") };
    relative.body = RelativeBody::Copular { copula: ClauseCopula::Is, predicate: Predicate::Words { words: vec!["a".to_string()], nominal: None }, agent: None, roles: Vec::new() };
    let named = |det: Det, modifiers: &[&str], head: &str| NpGroup::Single(Np { det: Some(det), modifiers: modifiers.iter().map(|m| m.to_string()).collect(), head: head.to_string(), of: None, relative: None, of_also: Vec::new(), of_conj: None });
    clause.body = ClauseBody::Verbal {
        verb: "member".to_string(),
        particle: None,
        manner: Vec::new(),
        object: None,
        roles: vec![RolePp::Other { preposition: "of".to_string(), np: named(Det::A, &["room", "posts", "a"], "message") }, RolePp::Recipient(named(Det::The, &[], "room"))],
        content: None,
        negation: None,
    };
    let Read::Differs { text: read, tree } = check(text, &sentence, &nouns()) else { panic!("the tree is not refused") };
    assert!(read.contains("that(is a member of a room)") && read.contains("posts <a message> to <the room>"), "{read}");
    assert!(tree.contains("that(is a)") && tree.contains("member of <a room posts a message>"), "{tree}");
    // A word that the tree leaves out, and a denial that it drops.
    let mut dropped = parse_sentence("The system shall not store a message.").unwrap();
    if let Core::Deontic { negated, .. } = &mut dropped.core {
        *negated = false;
    }
    assert!(matches!(check("The system shall not store a message.", &dropped, &nouns()), Read::Differs { .. }));
}

#[test]
fn a_text_outside_the_grammar_is_said_to_be_not_read() {
    // A value of two words in a relative clause has no end that the words tell.
    for text in ["When a user that is newly active posts a message, the system shall store the message.", "The system shall log out each user."] {
        let Ok(sentence) = parse_sentence(text) else { continue };
        assert!(matches!(check(text, &sentence, &nouns()), Read::NotRead(_)), "{text}");
    }
}
