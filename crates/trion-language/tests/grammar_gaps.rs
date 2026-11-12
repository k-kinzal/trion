//! Sentence forms that authors of the trion specification wrote and that the
//! parser rejected or misread.

use trion_language::parse_sentence;
use trion_language::syntax::ast::{Conj, Core, Definiens, NpGroup, RelMarker, VpGroup};

fn core(text: &str) -> Core {
    parse_sentence(text).unwrap_or_else(|e| panic!("{text}: {e}")).core
}

#[test]
fn a_repeated_of_joins_the_owners_of_one_head() {
    let Core::Definition { definiens: Definiens::Np { np: NpGroup::Single(np), .. }, .. } = core("A figure means a drawing of a concept block or of a flow block.") else { panic!() };
    assert_eq!(np.head, "drawing");
    assert_eq!(np.of.as_ref().map(|of| of.head.as_str()), Some("block"));
    assert_eq!(np.of_also.len(), 1);
    assert_eq!(np.of_conj, Some(Conj::Or));
    assert_eq!(np.render(), "a drawing of a concept block or of a flow block");
    // Without the repeated `of` the conjunction joins two noun phrases, as before.
    let Core::Deontic { vp: VpGroup::Single(vp), .. } = core("The API shall keep the name of the user and the room.") else { panic!() };
    assert!(matches!(vp.object, Some(NpGroup::Coordinated { .. })));
}

#[test]
fn where_after_a_noun_names_a_place_by_what_holds_there() {
    let Core::Deontic { vp: VpGroup::Single(vp), .. } = core("The parser shall mark the line where the error occurs.") else { panic!() };
    let Some(NpGroup::Single(object)) = &vp.object else { panic!() };
    assert_eq!(object.relative.as_ref().map(|r| r.marker), Some(RelMarker::Where));
    assert!(parse_sentence("A choice means a point of a flow where one of several steps follows.").is_ok());
    // A condition does not trail the response, and `only where` stays the restriction of the sentence.
    assert!(parse_sentence("The API shall stop where the door opens.").unwrap_err().contains("mid-sentence"));
    let restricted = parse_sentence("Each variable shall be available only where the grammar permits a use of that variable.").unwrap();
    assert!(restricted.necessary.is_some());
}

#[test]
fn a_partitive_is_read_as_its_quantifier() {
    let Core::Deontic { vp: VpGroup::Single(vp), .. } = core("When two rules conflict, the checker shall report each of them.") else { panic!() };
    let Some(NpGroup::Single(object)) = &vp.object else { panic!() };
    assert_eq!(object.head, "rules");
    let Core::Deontic { vp: VpGroup::Single(vp), .. } = core("The checker shall apply a prohibition to each of those subjects.") else { panic!() };
    assert!(format!("{:?}", vp.roles).contains("det: Some(Each)"), "{:?}", vp.roles);
}

#[test]
fn groups_of_role_phrases_share_one_verb_and_its_object() {
    let all = |text: &str| match core(text) {
        Core::Deontic { vp: VpGroup::All { items, .. }, .. } => items,
        other => panic!("{text}: {other:?}"),
    };
    let three = all("The plugin shall navigate from a use declaration to the namespace, from a citation to the source or quote, and from a reference to the statement.");
    assert_eq!(three.len(), 3);
    assert!(three.iter().all(|vp| vp.verb == "navigate" && vp.roles.len() == 2), "{three:?}");
    // The inner `or` joins two nouns of one role phrase.
    assert!(format!("{:?}", three[1].roles[1]).contains("Coordinated"), "{:?}", three[1]);
    let two = all("The API shall send the report to the admin and to the owner.");
    assert!(two.iter().all(|vp| vp.verb == "send" && vp.object.is_some()), "{two:?}");
    // A preposition is never read as a verb.
    assert!(!format!("{:?}", core("The API shall move the file from the inbox to the archive.")).contains("verb: \"to\""));
    // After a possessive, a conjunction continues the noun phrase.
    assert!(matches!(core("Each citation shall point to its source or quote."), Core::Deontic { vp: VpGroup::Single(_), .. }));
}
