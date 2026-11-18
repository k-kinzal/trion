//! Vocabulary and glossary rules of the language draft.

mod common;
use common::*;
use trion_language::{glossary, VocabularyMode};
use trion_verification::{Options};

#[test]
fn a_derived_term_keeps_its_interpretation_premises_rule_and_references() {
    let analysis = run("A room means a space.\n[OPEN] The API shall open the room door.\n[LOCK] The room door is locked.\n");
    let door = analysis.vocabulary["room door"].derivation.as_ref().expect("a derivation");
    assert_eq!(door.interpretation, ["attribute", "object"]);
    assert_eq!(door.rules, ["the subject of a description is an attribute", "the object or role of an action is an object"]);
    let premises: Vec<&str> = door.premises.iter().map(|p| p.id.as_str()).collect();
    assert_eq!(premises, ["LOCK", "OPEN"]);
    assert_eq!(door.referenced, ["room @ main.trion:2"]);
    // A defined term is not derived.
    assert!(analysis.vocabulary["room"].derivation.is_none());
    // The reader sees the derivation in the glossary.
    let entries = glossary(&analysis.vocabulary);
    let entry = entries.iter().find(|e| e.term == "room door").unwrap();
    assert_eq!(entry.status, "derived");
    let shown = entry.derivation.as_ref().unwrap();
    assert_eq!(shown.premises, ["main.trion:4", "main.trion:3"]);
    assert_eq!(shown.referenced, ["room @ main.trion:2"]);
}

#[test]
fn an_uninterpreted_predicate_has_a_signature_an_identity_and_no_axioms() {
    let src = "predicate overlap(interval, interval)\nThe first interval shall overlap the second interval.\n";
    let analysis = run(src);
    assert!(analysis.diagnostics.is_empty(), "{:?}", analysis.diagnostics);
    let entry = &analysis.vocabulary["overlap"];
    assert_eq!(entry.signature.as_deref(), Some(&["interval".to_string(), "interval".to_string()][..]));
    assert_eq!(entry.identity.as_deref(), Some("overlap/2"));
    assert_eq!(entry.declared_kind.as_deref(), Some("predicate"));
    // The declaration adds no constraint: the model is the model of the sentence alone.
    let without = run("// no declaration\nThe first interval shall overlap the second interval.\n");
    // The declaration makes the verb an operation with an input domain, which is no axiom.
    assert_eq!(format!("{:?}", analysis.model.constraints), format!("{:?}", without.model.constraints));
    assert_eq!(analysis.model.background, without.model.background);
    // A second declaration with another signature is not the same predicate.
    let clash = run_codes("predicate overlap(interval, interval)\npredicate overlap(interval)\nThe API shall stop.\n");
    assert_eq!(clash, ["vocabulary-redeclared"]);
    let entries = glossary(&analysis.vocabulary);
    assert_eq!(entries.iter().find(|e| e.term == "overlap").unwrap().status, "primitive");
}

#[test]
fn an_unresolved_term_is_reported_with_every_affected_statement() {
    let src = "term API: entity\n[A] The API shall return foo.\n[B] The API shall log foo.\n[C] The API shall stop.\n";
    let analysis = proved(&set_of(&[("main", true, src)], VocabularyMode::Declared), &Options::default());
    let unresolved: Vec<_> = analysis.diagnostics.iter().filter(|d| d.code == "UNRESOLVED_TERM").collect();
    assert_eq!(unresolved.len(), 1, "{:?}", analysis.diagnostics);
    assert!(unresolved[0].message.contains("`foo`"), "{}", unresolved[0].message);
    let affected: Vec<&str> = unresolved[0].refs.iter().map(|r| r.id.as_str()).collect();
    assert_eq!(affected, ["A", "B"]);
}

#[test]
fn a_cyclic_definition_is_rejected() {
    let analysis = run("[ROOM] A room means a space.\n[SPACE] A space means a room.\n");
    let cyclic: Vec<_> = analysis.diagnostics.iter().filter(|d| d.code == "CYCLIC_DEFINITION").collect();
    assert_eq!(cyclic.len(), 1, "{:?}", analysis.diagnostics);
    let mut ids: Vec<&str> = cyclic[0].refs.iter().map(|r| r.id.as_str()).collect();
    ids.sort();
    assert_eq!(ids, ["ROOM", "SPACE"]);
    assert_eq!(run_codes("A room means a room.\n"), ["CYCLIC_DEFINITION"]);
    // A chain that ends is not a cycle.
    assert!(run_codes("A room means a space.\nA space means an area.\n").is_empty());
}

#[test]
fn the_glossary_lists_type_namespace_definition_domain_and_occurrences() {
    let analysis = run("[DEF] A room means a space.\n[A] The API shall open the room.\n[B] The API shall close the room.\n");
    let entries = glossary(&analysis.vocabulary);
    let room = entries.iter().find(|e| e.term == "room").unwrap();
    assert_eq!(room.status, "explicit");
    assert_eq!(room.namespace, "");
    assert_eq!(room.kinds, ["object"]);
    assert_eq!(room.definition.as_deref(), Some("A room means a space."));
    assert_eq!(room.occurrences_at, ["main.trion:2", "main.trion:3", "main.trion:4"]);
    let api = entries.iter().find(|e| e.term == "API").unwrap();
    assert_eq!(api.occurrences_at, ["main.trion:3", "main.trion:4"]);
    assert_eq!(api.derivation.as_ref().unwrap().interpretation, ["entity"]);
    // A term of another namespace names its referenced domain.
    let two = proved(&set_of(&[("main", true, "namespace main:\n    use main.base\n    The API shall open the gate.\nnamespace main.base:\n    A gate means a door.\n")], VocabularyMode::Inferred), &Options::default());
    let entries = glossary(&two.vocabulary);
    let gate = entries.iter().find(|e| e.term.ends_with("gate")).unwrap();
    assert_eq!(gate.referenced_domain.as_deref(), Some("base"));
    assert_eq!(gate.namespace, "base");
}

#[test]
fn the_glossary_points_at_source_declarations_and_adds_no_constraint() {
    let src = "term API: entity\n[DEF] A room means a space.\n[A] The API shall open the room.\n";
    let analysis = run(src);
    let before = format!("{:?}", analysis.model);
    let entries = glossary(&analysis.vocabulary);
    assert_eq!(entries.iter().find(|e| e.term == "API").unwrap().declared_at.as_deref(), Some("main.trion:2"));
    assert_eq!(entries.iter().find(|e| e.term == "room").unwrap().defined_at.as_deref(), Some("main.trion:3"));
    // Generating the glossary changes neither the model nor the diagnostics.
    let again = run(src);
    assert_eq!(format!("{:?}", again.model), before);
    assert!(again.diagnostics.is_empty());
}
