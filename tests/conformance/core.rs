use trion_core::{CoreDocument, Expr, Problem, Question};
use trion_reference::{check_witness, scan, Scan};

fn problem(names: &[&str], premises: Vec<Expr>, question: Question) -> Problem {
    Problem::new(
        CoreDocument::new(names.iter().map(|name| (*name).into()).collect(), premises).unwrap(),
        question,
    )
    .unwrap()
}

#[test]
fn empty_universe_is_a_single_valuation() {
    let empty = problem(&[], vec![], Question::Entails(Expr::False));
    assert!(check_witness(&empty, &[]));
    assert_eq!(scan(&empty, 0), Scan::Incomplete);
    assert_eq!(
        scan(&empty, 1),
        Scan::Complete {
            assignments: 1,
            has_model: true,
            has_candidate: true,
        }
    );
    let false_premise = problem(&[], vec![Expr::False], Question::Satisfiable);
    assert_eq!(
        scan(&false_premise, 1),
        Scan::Complete {
            assignments: 1,
            has_model: false,
            has_candidate: false,
        }
    );
}

#[test]
fn each_valuation_can_be_the_only_witness() {
    for bits in 0..8 {
        let valuation: Vec<bool> = (0..3).map(|i| bits & (1 << i) != 0).collect();
        let literals = valuation.iter().enumerate().map(|(i, value)| {
            let atom = Expr::Atom(i as u32);
            if *value {
                atom
            } else {
                Expr::Not(Box::new(atom))
            }
        });
        let subject = problem(&["P", "Q", "R"], literals.collect(), Question::Satisfiable);
        assert_eq!(scan(&subject, 7), Scan::Incomplete);
        assert_eq!(
            scan(&subject, 8),
            Scan::Complete {
                assignments: 8,
                has_model: true,
                has_candidate: true,
            }
        );
        assert!(check_witness(&subject, &valuation));
        assert!(!check_witness(&subject, &valuation[..2]));
    }
}

#[test]
fn canonical_round_trip_and_name_validation() {
    let doc = CoreDocument::new(vec!["P".into(), "p".into()], vec![Expr::Atom(1)]).unwrap();
    assert_eq!(
        doc.canonical_json(),
        r#"{"semantics":"classical-propositional","schema":"core-json","definitions":"empty","declarations":["P","p"],"premises":[{"atom":1}]}"#
    );
    let roundtrip: CoreDocument = serde_json::from_str(&doc.canonical_json()).unwrap();
    assert_eq!(roundtrip.id(), doc.id());
    assert_eq!(roundtrip, doc);
    for name in ["Ｐ", " a", "a.b", "a-b", "_a", "a b", ""] {
        assert!(
            CoreDocument::new(vec![name.into()], vec![]).is_err(),
            "{name:?}"
        );
    }
    assert!(CoreDocument::new(vec!["P".into(), "P".into()], vec![]).is_err());
    assert!(CoreDocument::new(vec![], vec![Expr::Atom(0)]).is_err());
}

#[test]
fn rejects_corrupt_forms_and_queries() {
    let subject = problem(&["P"], vec![], Question::Entails(Expr::Atom(0)));
    let json = serde_json::to_string(&subject).unwrap();
    assert_eq!(serde_json::from_str::<Problem>(&json).unwrap(), subject);
    for (original, broken) in [
        ("classical-propositional", "other-semantics"),
        ("empty", "other-definition-environment"),
        ("core-json", "other-schema"),
        (r#""atom":0"#, r#""atom":1"#),
        (r#""atom":0"#, r#""unknown":0"#),
        (r#""atom":0"#, r#""atom":0,"atom":0"#),
        (r#""premises":[]"#, r#""premises":[],"premises":[]"#),
        (r#""premises":[]"#, r#""premises":[],"extra":null"#),
        (r#""premises":[]"#, r#""premises":["true"]"#),
    ] {
        assert!(
            serde_json::from_str::<Problem>(&json.replace(original, broken)).is_err(),
            "{broken}"
        );
    }
}

#[test]
fn decoder_accepts_only_the_declared_wire_shapes() {
    for invalid in [
        r#"{"true":null}"#,
        r#"{"and":["true","false","true"]}"#,
        r#"{"not":false}"#,
        r#"{"and":{"left":"true","right":"true"}}"#,
        r#"{"not":"true","extra":null}"#,
    ] {
        assert!(serde_json::from_str::<Expr>(invalid).is_err(), "{invalid}");
    }
    assert!(serde_json::from_str::<Question>(r#"{"satisfiable":null}"#).is_err());
    let doc = problem(&["P"], vec![Expr::Atom(0)], Question::Satisfiable);
    let reordered = r#"{"definitions":"empty","schema":"core-json","declarations":["P"],"premises":[{"atom":0}],"semantics":"classical-propositional"}"#;
    assert_eq!(
        serde_json::from_str::<CoreDocument>(reordered)
            .unwrap()
            .id(),
        doc.document().id()
    );
}

#[test]
fn named_records_reject_positional_arrays() {
    assert!(
        serde_json::from_str::<CoreDocument>(r#"["classical-propositional","core-json","empty",[],[]]"#).is_err()
    );
    let valid = problem(&[], vec![], Question::Satisfiable);
    let document = valid.document().canonical_json();
    let id = valid.document().id();
    let array_query = format!(r#"{{"document":{document},"query":["{id}","satisfiable"]}}"#);
    let array_pair = format!(r#"[{document},{{"document":"{id}","question":"satisfiable"}}]"#);
    assert!(serde_json::from_str::<Problem>(&array_query).is_err());
    assert!(serde_json::from_str::<Problem>(&array_pair).is_err());
}
