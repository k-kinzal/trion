use trion_cnl::{formalize, formalize_version, Accepted, Grammar, Rejected, Root};
use trion_core::Expr;

const SECTION_13: &str =
    "proposition P.\nproposition Q.\nassume P implies Q.\nassume P.\nentails Q.\n";

#[test]
fn published_implication_expands_and_prints() {
    let accepted = formalize_version(SECTION_13, None).unwrap();
    assert_eq!(accepted.grammar(), Grammar::V1);
    let expected = Expr::Or(
        Box::new(Expr::Not(Box::new(Expr::Atom(0)))),
        Box::new(Expr::Atom(1)),
    );
    assert_eq!(
        accepted.problem().document().premises(),
        &[expected, Expr::Atom(0)]
    );
    assert_eq!(
        formalize(&accepted.canonical_cnl(), accepted.grammar())
            .unwrap()
            .problem(),
        accepted.problem()
    );
    let synthetic = accepted
        .mappings()
        .iter()
        .find(|mapping| mapping.root == Root::Premise(0) && mapping.children == [0])
        .unwrap();
    assert_eq!(
        &SECTION_13[synthetic.span.start..synthetic.span.end],
        "implies"
    );
    let bytes = serde_json::to_vec(&accepted).unwrap();
    assert_eq!(Accepted::from_json(&bytes).unwrap(), accepted);
}

#[test]
fn positions_and_failure_categories() {
    assert!(matches!(formalize("entails 12 + 3.", Grammar::V1),
        Err(Rejected::Unsupported(d)) if d.rule == "CNL-FEATURE" && d.span.end - d.span.start == 2));
    let prefix = "proposition P. proposition Q. proposition R. ";
    let failure = |suffix: &str| formalize(&format!("{prefix}{suffix}"), Grammar::V1).unwrap_err();
    assert!(
        matches!(failure("entails P and Q or R."), Rejected::Ambiguous(d) if d.rule == "CNL-AMBIGUOUS" && d.span.start == prefix.len() + "entails ".len())
    );
    assert!(
        matches!(failure("entails always Q."), Rejected::Unsupported(d) if d.rule == "CNL-FEATURE")
    );
    assert!(matches!(failure("entails T."), Rejected::Invalid(d) if d.rule == "CNL-UNDECLARED"));
    assert!(
        matches!(failure("proposition P. satisfiable."), Rejected::Invalid(d) if d.rule == "CNL-DUPLICATE")
    );
    assert!(matches!(failure("entails (P and Q."), Rejected::Invalid(d) if d.rule == "CNL-SYNTAX"));
    assert!(
        matches!(failure("entails Ｐ."), Rejected::Invalid(d) if d.span.end - d.span.start == 3)
    );
    assert!(
        matches!(failure("entails P and Q or U."), Rejected::Invalid(d) if d.rule == "CNL-UNDECLARED")
    );
    assert!(matches!(failure("entails P Q."), Rejected::Invalid(_)));
    assert!(matches!(
        failure("entails P. satisfiable."),
        Rejected::Invalid(_)
    ));
    assert!(matches!(
        formalize_version(SECTION_13, Some("latest")),
        Err(Rejected::Unsupported(_))
    ));
}

#[test]
fn grammar_versions_pin_the_extension_and_old_associations() {
    let extended = SECTION_13.replace("P implies Q", "if P then Q");
    let original = formalize(SECTION_13, Grammar::V1).unwrap();
    assert_eq!(
        original.problem(),
        formalize(SECTION_13, Grammar::V2).unwrap().problem()
    );
    assert!(matches!(
        formalize(&extended, Grammar::V1),
        Err(Rejected::Unsupported(_))
    ));
    assert!(matches!(
        formalize_version(&extended, None),
        Err(Rejected::Unsupported(_))
    ));
    let new = formalize(&extended, Grammar::V2).unwrap();
    assert_eq!(original.problem(), new.problem());
    let tampered = serde_json::to_string(&new)
        .unwrap()
        .replace("propositional-cnl/2", "propositional-cnl/1");
    assert!(Accepted::from_json(tampered.as_bytes()).is_err());
    assert!(matches!(
        formalize("entails true or false and false.", Grammar::V2),
        Err(Rejected::Ambiguous(_))
    ));
}

#[test]
fn exchange_depth_covers_the_printer_and_sugar() {
    let deepest = format!(
        "entails {}false.",
        "not ".repeat(trion_core::MAX_DEPTH - 1)
    );
    let input = formalize(&deepest, Grammar::V1).unwrap();
    assert_eq!(
        formalize(&input.canonical_cnl(), Grammar::V1)
            .unwrap()
            .problem(),
        input.problem()
    );
    let too_deep = format!("entails {}true.", "not ".repeat(trion_core::MAX_DEPTH));
    assert!(matches!(
        formalize(&too_deep, Grammar::V1),
        Err(Rejected::Unsupported(_))
    ));
    let sugar = format!(
        "entails {}false implies true.",
        "not ".repeat(trion_core::MAX_DEPTH - 2)
    );
    assert!(matches!(
        formalize(&sugar, Grammar::V1),
        Err(Rejected::Unsupported(_))
    ));
}

#[test]
fn invalid_utf8_reports_the_byte_range() {
    let result = trion_cnl::formalize_bytes(b"entails \xff.", None);
    assert!(
        matches!(result, Err(Rejected::Invalid(d)) if d.rule == "CNL-UTF8" && d.span.start == 8 && d.span.end == 9)
    );
}
