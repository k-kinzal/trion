//! The account of a reading names a rule for each kind of node: where it
//! tells the kinds of a node apart, it lists every kind, so that a new kind
//! of node does not pass without a decision.

#[test]
fn the_account_of_a_reading_has_no_catch_all_over_node_kinds() {
    let source = std::fs::read_to_string(concat!(env!("CARGO_MANIFEST_DIR"), "/src/reading/rules.rs")).unwrap();
    for (number, line) in source.lines().enumerate() {
        let arm = line.trim_start();
        // `_ => false` closes a match over the words of the three timing adverbs, which are no nodes.
        let catch_all = arm.starts_with("_ =>") && !arm.starts_with("_ => false");
        assert!(!catch_all, "crates/trion-language/src/reading/rules.rs:{}: a catch-all arm names no rule for the node kinds it covers: {line}", number + 1);
    }
    // Each determiner, each role and each relative marker has its own arm.
    for kind in ["Det::The", "Det::Each", "Det::No", "Det::Some", "Det::AtLeast", "Det::Reference", "RolePp::Recipient", "RolePp::Means", "RolePp::Topic", "RolePp::Deadline", "RolePp::Duration", "RolePp::Rate", "RolePp::Before", "RolePp::After", "RolePp::Until", "RolePp::Source", "RolePp::Goal", "RolePp::Location", "RolePp::Other", "RolePp::Agent", "RelMarker::That", "RelMarker::Who", "RelMarker::Whose", "RelMarker::Where"] {
        assert!(source.contains(kind), "the account names no rule for {kind}");
    }
}
