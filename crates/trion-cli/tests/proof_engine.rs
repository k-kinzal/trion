//! The certificates of the trion package itself: every proof obligation of
//! the package is proved as `trioc` proves it, and the checker of the tests
//! accepts the certificate of every answer that a verdict rests on. This
//! shows nothing about what the package says; it shows that no verdict
//! about it rests on the solver alone.

use trion_checker::certificate as checker;

use std::path::Path;
use trion_verification::{analyze, proof_obligations, Bounds, ObligationVerdict, Options};

#[test]
fn every_obligation_of_the_trion_package_is_proved_with_certified_answers() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let project = trion_cli::project::load(&root).expect("the trion package loads");
    let options = Options { bounds: Bounds::default(), ..Options::default() };
    let analysis = analyze(&project.set, &options);
    let stated = proof_obligations(&project.set, &analysis, options.bounds.trace_length);
    assert!(stated.obligations.iter().any(|o| o.property == "consistency") && stated.obligations.iter().any(|o| o.property == "compatibility"));
    let inst = stated.instance(None);
    let mut answers = 0;
    for obligation in &stated.obligations {
        let decision = stated.decide(&inst, obligation);
        assert_eq!(decision.verdict, ObligationVerdict::Proved, "{}: {:?}", obligation.name, decision.reason);
        for asked in &decision.asked {
            if let Err(problem) = checker::check(&asked.formulas, &asked.answer) {
                panic!("the certificate of `{}` of {} is rejected: {problem}", asked.name, obligation.name);
            }
            answers += 1;
        }
    }
    assert!(answers >= stated.obligations.len(), "{answers}");
}
