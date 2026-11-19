#[path = "../common/analysis.rs"]
mod common;

use common::{worker, SETTINGS};
use trion_boolean::{Constructor, Contract, Preparation, QueryKind, EXACT};
use trion_analysis::{analyze, Conclusion, Execution};
use trion_cnl::{formalize, Grammar};

const RESTRICTED: Contract = Contract {
    id: "conjunctive-test/1",
    constructors: &[Constructor::Atom, Constructor::Not, Constructor::And],
    queries: &[QueryKind::Satisfiable, QueryKind::Entails],
    ..EXACT
};

#[test]
fn changing_grammar_and_backend_does_not_change_core() {
    let v1 = formalize(
        "proposition P. proposition Q. assume P implies Q. assume P. entails Q.",
        Grammar::V1,
    )
    .unwrap();
    let v2 = formalize(
        "proposition P. proposition Q. assume if P then Q. assume P. entails Q.",
        Grammar::V2,
    )
    .unwrap();
    assert_eq!(v1.problem(), v2.problem());
    let verified = analyze(v1.problem(), &EXACT, SETTINGS, worker);
    for artifact in [v1, v2] {
        let snapshot = serde_json::to_vec(&artifact).unwrap();
        let rejected = analyze(artifact.problem(), &RESTRICTED, SETTINGS, |_| {
            panic!("backend that lacks Or must not run");
        });
        assert!(
            matches!(rejected.translation(), Preparation::Unsupported(reason) if reason.contains("Or"))
        );
        assert_eq!(rejected.outcome().execution(), Execution::NotRun);
        assert_eq!(rejected.outcome().conclusion(), Conclusion::None);
        assert_eq!(rejected.problem(), verified.problem());
        assert_eq!(serde_json::to_vec(&artifact).unwrap(), snapshot);
    }
    let supported = formalize(
        "proposition P. assume P and not P. satisfiable.",
        Grammar::V1,
    )
    .unwrap();
    assert!(matches!(
        RESTRICTED.prepare(supported.problem(), SETTINGS.backend),
        Preparation::Applicable(_)
    ));
    let query_only = formalize("proposition P. entails P or P.", Grammar::V1).unwrap();
    assert!(matches!(
        RESTRICTED.prepare(query_only.problem(), SETTINGS.backend),
        Preparation::Unsupported(_)
    ));

    let incompatible = Contract {
        semantics: "classical-propositional/0",
        ..EXACT
    };
    assert!(matches!(
        incompatible.prepare(supported.problem(), SETTINGS.backend),
        Preparation::PreconditionFailed(_)
    ));
}
