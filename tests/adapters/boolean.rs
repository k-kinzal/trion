#[path = "../common/analysis.rs"]
mod common;

use common::{worker, SETTINGS};
use trion_analysis::{
    analyze, compare, ComparisonError, Conclusion, Evidence, Execution, Premises, Record,
};
use trion_boolean::{solve, Preparation, Reply, EXACT};
use trion_cnl::{formalize};
use trion_core::{CoreDocument, Expr, Problem, Question};
use trion_reference::{check_witness, scan, Scan};

#[test]
fn worked_examples_and_replay() {
    let declarations = "proposition P. proposition Q. ";
    for (text, conclusion, premises, evidence) in [
        (
            "assume P implies Q. assume P. entails Q.",
            Conclusion::Entails,
            Premises::Consistent,
            Evidence::Exhaustive,
        ),
        (
            "assume P implies Q. assume Q. entails P.",
            Conclusion::DoesNotEntail,
            Premises::Consistent,
            Evidence::CheckedCounterexample(vec![false, true]),
        ),
        (
            "assume P. assume not P. entails Q.",
            Conclusion::Entails,
            Premises::Contradictory,
            Evidence::Exhaustive,
        ),
        (
            "assume P. assume not P. satisfiable.",
            Conclusion::Unsatisfiable,
            Premises::Contradictory,
            Evidence::Exhaustive,
        ),
        (
            "assume P. satisfiable.",
            Conclusion::Satisfiable,
            Premises::Consistent,
            Evidence::CheckedModel(vec![true, false]),
        ),
    ] {
        let input = formalize(&format!("{declarations}{text}")).unwrap();
        let record = analyze(input.problem(), &EXACT, SETTINGS, worker);
        assert_eq!(record.outcome().conclusion(), conclusion, "{text}");
        assert_eq!(record.outcome().premises(), premises, "{text}");
        assert_eq!(*record.outcome().evidence(), evidence, "{text}");
        if conclusion == Conclusion::Entails && premises == Premises::Contradictory {
            assert!(record.outcome().summary().starts_with("vacuous entailment"));
        }
        let bytes = serde_json::to_vec(&record).unwrap();
        assert_eq!(Record::replay(input.problem(), &bytes).unwrap(), record);
    }
    let empty = formalize("entails false.").unwrap();
    let record = analyze(empty.problem(), &EXACT, SETTINGS, worker);
    assert_eq!(
        *record.outcome().evidence(),
        Evidence::CheckedCounterexample(vec![])
    );
}

#[test]
fn budget_and_partial_evidence() {
    let uncertain = formalize("proposition P. entails (P or not P).").unwrap();
    let mut settings = SETTINGS;
    settings.backend.max_assignments = 1;
    let stopped = analyze(uncertain.problem(), &EXACT, settings, worker);
    assert_eq!(stopped.outcome().execution(), Execution::ResourceLimit);
    assert_eq!(stopped.outcome().conclusion(), Conclusion::None);
    assert_eq!(stopped.outcome().evidence(), &Evidence::ExternalResponse);
    settings.backend.max_assignments = 2;
    settings.reference_assignments = 1;
    let external = analyze(uncertain.problem(), &EXACT, settings, worker);
    assert_eq!(external.outcome().execution(), Execution::Undecided);
    assert_eq!(external.outcome().premises(), Premises::Undecided);
    assert_eq!(external.outcome().conclusion(), Conclusion::None);
    assert_eq!(*external.outcome().evidence(), Evidence::ExternalResponse);

    let refuted = formalize("proposition P. entails P.").unwrap();
    settings.reference_assignments = 0;
    let checked = analyze(refuted.problem(), &EXACT, settings, worker);
    assert_eq!(checked.outcome().conclusion(), Conclusion::DoesNotEntail);
    assert_eq!(
        *checked.outcome().evidence(),
        Evidence::CheckedCounterexample(vec![false])
    );

    let many = (0..64)
        .map(|i| format!("proposition P{i}. "))
        .collect::<String>()
        + "satisfiable.";
    let large = formalize(&many).unwrap();
    let decision = analyze(large.problem(), &EXACT, settings, worker);
    assert_eq!(decision.outcome().conclusion(), Conclusion::Satisfiable);
    assert_eq!(
        decision.outcome().evidence(),
        &Evidence::CheckedModel(vec![false; 64])
    );

    assert_eq!(compare(&stopped, &external), Ok(()));
    assert_eq!(
        compare(&stopped, &checked),
        Err(ComparisonError::DifferentSubject)
    );
}

fn random(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6364136223846793005)
        .wrapping_add(1442695040888963407);
    *state >> 32
}

fn generate(state: &mut u64, depth: usize, slots: usize) -> Expr {
    let choice = random(state) % if depth == 1 { 3 } else { 6 };
    match choice {
        0 => Expr::True,
        1 => Expr::False,
        2 if slots == 0 => Expr::True,
        2 => Expr::Atom((random(state) % slots as u64) as u32),
        3 => Expr::Not(Box::new(generate(state, depth - 1, slots))),
        4 | 5 => {
            let left = Box::new(generate(state, depth - 1, slots));
            let right = Box::new(generate(state, depth - 1, slots));
            if choice == 4 {
                Expr::And(left, right)
            } else {
                Expr::Or(left, right)
            }
        }
        _ => unreachable!(),
    }
}

fn subject(names: Vec<String>, premises: Vec<Expr>, question: Question) -> Problem {
    Problem::new(CoreDocument::new(names, premises).unwrap(), question).unwrap()
}

fn agrees(problem: &Problem) -> bool {
    let Preparation::Applicable(request) = EXACT.prepare(problem, SETTINGS.backend) else {
        panic!("all propositional constructors must be supported");
    };
    let Scan::Complete { has_candidate, .. } = scan(problem, SETTINGS.reference_assignments) else {
        panic!("the generated case fits the reference budget");
    };
    match solve(&request).unwrap().reply {
        Reply::Sat(values) => assert!(
            has_candidate && check_witness(problem, &values),
            "{problem:?}"
        ),
        Reply::Unsat => assert!(!has_candidate, "{problem:?}"),
        other => panic!("unexpected backend reply {other:?}"),
    }
    has_candidate
}

#[test]
fn independent_evaluators_agree_under_each_small_assignment() {
    let mut state = 0x8af7_239b_0061_c45d;
    for slots in 0..=4 {
        let names: Vec<_> = (0..slots).map(|i| format!("P{i}")).collect();
        let changed_names: Vec<_> = (0..slots).map(|i| format!("Renamed_{i}")).collect();
        for example in 0..32 {
            let premises: Vec<_> = (0..(example % 4))
                .map(|_| generate(&mut state, 5, slots))
                .collect();
            let question = if example % 2 == 0 {
                Question::Satisfiable
            } else {
                Question::Entails(generate(&mut state, 5, slots))
            };
            let original = subject(names.clone(), premises.clone(), question.clone());
            let renamed = subject(changed_names.clone(), premises.clone(), question.clone());
            assert_eq!(agrees(&original), agrees(&renamed));
            for bits in 0..(1 << slots) {
                let values: Vec<_> = (0..slots).map(|i| (bits & (1 << i)) != 0).collect();
                let mut fixed = premises.clone();
                fixed.extend(values.iter().enumerate().map(|(slot, value)| {
                    let expr = Expr::Atom(slot as u32);
                    if *value {
                        expr
                    } else {
                        Expr::Not(Box::new(expr))
                    }
                }));
                let pinned = subject(names.clone(), fixed, question.clone());
                assert_eq!(agrees(&pinned), check_witness(&original, &values));
            }
        }
    }
}
