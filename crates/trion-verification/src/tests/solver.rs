//! The built-in solver over the contracts of a model.

use super::common::*;
use trion_solver::Instance;
use trion_solver::Status;

#[test]
fn the_solver_finds_a_minimal_core() {
    let model = run("kind is A and B.\nThe API shall stop.\nkind is C.\n").model;
    // Each contract is a group of its own; its condition is what a query may force.
    let groups: Vec<_> = model.constraints.iter().map(|c| (c.formula(), c.has_guard().then(|| c.assume.clone()))).collect();
    let instance = Instance::new(&model.background, &groups, None);
    let all: Vec<usize> = (0..groups.len()).collect();
    assert_eq!(instance.status(&all, &[]), Status::Unsatisfiable);
    // The second enumeration, and what the first one says about its value.
    let (core, minimal) = instance.unsat_subset(&all, &[]);
    assert!(minimal);
    let lines: Vec<usize> = core.iter().map(|&i| model.constraints[i].refs[0].line).collect();
    assert_eq!(core.len(), 2, "{core:?}");
    assert_ne!(lines[0], lines[1], "{lines:?}");
    assert!(lines.iter().all(|line| model.constraints.iter().any(|c| c.refs[0].line == *line && c.refs[0].text.starts_with("kind is"))), "{lines:?}");
}
