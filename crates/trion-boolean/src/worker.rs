//! Candidate search over the target syntax, independent of the original trees.

use super::{Reply, Request, Response, Term, ADAPTER, BACKEND, PROTOCOL, STAGES};
use trion_core::{DEFINITIONS, SEMANTICS};

fn valid(term: &Term, slots: usize) -> bool {
    match term {
        Term::Constant(_) => true,
        Term::Literal { slot, .. } => (*slot as usize) < slots,
        Term::All(left, right) | Term::Any(left, right) => {
            valid(left, slots) && valid(right, slots)
        }
    }
}

fn evaluate(term: &Term, values: &[bool]) -> bool {
    match term {
        Term::Constant(value) => *value,
        Term::Literal { slot, positive } => values[*slot as usize] == *positive,
        Term::All(left, right) => evaluate(left, values) && evaluate(right, values),
        Term::Any(left, right) => evaluate(left, values) || evaluate(right, values),
    }
}

/// Increment the little-endian Boolean word. The empty word overflows after
/// its first assignment, exactly like a fully set non-empty word.
fn next(values: &mut [bool]) -> bool {
    for value in values {
        *value = !*value;
        if *value {
            return true;
        }
    }
    false
}

pub fn solve(request: &Request) -> Result<Response, &'static str> {
    if request.protocol != PROTOCOL
        || request.backend != BACKEND
        || request.adapter != ADAPTER
        || request.stages != STAGES
        || request.semantics != SEMANTICS
        || request.definitions != DEFINITIONS
        || !request.added_assumptions.is_empty()
        || !request
            .condition
            .iter()
            .all(|term| valid(term, request.slots))
    {
        return Err("incompatible or malformed worker request");
    }
    let mut values = Vec::new();
    values
        .try_reserve(request.slots)
        .map_err(|_| "worker allocation failed")?;
    values.resize(request.slots, false);
    let mut reply = Reply::ResourceLimit;
    for _ in 0..request.settings.max_assignments {
        if request.condition.iter().all(|term| evaluate(term, &values)) {
            reply = Reply::Sat(values);
            break;
        }
        if !next(&mut values) {
            reply = Reply::Unsat;
            break;
        }
    }
    Ok(Response {
        request: request.id(),
        scope: request.scope,
        reply,
    })
}
