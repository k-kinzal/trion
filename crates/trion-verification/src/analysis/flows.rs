//! The choices of a flow: their guards exclude each other and cover every case.

use super::*;

/// Finds every choice block, so that its guards can be examined.
fn flow_nodes(node: &CompNode, out: &mut Vec<trion_language::syntax::ast::Flow>) {
    match node {
        CompNode::Flow(flow) => out.push((**flow).clone()),
        CompNode::All { items } | CompNode::Some { items } | CompNode::One { items } | CompNode::Sequence { items } => items.iter().for_each(|item| flow_nodes(item, out)),
        CompNode::Leaf { .. } => {}
    }
}

fn interpreted(formula: &Formula) -> bool {
    let mut all = true;
    formula.atoms(true, &mut |a, _| all &= matches!(a, trion_solver::Atom::Val { .. } | trion_solver::Atom::Num { .. }));
    all
}

/// The proof obligation of one choice: what was asked, at which instant and
/// from which premises.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct GuardObligation {
    pub statement: String,
    pub after: String,
    /// The instant at which the guards are evaluated.
    pub instant: String,
    /// What the proof may use: invariants, definitions and the conditions of
    /// the path that leads to the choice. The flow itself is never among them.
    pub premises: Vec<String>,
    pub exclusive: Status,
    pub covered: Status,
}

/// The condition under which a flow reaches a step: the guards chosen on the way.
fn path_condition(flow: &trion_language::syntax::ast::Flow, step: &str, lex: &Lexicon, seen: &mut Vec<String>) -> Formula {
    if step == flow.start || seen.iter().any(|s| s == step) {
        return Formula::True;
    }
    seen.push(step.to_string());
    let mut ways = Vec::new();
    for (from, to) in &flow.edges {
        if to == step {
            ways.push(path_condition(flow, from, lex, seen));
        }
    }
    for choice in &flow.choices {
        let before = path_condition(flow, &choice.after, lex, seen);
        let guards: Vec<Formula> = choice.arms.iter().map(|(guard, _)| trion_language::reading::group_formula(guard, lex)).collect();
        for (guard, (_, target)) in guards.iter().zip(&choice.arms) {
            if target == step {
                ways.push(Formula::And(vec![before.clone(), guard.clone()]));
            }
        }
        if choice.otherwise.as_deref() == Some(step) {
            let mut none = vec![before.clone()];
            none.extend(guards.iter().map(|g| Formula::not(g.clone())));
            ways.push(Formula::And(none));
        }
    }
    seen.pop();
    match ways.len() {
        0 => Formula::True,
        1 => ways.remove(0),
        _ => Formula::Or(ways),
    }
}

/// A choice needs exclusive guards and, without `otherwise`, exhaustive ones.
/// The guards are evaluated once, at the completion of the step before the
/// choice, over the states that can hold there: the invariants of the package,
/// the definitions of the domains the guards mention and the conditions of the
/// path to the choice. A state that only gated the activation may have changed
/// by then, and the flow is no premise of its own obligation. The instant of
/// the choice is one moment of the trace: the guards and the path are read at
/// the first moment, where every invariant holds as at any other.
pub(super) fn check_flow_guards(set: &SpecSet, model: &Model, lex: &Lexicon, inst: &Instance, bounds: Bounds, out: &mut Vec<Diagnostic>, claims: &mut Vec<ChoiceClaim>) -> Vec<GuardObligation> {
    let mut obligations = Vec::new();
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let scoped = lex.in_document(doc);
        for spec in &doc.specs {
            let Core::Deontic { vp: VpGroup::Composite(composition), .. } = &spec.sentence.core else { continue };
            let at = SpecRef { id: spec.display_id(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
            let own = |id: &str| id == at.id || id.starts_with(&format!("{}/", at.id));
            let mut flows = Vec::new();
            flow_nodes(&composition.root, &mut flows);
            for flow in &flows {
                for choice in &flow.choices {
                    let guards: Vec<Formula> = choice.arms.iter().map(|(guard, _)| trion_language::reading::group_formula(guard, &scoped)).collect();
                    let mut env = Environment::of(model, inst, bounds);
                    let mut premises = Vec::new();
                    for (index, c) in model.constraints.iter().enumerate() {
                        let Some(reference) = c.refs.first() else { continue };
                        if c.kind == ConstraintKind::Spec && !c.has_guard() && !own(&reference.id) && interpreted(&c.guarantee) {
                            env.premises.push(inst.group(index));
                            premises.push(format!("invariant {}", reference.id));
                        }
                    }
                    let known = env.premises.len();
                    env = env.using_definitions(&guards.iter().map(|g| Operand { assume: &Formula::True, guarantee: g, id: None }).collect::<Vec<_>>());
                    if env.premises.len() > known {
                        premises.push("the closed domains of the guards".to_string());
                    }
                    let path = path_condition(flow, &choice.after, &scoped, &mut Vec::new());
                    if path != Formula::True {
                        premises.push(format!("path condition {path}"));
                        env.premises.push(inst.add(&trion_language::reading::at_first_moment(&path)));
                    }
                    let placed: Vec<usize> = guards.iter().map(|g| inst.add(&trion_language::reading::at_first_moment(g))).collect();
                    let mut exclusive = Status::Unsatisfiable;
                    let mut refutations = Vec::new();
                    let mut overlap = None;
                    for (i, a) in guards.iter().enumerate() {
                        for (j, b) in guards.iter().enumerate().skip(i + 1) {
                            let question = env.ask(&[placed[i], placed[j]]);
                            let found = question.status();
                            if found == Status::Unsatisfiable {
                                refutations.push(question);
                                continue;
                            }
                            exclusive = if exclusive == Status::Satisfiable { exclusive } else { found };
                            if found == Status::Satisfiable && overlap.is_none() {
                                overlap = Some(Exclusivity::Overlap { first: i, second: j, witness: question });
                            }
                            let (code, message): (&str, &str) = if found == Status::Satisfiable && interpreted(a) && interpreted(b) { ("OVERLAPPING_FLOW_GUARDS", "two guards of this choice can hold together") } else { ("flow-guard-obligation", "the exclusivity of these guards is neither proved nor refuted") };
                            let diagnostic = if code == "OVERLAPPING_FLOW_GUARDS" { Diagnostic::error(code, message, vec![at.clone()]) } else { Diagnostic::warning(code, message, vec![at.clone()]) };
                            out.push(diagnostic);
                        }
                    }
                    let exclusivity = match (exclusive, overlap) {
                        (Status::Unsatisfiable, _) => Exclusivity::Exclusive { refutations },
                        (_, Some(overlap)) => overlap,
                        _ => Exclusivity::Unknown,
                    };
                    let none = inst.add(&trion_language::reading::at_first_moment(&Formula::And(guards.iter().map(|g| Formula::not(g.clone())).collect())));
                    let mut covered = Status::Unsatisfiable;
                    let mut coverage = None;
                    if choice.otherwise.is_none() {
                        let question = env.ask(&[none]);
                        covered = question.status();
                        if covered != Status::Unsatisfiable {
                            if covered == Status::Satisfiable && guards.iter().all(interpreted) {
                                out.push(Diagnostic::error("INCOMPLETE_FLOW_CHOICE", "the guards of this choice can all be false; add `otherwise`", vec![at.clone()]));
                            } else {
                                out.push(Diagnostic::warning("flow-guard-obligation", "the coverage of these guards is neither proved nor refuted", vec![at.clone()]));
                            }
                        }
                        coverage = Some(match covered {
                            Status::Unsatisfiable => Coverage::Covered { refutation: question },
                            Status::Satisfiable => Coverage::Missing { witness: question },
                            Status::Unknown => Coverage::Unknown,
                        });
                    }
                    claims.push(ChoiceClaim { environment: env.record(&format!("{} after {}", at.id, choice.after), "choice"), statement: at.id.clone(), after: choice.after.clone(), guards: placed, none, otherwise: choice.otherwise.is_some(), exclusive: exclusivity, covered: coverage });
                    obligations.push(GuardObligation { statement: at.id.clone(), after: choice.after.clone(), instant: format!("completion of step {}", choice.after), premises, exclusive, covered });
                }
            }
        }
    }
    obligations
}
