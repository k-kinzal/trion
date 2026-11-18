//! The choices of a flow: the obligations that their guards exclude each
//! other and cover every case.

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

/// The questions of one choice as proof obligations: for each pair of
/// guards, that they cannot hold together; and without `otherwise`, that
/// they cannot all be false. Each is unsatisfiable when it holds.
pub(super) struct ChoiceQuestion {
    pub statement: SpecRef,
    pub after: String,
    /// `exclusive` for a pair of guards, `covered` for all of them.
    pub kind: &'static str,
    /// The guards that the question names, by their place in the choice.
    pub guards: Vec<usize>,
    pub query: Vec<usize>,
    /// What the question may use, in words.
    pub premises: Vec<String>,
}

/// The questions of every choice of a flow, added to `inst`, and a finding
/// for each choice whose guards no formula interprets: its questions say
/// nothing about the guards and are not asked. `group` holds the formula of
/// each contract of the model in `inst`.
pub(super) fn choice_questions(set: &SpecSet, model: &Model, lex: &Lexicon, inst: &Instance, group: &[usize], bounds: Bounds, out: &mut Vec<Diagnostic>) -> Vec<ChoiceQuestion> {
    let mut questions = Vec::new();
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
                    if !guards.iter().all(interpreted) {
                        out.push(Diagnostic::warning("flow-guard-obligation", format!("the guards of the choice after `{}` are not all states or quantities: whether they exclude each other and cover every case is neither proved nor refuted", choice.after), vec![at.clone()]));
                        continue;
                    }
                    let mut env = Environment::of(model, inst, bounds);
                    let mut premises = Vec::new();
                    for (index, c) in model.constraints.iter().enumerate() {
                        let Some(reference) = c.refs.first() else { continue };
                        if c.kind == ConstraintKind::Spec && !c.has_guard() && !own(&reference.id) && interpreted(&c.guarantee) {
                            env.premises.push(group[index]);
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
                    for i in 0..guards.len() {
                        for j in i + 1..guards.len() {
                            let query = env.query(&[placed[i], placed[j]]);
                            questions.push(ChoiceQuestion { statement: at.clone(), after: choice.after.clone(), kind: "exclusive", guards: vec![i, j], query, premises: premises.clone() });
                        }
                    }
                    if choice.otherwise.is_none() {
                        let none = inst.add(&trion_language::reading::at_first_moment(&Formula::And(guards.iter().map(|g| Formula::not(g.clone())).collect())));
                        let query = env.query(&[none]);
                        questions.push(ChoiceQuestion { statement: at.clone(), after: choice.after.clone(), kind: "covered", guards: (0..guards.len()).collect(), query, premises: premises.clone() });
                    }
                }
            }
        }
    }
    questions
}
