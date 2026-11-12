//! The search for conflict sets: statements that cannot all hold, alone,
//! while the condition of one of them is met, or in a situation in which the
//! conditions of several of them hold together.

use super::*;

/// The statements of a set with what the explanation of a conflict needs.
pub(super) struct Authored<'a> {
    specs: Vec<(&'a Spec, &'a Document, String)>,
    lex: &'a Lexicon,
}

impl<'a> Authored<'a> {
    pub(super) fn new(set: &'a SpecSet, lex: &'a Lexicon) -> Self {
        let mut specs = Vec::new();
        for pkg in &set.packages {
            for doc in &pkg.documents {
                for spec in &doc.specs {
                    let display = if pkg.is_root { spec.display_id() } else { format!("{}::{}", pkg.name, spec.display_id()) };
                    specs.push((spec, doc, display));
                }
            }
        }
        Self { specs, lex }
    }

    /// The statement a reference of the model points at or into.
    pub(super) fn owner(&self, r: &SpecRef) -> Option<(&'a Spec, &'a Document)> {
        self.specs.iter().find(|(s, _, id)| s.file == r.file && (r.id == *id || r.id.strip_prefix(id.as_str()).is_some_and(|rest| rest.starts_with('/')))).map(|(s, d, _)| (*s, *d))
    }

    /// `true` for a `should` statement: a recommendation is no hard constraint.
    pub(super) fn is_recommendation(&self, c: &Constraint) -> bool {
        c.refs.first().and_then(|r| self.owner(r)).is_some_and(|(s, _)| matches!(s.sentence.core, Core::Deontic { modal: Modal::Should, .. }))
    }

    /// `true` for a statement with no modal force: it says how things are,
    /// and no system has to make it so.
    pub(super) fn is_description(&self, c: &Constraint) -> bool {
        c.refs.first().and_then(|r| self.owner(r)).is_some_and(|(s, _)| !matches!(s.sentence.core, Core::Deontic { .. }))
    }

    fn element(&self, r: &SpecRef) -> ConflictElement {
        let Some((spec, doc)) = self.owner(r) else {
            return ConflictElement { reference: r.clone(), scopes: Vec::new(), expansion: r.text.clone(), terms: Vec::new() };
        };
        let mut scopes: Vec<String> = spec.sections.iter().map(|title| format!("section \"{title}\"")).collect();
        let written = spec.sentence.source.to_lowercase();
        let frames = &spec.sentence.frames;
        let conditions = frames.scopes.iter().chain(&frames.states).map(|f| format!("{} {}", f.keyword, f.clause.render())).chain(frames.trigger.iter().map(|t| format!("{} {}", t.keyword, t.clause.render())));
        // A condition the statement does not write itself comes from a block around it.
        scopes.extend(conditions.filter(|c| !written.contains(&c.to_lowercase())));
        let scoped = self.lex.in_document(doc);
        let mut terms: Vec<String> = occurrences(&spec.sentence, &scoped).into_iter().map(|(term, kind)| format!("{term} ({kind})")).collect();
        terms.sort();
        terms.dedup();
        ConflictElement { reference: r.clone(), scopes, expansion: trion_language::expand::expand(spec), terms }
    }

    /// The definitions whose term one of the elements uses.
    fn definitions(&self, elements: &[ConflictElement]) -> Vec<SpecRef> {
        let used: BTreeSet<&str> = elements.iter().flat_map(|e| &e.terms).filter_map(|t| t.rsplit_once(" (").map(|(term, _)| term)).collect();
        let mut out = Vec::new();
        for (spec, doc, display) in &self.specs {
            let scoped = self.lex.in_document(doc);
            let defines = match &spec.sentence.core {
                Core::Definition { term, .. } => Some(trion_language::reading::np_key(term, &scoped)),
                Core::Description { subject: trion_language::syntax::ast::NpGroup::Single(np), predicate: trion_language::syntax::ast::Predicate::Enumeration { .. }, adverb: None, .. } if spec.sentence.frames.is_empty() => Some(trion_language::reading::np_key(np, &scoped)),
                _ => None,
            };
            if defines.is_some_and(|term| used.contains(term.as_str())) && !elements.iter().any(|e| e.reference.id == *display && e.reference.file == spec.file) {
                out.push(SpecRef { id: display.clone(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() });
            }
        }
        out
    }
}

fn atom_names(f: &Formula) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    f.atoms(true, &mut |a, _| {
        names.insert(a.to_string());
    });
    names
}

/// The contracts of a conflict set and the background axioms that touch them.
fn derivation(model: &Model, members: &[usize], conditions: &[usize]) -> Vec<DerivationStep> {
    let mut steps = Vec::new();
    let mut atoms = BTreeSet::new();
    for c in members.iter().chain(conditions).map(|&m| &model.constraints[m]) {
        atoms.extend(atom_names(&c.assume));
        atoms.extend(atom_names(&c.guarantee));
    }
    for &m in members {
        let c = &model.constraints[m];
        let id = c.refs.first().map_or(String::new(), |r| r.id.clone());
        // What a statement says about terms is told apart from what it requires.
        let origin = if c.kind.is_axiom() { format!("meaning of {id}") } else { id };
        steps.push(DerivationStep { origin, assume: c.assume.to_string(), guarantee: c.guarantee.to_string() });
    }
    for c in conditions.iter().map(|&g| &model.constraints[g]) {
        steps.push(DerivationStep { origin: format!("condition of {}", c.refs.first().map_or("", |r| r.id.as_str())), assume: Formula::True.to_string(), guarantee: c.assume.to_string() });
    }
    for axiom in &model.background {
        if !atom_names(axiom).is_disjoint(&atoms) {
            steps.push(DerivationStep { origin: "background".to_string(), assume: Formula::True.to_string(), guarantee: axiom.to_string() });
        }
    }
    steps
}

/// Where the findings of the conflict search go.
struct Findings<'a> {
    authored: &'a Authored<'a>,
    diagnostics: &'a mut Vec<Diagnostic>,
    conflicts: Vec<ConflictExplanation>,
    seen: BTreeSet<Vec<String>>,
    /// The hard constraints were refuted with no condition forced.
    unsatisfiable: bool,
    /// A conflict was reported: a refutation, or a conflict under conditions.
    conflicted: bool,
    /// A query ended at the bounds.
    unknown: bool,
    /// The conflicts that are reported now are conflicts of a situation:
    /// the questions of the situations certify them.
    situation: bool,
    /// Refutations that have no row of their own in the inventory: the kind
    /// of the claim, the conditions that were forced and the refuted groups.
    refuted: Vec<(&'static str, Vec<Lit>, Vec<usize>)>,
    /// The condition of each group, as the instance numbers it.
    guards: Vec<Option<Lit>>,
}

impl Findings<'_> {
    /// Reports one conflict set. `conditions` are the statements whose
    /// conditions were forced; `minimal` tells whether the set was proved minimal.
    fn report(&mut self, model: &Model, members: &[usize], conditions: &[usize], minimal: bool) {
        let context: Vec<&SpecRef> = conditions.iter().filter_map(|&g| model.constraints[g].refs.first()).collect();
        let mut refs: Vec<SpecRef> = Vec::new();
        for r in members.iter().flat_map(|&m| &model.constraints[m].refs).chain(context.iter().copied()) {
            if !refs.contains(r) {
                refs.push(r.clone());
            }
        }
        // What contradicts a detail contradicts the statement that the detail details.
        let mut reached: Vec<String> = Vec::new();
        let mut at = 0;
        while at < refs.len() {
            // An edge of a concept block or an item of a list details what its block details.
            let block = refs[at].id.split('/').next().unwrap_or(&refs[at].id).to_string();
            for parent in model.refined.get(&refs[at].id).into_iter().chain(model.refined.get(&block).filter(|_| block != refs[at].id)).flatten() {
                if !refs.contains(parent) {
                    reached.push(format!("`{}` details `{}`", refs[at].id, parent.id));
                    refs.push(parent.clone());
                }
            }
            at += 1;
        }
        let mut key: Vec<String> = refs.iter().map(|r| r.id.clone()).collect();
        key.sort();
        if !self.seen.insert(key) {
            return;
        }
        let size = if minimal { String::new() } else { " (the analysis bounds ended before this set was proved minimal)".to_string() };
        let size = if reached.is_empty() { size } else { format!("{size}; {}, so the detailed statement cannot hold either", reached.join(" and ")) };
        let soft = members.iter().any(|&m| self.authored.is_recommendation(&model.constraints[m]));
        if !self.situation && members.iter().any(|&m| model.constraints[m].kind == ConstraintKind::Form) {
            self.refuted.push(("shape-violation", conditions.iter().filter_map(|&g| self.guards.get(g).copied().flatten()).collect(), members.to_vec()));
        }
        // What the conflict is a conflict under.
        let met = match context.as_slice() {
            [] => String::new(),
            [one] => format!(" when the condition of `{}` is met", one.text),
            several => format!(" when the conditions of {} are met together, and no statement without a modal verb says that these conditions exclude each other", several.iter().map(|r| format!("`{}`", r.id)).collect::<Vec<_>>().join(", ")),
        };
        let advice = match context.len() {
            0 => "",
            1 => "; if one is an exception to the other, write it with `, unless`, or write `overrides [ID]` under the statement that wins",
            _ => "; write the exception with `, unless`, write `overrides [ID]` under the statement that wins, or state without a modal verb that the conditions cannot hold together",
        };
        let diagnostic = if members.iter().any(|&m| model.constraints[m].kind == ConstraintKind::Form) {
            Diagnostic::error("shape-violation", "this specification does not have the form its bound role requires: no such thing exists in that specification set", refs.clone())
        } else if soft {
            // A recommendation is no hard constraint: breaking it leaves the
            // specification consistent.
            Diagnostic::error("recommendation-violation", format!("a recommendation cannot be followed together with these specifications{met}; the hard constraints stay consistent{size}"), refs.clone())
        } else {
            Diagnostic::error("contradiction", format!("these specifications cannot all hold{met}{advice}{size}"), refs.clone())
        };
        // A refutation of the hard constraints with no condition forced makes
        // the specification unsatisfiable. A conflict under conditions leaves
        // it satisfiable, where the conditions never hold, and inconsistent
        // all the same: the conditions can hold.
        self.unsatisfiable |= diagnostic.code != "recommendation-violation" && conditions.is_empty();
        self.conflicted |= diagnostic.code != "recommendation-violation";
        let elements: Vec<ConflictElement> = refs.iter().map(|r| self.authored.element(r)).collect();
        let definitions = self.authored.definitions(&elements);
        self.conflicts.push(ConflictExplanation {
            code: diagnostic.code.clone(),
            condition: (!conditions.is_empty()).then(|| conditions.iter().map(|&g| model.constraints[g].assume.to_string()).collect::<Vec<_>>().join(" ∧ ")),
            minimal,
            elements,
            derivation: derivation(model, members, conditions),
            definitions,
        });
        self.diagnostics.push(diagnostic);
    }
}

/// What the search for conflict sets found.
pub(super) struct Conflicts {
    /// An explanation of every reported conflict set.
    pub(super) conflicts: Vec<ConflictExplanation>,
    /// The conditions that make a statement hold emptily.
    pub(super) coverage: CoverageExplanation,
    /// The hard constraints were refuted with no condition forced.
    pub(super) unsatisfiable: bool,
    /// A conflict was reported: a refutation, or a conflict under conditions.
    /// The specification is then inconsistent.
    pub(super) conflicted: bool,
    /// A query ended at the bounds, or situations were left unexamined.
    pub(super) unknown: bool,
    /// Refutations that have no row of their own in the inventory: the kind
    /// of the claim, the conditions that were forced and the refuted groups.
    pub(super) refuted: Vec<(&'static str, Vec<Lit>, Vec<usize>)>,
    /// The situations, when the statements are consistent one condition at a time.
    pub(super) situations: Option<situations::Situations>,
}

impl Conflicts {
    /// What the search decides about the consistency of the statements: a
    /// conflict settles it, and a search that the bounds ended settles nothing.
    pub(super) fn verdict(&self) -> &'static str {
        if self.conflicted {
            "inconsistent"
        } else if self.unknown {
            "unknown"
        } else {
            "consistent"
        }
    }
}

/// Decides the consistency of the contracts of a model and reports each
/// conflict set. `standing` gives, for a contract with a condition, the
/// group of the instance that makes the condition hold while the response is due.
///
/// The statements without normative force say which situations can occur.
/// The statements are consistent when they can all hold, when they can all
/// hold while the condition of each one is met, and when they can all be
/// kept in each situation in which several conditions hold together.
pub(super) fn search(model: &Model, inst: &Instance, standing: &BTreeMap<usize, usize>, authored: &Authored, diagnostics: &mut Vec<Diagnostic>) -> Conflicts {
    let mut found = Findings { authored, diagnostics, conflicts: Vec::new(), seen: BTreeSet::new(), unsatisfiable: false, conflicted: false, unknown: false, situation: false, refuted: Vec::new(), guards: (0..model.constraints.len()).map(|g| inst.guard(g)).collect() };
    let coverage = find_conflicts(model, inst, &mut found);
    let mut examined = None;
    if !found.conflicted && !found.unknown {
        let soft = |i: usize| authored.is_recommendation(&model.constraints[i]);
        let situations = situations::search(model, inst, standing, &soft, &|i| authored.is_description(&model.constraints[i]));
        found.situation = true;
        for conflict in &situations.conflicts {
            found.report(model, &conflict.statements, &conflict.conditions, true);
        }
        found.unknown |= situations.conflicts.is_empty() && !situations.decided;
        examined = Some(situations);
    }
    let Findings { conflicts, unsatisfiable, conflicted, unknown, refuted, .. } = found;
    Conflicts { conflicts, coverage, unsatisfiable, conflicted, unknown, refuted, situations: examined }
}

/// Extracts unsatisfiable subsets until the rest is satisfiable: first among
/// the hard constraints, then with the recommendations added.
fn find_conflicts(model: &Model, inst: &Instance, found: &mut Findings) -> CoverageExplanation {
    let all: Vec<usize> = (0..model.constraints.len()).collect();
    let soft: BTreeSet<usize> = all.iter().copied().filter(|&g| found.authored.is_recommendation(&model.constraints[g])).collect();
    let mut active: Vec<usize> = all.iter().copied().filter(|g| !soft.contains(g)).collect();
    while !active.is_empty() {
        match inst.status(&active, &[]) {
            Status::Satisfiable => break,
            Status::Unknown => {
                found.unknown = true;
                break;
            }
            Status::Unsatisfiable => {}
        }
        let (core, minimal) = inst.unsat_subset(&active, &[]);
        found.report(model, &core, &[], minimal);
        let Some(last) = core.last() else { break };
        active.retain(|g| g != last);
    }
    // A recommendation that cannot be followed is reported apart from the
    // inconsistency of the hard constraints.
    let mut advised: Vec<usize> = all.iter().copied().filter(|g| active.contains(g) || soft.contains(g)).collect();
    while !found.unknown && advised.iter().any(|g| soft.contains(g)) {
        match inst.status(&advised, &[]) {
            Status::Satisfiable => break,
            Status::Unknown => {
                found.unknown = true;
                break;
            }
            Status::Unsatisfiable => {}
        }
        let (core, minimal) = inst.unsat_subset(&advised, &[]);
        found.report(model, &core, &[], minimal);
        let Some(last) = core.iter().rev().find(|g| soft.contains(g)) else { break };
        advised.retain(|g| g != last);
    }
    let mut coverage = CoverageExplanation::default();
    // What says which situations can occur: the meaning of the terms and
    // each statement without normative force.
    let possible: Vec<usize> = active.iter().copied().filter(|&g| model.constraints[g].kind.is_axiom() || found.authored.is_description(&model.constraints[g])).collect();
    // A guarded contract is vacuously true when its guard is false, so each
    // guard is forced true before checking.
    for g in 0..model.constraints.len() {
        let Some(guard) = inst.guard(g) else { continue };
        if !advised.contains(&g) {
            continue;
        }
        // No query leaves a statement out: a general permission that a
        // narrower prohibition restricts is narrowed in its own formula.
        let hard = active.clone();
        let mut vacuous = |reason: &str| {
            if let Some(reference) = model.constraints[g].refs.first() {
                coverage.vacuous.push(VacuousCondition { reference: reference.clone(), condition: model.constraints[g].assume.to_string(), reason: reason.to_string() });
            }
        };
        match inst.status(&hard, &[guard]) {
            Status::Unknown => found.unknown = true,
            Status::Unsatisfiable => {
                // The statement holds only because its condition cannot occur.
                let alone = inst.status(&[], &[guard]) == Status::Unsatisfiable;
                // A condition that holds in no situation that can occur
                // leaves its statement without a case, and breaks nothing.
                match if alone { Status::Unsatisfiable } else { inst.status(&possible, &[guard]) } {
                    Status::Unknown => {
                        found.unknown = true;
                        continue;
                    }
                    Status::Unsatisfiable => {
                        let (core, _) = if alone { (Vec::new(), true) } else { inst.unsat_subset(&possible, &[guard]) };
                        let by: Vec<&SpecRef> = core.iter().filter_map(|&c| model.constraints[c].refs.first()).collect();
                        let reason = if alone { "unreachable in every situation".to_string() } else { format!("excluded by {}", by.iter().map(|r| format!("`{}`", r.id)).collect::<Vec<_>>().join(" and ")) };
                        vacuous(&reason);
                        if !alone {
                            found.refuted.push(("condition-unreachable", vec![guard], core.clone()));
                        }
                        if let Some(at) = model.constraints[g].refs.first() {
                            let mut refs = vec![at.clone()];
                            refs.extend(by.into_iter().filter(|r| r.id != at.id).cloned());
                            // Statements that exclude the conditions of each other are reported once.
                            let mut key: Vec<String> = refs.iter().map(|r| r.id.clone()).collect();
                            key.sort();
                            if found.seen.insert(key) {
                                found.diagnostics.push(Diagnostic::error("condition-unreachable", format!("the condition of `{}` holds in no situation that can occur ({reason}): the statement is kept vacuously and requires nothing", at.id), refs));
                            }
                        }
                        continue;
                    }
                    Status::Satisfiable => {}
                }
                // A statement that cannot be kept alone while the condition
                // is met forbids the situation or ends it: it is in conflict
                // with nothing there, and what is left is examined without it.
                let mut kept = hard.clone();
                let mut excluding: Vec<usize> = Vec::new();
                let conflict = loop {
                    let (core, minimal) = inst.unsat_subset(&kept, &[guard]);
                    let alone: Vec<usize> = core.iter().copied().filter(|&c| c != g && !possible.contains(&c) && inst.status(&[possible.as_slice(), &[c]].concat(), &[guard]) == Status::Unsatisfiable).collect();
                    if alone.is_empty() {
                        break Some((core, minimal));
                    }
                    kept.retain(|c| !alone.contains(c));
                    excluding.extend(alone);
                    match inst.status(&kept, &[guard]) {
                        Status::Unsatisfiable => {}
                        Status::Unknown => {
                            found.unknown = true;
                            break None;
                        }
                        Status::Satisfiable => break None,
                    }
                };
                for &statement in &excluding {
                    let (core, _) = inst.unsat_subset(&[possible.as_slice(), &[statement]].concat(), &[guard]);
                    found.refuted.push(("condition-excluded-by-a-statement", vec![guard], core));
                }
                let Some((core, minimal)) = conflict else {
                    let by: Vec<String> = excluding.iter().filter_map(|&c| model.constraints[c].refs.first()).map(|r| format!("`{}`", r.id)).collect();
                    vacuous(&format!("excluded by {}", by.join(" and ")));
                    continue;
                };
                vacuous("unreachable under the other statements");
                found.report(model, &core, &[g], minimal);
            }
            Status::Satisfiable => {
                let wide = advised.clone();
                if wide.len() > hard.len() {
                    match inst.status(&wide, &[guard]) {
                        Status::Unknown => found.unknown = true,
                        Status::Unsatisfiable => {
                            let (core, minimal) = inst.unsat_subset(&wide, &[guard]);
                            found.report(model, &core, &[g], minimal);
                        }
                        Status::Satisfiable => {}
                    }
                }
            }
        }
    }
    coverage
}
