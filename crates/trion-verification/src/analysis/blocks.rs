//! The `check` and `example` blocks of a set: each is a question asked in an
//! environment over the unrolled formulas of the package.

use super::*;

/// The environment a question is asked in: the unrolled background of the
/// model, the selected premises and the analysis bounds. Both sides of a
/// comparison and of a check are read in one environment, over the same
/// unrolled formulas as the consistency of the package.
#[derive(Clone)]
pub(super) struct Environment<'a> {
    pub model: &'a Model,
    /// The unrolled model: its formulas are named by their numbers.
    pub instance: &'a Instance,
    /// The selected premises, as formulas that every interpretation satisfies.
    pub premises: Vec<usize>,
    pub bounds: Bounds,
    /// `true` when the premises hold every axiom that reaches the operands.
    pub complete: bool,
}

/// What a question is about: a contract of the model, or formulas of a flow.
pub(super) struct Operand<'a> {
    pub assume: &'a Formula,
    pub guarantee: &'a Formula,
    /// The statement of the operand, which is no premise of its own question.
    pub id: Option<&'a str>,
}

impl<'a> Operand<'a> {
    fn of(c: &'a Constraint) -> Self {
        Self { assume: &c.assume, guarantee: &c.guarantee, id: c.refs.first().map(|r| r.id.as_str()) }
    }
}

impl<'a> Environment<'a> {
    /// The environment of the background alone.
    pub(super) fn of(model: &'a Model, instance: &'a Instance, bounds: Bounds) -> Self {
        Self { model, instance, premises: Vec::new(), bounds, complete: false }
    }

    /// Adds the definitions that the operands need: each closed domain they
    /// mention holds one of its values. A domain that an operand itself
    /// declares is left out, since an operand is no premise.
    pub(super) fn using_definitions(self, operands: &[Operand]) -> Self {
        self.using_definitions_within(operands, usize::MAX)
    }

    /// As `using_definitions`, with the axioms that reach the operands in at
    /// most `steps` steps of shared atoms. Fewer premises prove no less
    /// soundly; only the whole reach can refute.
    pub(super) fn using_definitions_within(mut self, operands: &[Operand], steps: usize) -> Self {
        let mut mentioned = BTreeSet::new();
        let mut declared = BTreeSet::new();
        for c in operands {
            let mut visit = |a: &trion_solver::Atom, _: bool| match a {
                trion_solver::Atom::Val { attr, .. } => {
                    mentioned.insert(attr.clone());
                }
                trion_solver::Atom::Dom { attr, .. } => {
                    declared.insert(attr.clone());
                }
                _ => {}
            };
            c.assume.atoms(true, &mut visit);
            c.guarantee.atoms(true, &mut visit);
        }
        // What the vocabulary means is a premise of every proof, apart from
        // what an operand itself says.
        let own: BTreeSet<&str> = operands.iter().filter_map(|c| c.id).collect();
        // Only an axiom that reaches the operands through shared atoms can bear
        // on the question; the others would only enlarge the search.
        let names = |f: &Formula| {
            let mut found = BTreeSet::new();
            f.atoms(true, &mut |a: &trion_solver::Atom, _: bool| {
                found.insert(format!("{a:?}"));
            });
            found
        };
        let mut reached: BTreeSet<String> = operands.iter().flat_map(|c| names(c.assume).into_iter().chain(names(c.guarantee))).collect();
        // A refinement says what its detailed statement means. It bears on a
        // question only through that statement: the details hold or fail
        // whatever the detailed statement says, so it is reached by the atoms
        // of the detailed statement alone.
        let reach = |c: &Constraint| match (c.kind, c.refs.first()) {
            (ConstraintKind::Refinement, Some(origin)) => constraints_of(self.model, &origin.id).into_iter().flat_map(|own| names(&self.model.constraints[own].assume).into_iter().chain(names(&self.model.constraints[own].guarantee))).collect(),
            _ => names(&c.guarantee),
        };
        let axioms: Vec<(usize, BTreeSet<String>)> = self.model.constraints.iter().enumerate().filter(|(_, c)| c.kind.is_axiom() && !c.refs.first().is_some_and(|r| own.contains(r.id.as_str()))).map(|(i, c)| (i, reach(c))).collect();
        let mut taken = vec![false; axioms.len()];
        for _ in 0..steps {
            // One step takes the axioms that touch what the last step reached.
            let frontier = reached.clone();
            let mut grew = false;
            for (i, (axiom, atoms)) in axioms.iter().enumerate() {
                if !taken[i] && !atoms.is_disjoint(&frontier) {
                    taken[i] = true;
                    grew = true;
                    reached.extend(atoms.iter().cloned());
                    let premise = self.premise_of(*axiom);
                    if !self.premises.contains(&premise) {
                        self.premises.push(premise);
                    }
                }
            }
            if !grew {
                self.complete = true;
                break;
            }
        }
        for (attr, values) in &self.model.closed_domains {
            if mentioned.contains(attr) && !declared.contains(attr) && !values.is_empty() {
                // The attribute holds one of its values at each moment.
                let one = Formula::Or(values.iter().map(|value| Formula::Atom(trion_solver::Atom::Val { attr: attr.clone(), value: value.clone() })).collect());
                let premise = self.instance.add(&trion_language::reading::at_each_moment(&one, self.bounds.trace_length));
                self.premises.push(premise);
            }
        }
        self
    }

    /// The formula over the trace of an axiom of the model. A refinement is
    /// no part of the trace of the package, since every party of it stands
    /// there already; as a premise it holds at every moment.
    fn premise_of(&self, axiom: usize) -> usize {
        let c = &self.model.constraints[axiom];
        if c.kind == ConstraintKind::Refinement {
            return self.instance.add(&trion_language::reading::unroll_axiom(&c.guarantee, self.bounds.trace_length));
        }
        self.instance.group(axiom)
    }

    /// The numbers of the formulas of a question in this environment.
    pub(super) fn query(&self, formulas: &[usize]) -> Vec<usize> {
        self.instance.background().iter().chain(&self.premises).chain(formulas).copied().collect()
    }

    /// Asks a question in this environment and keeps it with its answer.
    pub(super) fn ask(&self, formulas: &[usize]) -> Question {
        Question::ask(self.instance, self.query(formulas))
    }

    /// What the search establishes for the formulas in this environment.
    pub(super) fn status(&self, formulas: &[usize]) -> Status {
        self.ask(formulas).status()
    }

    /// The formulas of the given contracts over the trace as a list of
    /// formulas whose conjunction says the same. A contract over a trace is
    /// a conjunction over its moments, and what a condition requires is a
    /// conjunction of responses: `a → (b ∧ c)` is listed as `a → b` and
    /// `a → c`. A question about a side is then asked one formula at a time.
    pub(super) fn conjuncts(&self, contracts: &[usize]) -> Vec<usize> {
        fn flatten(formula: &Formula, out: &mut Vec<Formula>) {
            match formula {
                Formula::And(items) => items.iter().for_each(|item| flatten(item, out)),
                Formula::True => {}
                Formula::Implies(condition, response) => {
                    let mut parts = Vec::new();
                    flatten(response, &mut parts);
                    out.extend(parts.into_iter().map(|part| Formula::Implies(condition.clone(), Box::new(part))));
                }
                other => out.push(other.clone()),
            }
        }
        let all = self.instance.formulas();
        let mut out = Vec::new();
        for &contract in contracts {
            let id = self.instance.group(contract);
            match &all[id] {
                formula @ (Formula::And(_) | Formula::Implies(..)) => {
                    let mut parts = Vec::new();
                    flatten(formula, &mut parts);
                    out.extend(parts.iter().map(|part| self.instance.add(part)));
                }
                Formula::True => {}
                _ => out.push(id),
            }
        }
        out
    }

    /// The negation of each of the formulas, as new formulas.
    pub(super) fn negations(&self, formulas: &[usize]) -> Vec<usize> {
        let all = self.instance.formulas();
        formulas.iter().map(|&id| self.instance.add(&Formula::not(all[id].clone()))).collect()
    }

    pub(super) fn record(&self, name: &str, kind: &str) -> EnvironmentRecord {
        EnvironmentRecord { name: name.to_string(), kind: kind.to_string(), bounds: used_bounds(self.model, self.bounds), background: self.instance.background().to_vec(), premises: self.premises.clone() }
    }
}

/// The bounds as the reader used them.
pub(super) fn used_bounds(model: &Model, bounds: Bounds) -> UsedBounds {
    UsedBounds { moments: bounds.trace_length.max(2), individuals: model.instance_scope, decisions: bounds.decisions }
}

fn constraints_of(model: &Model, id: &str) -> Vec<usize> {
    let nested = format!("{id}/");
    (0..model.constraints.len()).filter(|&i| matches!(model.constraints[i].kind, ConstraintKind::Spec | ConstraintKind::Permission) && model.constraints[i].refs.first().is_some_and(|r| r.id == id || r.id.starts_with(&nested))).collect()
}

/// Why the operands of a question have no formulas.
enum OperandError {
    /// No statement has the identifier.
    Unresolved,
    /// The statement is accepted and has no formal interpretation.
    Unsupported(String),
}

/// The contracts of the named statements, by their index in the model.
fn operand_formulas(set: &SpecSet, model: &Model, ids: &[String]) -> Result<Vec<usize>, OperandError> {
    let mut all = Vec::new();
    for id in ids {
        let found = constraints_of(model, id);
        if found.is_empty() {
            let declared = set.packages.iter().filter(|p| p.is_root).any(|p| p.identifiers().contains(id));
            return Err(if declared { OperandError::Unsupported(id.clone()) } else { OperandError::Unresolved });
        }
        all.extend(found);
    }
    Ok(all)
}

/// Reports why an obligation cannot be examined.
fn operand_diagnostic(error: &OperandError, obligation: &str, at: SpecRef) -> Diagnostic {
    match error {
        OperandError::Unresolved => Diagnostic::error("UNRESOLVED_REFERENCE", format!("the {obligation} names a statement that does not exist"), vec![at]),
        OperandError::Unsupported(id) => Diagnostic::error("UNSUPPORTED_SEMANTICS", format!("[{id}] has no supported formal interpretation, so the {obligation} cannot be established"), vec![at]),
    }
}

/// Asks, for each formula of `other`, whether the environment and `side`
/// hold without it. `Err` holds a witness: the side does not imply the
/// other. `Ok(None)` means that a question stayed open. Otherwise every
/// question is refuted: the side implies each formula of the other, and so
/// their conjunction. One refutation for each formula keeps each search
/// within one conjunct; a single refutation of the negated conjunction
/// would have to enumerate the cases of all of them at once.
fn implies(env: &Environment, side: &[usize], negated: &[usize]) -> Result<Option<Vec<Question>>, Question> {
    let mut refutations = Vec::new();
    let mut open = false;
    for &not in negated {
        let question = env.ask(&side.iter().copied().chain([not]).collect::<Vec<_>>());
        match question.status() {
            Status::Satisfiable => return Err(question),
            Status::Unknown => open = true,
            Status::Unsatisfiable => refutations.push(question),
        }
    }
    Ok((!open).then_some(refutations))
}

/// Decides an equivalence in an environment, over the unrolled formulas of
/// both sides: proved, refuted or unknown, or that the environment itself
/// has no interpretation and so proves nothing. The result holds the
/// certificates of its row. With it come the negations of the formulas of
/// the right side and of the left side.
pub(super) fn prove_equivalence(env: &Environment, left: &[usize], right: &[usize]) -> (CheckResult, Vec<usize>, Vec<usize>) {
    let (not_right, not_left) = (env.negations(right), env.negations(left));
    let environment = env.ask(&[]);
    match environment.status() {
        Status::Unsatisfiable => return (CheckResult::EnvironmentInconsistent { refutation: environment }, not_right, not_left),
        Status::Unknown => return (CheckResult::Unknown, not_right, not_left),
        Status::Satisfiable => {}
    }
    let result = match (implies(env, left, &not_right), implies(env, right, &not_left)) {
        (Err(witness), _) | (_, Err(witness)) => CheckResult::Refuted { witness },
        (Ok(Some(forward)), Ok(Some(backward))) => CheckResult::Proved { environment, forward, backward },
        _ => CheckResult::Unknown,
    };
    (result, not_right, not_left)
}

pub(super) fn run_checks(set: &SpecSet, model: &Model, inst: &Instance, bounds: Bounds, out: &mut Vec<Diagnostic>, claims: &mut Vec<CheckClaim>) -> Vec<CheckOutcome> {
    let mut outcomes = Vec::new();
    for check in set.packages.iter().flat_map(|p| &p.documents).flat_map(|d| &d.checks) {
        let at = SpecRef::point(&check.file, check.line, &check.name);
        let obligation = format!("check {}", check.name);
        let (left, right) = match (operand_formulas(set, model, &check.left), operand_formulas(set, model, &check.right)) {
            (Ok(left), Ok(right)) => (left, right),
            (Err(error), _) | (_, Err(error)) => {
                out.push(operand_diagnostic(&error, &obligation, at));
                continue;
            }
        };
        // The operands prove nothing about each other: only the background and
        // the selected definitions stand behind this question.
        let operands: Vec<Operand> = left.iter().chain(&right).map(|&i| Operand::of(&model.constraints[i])).collect();
        // A proof from the nearest axioms is a proof; a refutation counts only
        // with every axiom that reaches the operands.
        let mut claim = None;
        for steps in [1, 2, 4, usize::MAX] {
            let env = Environment::of(model, inst, bounds).using_definitions_within(&operands, steps);
            let started = std::time::Instant::now();
            let (left_parts, right_parts) = (env.conjuncts(&left), env.conjuncts(&right));
            let (result, not_right, not_left) = prove_equivalence(&env, &left_parts, &right_parts);
            if std::env::var("TRION_PROFILE").is_ok() {
                eprintln!("profile: check {} steps {steps}: {} premises, {}, {:.3}s", check.name, env.premises.len(), result.name(), started.elapsed().as_secs_f64());
            }
            let done = matches!(result, CheckResult::Proved { .. } | CheckResult::EnvironmentInconsistent { .. }) || env.complete;
            claim = Some(CheckClaim { environment: env.record(&check.name, "check"), left: left_parts, right: right_parts, not_right, not_left, result });
            if done {
                break;
            }
        }
        let Some(claim) = claim else { continue };
        let result = match &claim.result {
            CheckResult::Refuted { .. } => {
                out.push(Diagnostic::error("check-refuted", format!("the check {} is refuted: its two sides have different interpretations", check.name), vec![at]));
                "refuted"
            }
            CheckResult::EnvironmentInconsistent { .. } => {
                out.push(Diagnostic::error("check-environment-inconsistent", format!("the check {} is not proved: its selected definitions have no interpretation, so they would prove anything", check.name), vec![at]));
                "unknown"
            }
            CheckResult::Unknown => {
                out.push(Diagnostic::warning("check-unknown", format!("the check {} is neither proved nor refuted within the analysis bounds: it remains an unresolved obligation", check.name), vec![at]));
                "unknown"
            }
            CheckResult::Proved { .. } => "proved",
        };
        claims.push(claim);
        outcomes.push(CheckOutcome { name: check.name.clone(), relation: check.relation.clone(), result: result.to_string(), file: check.file.clone(), line: check.line });
    }
    outcomes
}

/// A comparison keeps operands apart and forces their conditions when it asks
/// about conflict: two rules with one trigger conflict when that trigger
/// occurs. The base and the candidate are contracts of the model, read over
/// the trace in the one environment given; a question the bounds leave open
/// makes the whole comparison unknown. The conditions of the base that are
/// forced join the premises of the claim.
pub(super) fn compare(env: &Environment, name: &str, base: &[usize], candidate: &[usize]) -> ComparisonClaim {
    let inst = env.instance;
    let guards = |items: &[usize]| items.iter().filter_map(|&i| inst.guard(i)).map(|g| g as usize).collect::<Vec<_>>();
    let formulas = |items: &[usize]| items.iter().map(|&i| inst.group(i)).collect::<Vec<_>>();
    let (base_formulas, candidate_formulas) = (formulas(base), formulas(candidate));
    let not_candidate = env.negations(&env.conjuncts(candidate));
    let mut env = env.clone();
    let claim = |env: &Environment, candidate_conditions: Vec<usize>, result: ComparisonResult| ComparisonClaim { environment: env.record(name, "comparison"), base: base_formulas.clone(), candidate: candidate_formulas.clone(), candidate_conditions, not_candidate: not_candidate.clone(), expected: None, result };
    // Conditions that cannot occur together, such as two values of one
    // attribute, are not forced: nothing happens under all of them.
    let conditions = guards(base);
    match env.status(&conditions) {
        Status::Unsatisfiable => {}
        Status::Unknown => return claim(&env, Vec::new(), ComparisonResult::Unknown),
        Status::Satisfiable => env.premises.extend(conditions),
    }
    let base_alone = env.ask(&base_formulas);
    match base_alone.status() {
        Status::Unsatisfiable => return claim(&env, Vec::new(), ComparisonResult::BaseInconsistent { refutation: base_alone }),
        Status::Unknown => return claim(&env, Vec::new(), ComparisonResult::Unknown),
        Status::Satisfiable => {}
    }
    let candidate_conditions = match env.status(&guards(candidate)) {
        Status::Unsatisfiable => Vec::new(),
        Status::Unknown => return claim(&env, Vec::new(), ComparisonResult::Unknown),
        Status::Satisfiable => guards(candidate),
    };
    let together = env.ask(&base_formulas.iter().chain(&candidate_formulas).chain(&candidate_conditions).copied().collect::<Vec<_>>());
    match together.status() {
        Status::Unsatisfiable => return claim(&env, candidate_conditions, ComparisonResult::Conflict { base: base_alone, refutation: together }),
        Status::Unknown => return claim(&env, candidate_conditions, ComparisonResult::Unknown),
        Status::Satisfiable => {}
    }
    let result = match implies(&env, &base_formulas, &not_candidate) {
        Ok(Some(refutations)) => ComparisonResult::Redundant { base: base_alone, refutations },
        Err(without) => ComparisonResult::Extension { with: together, without },
        Ok(None) => ComparisonResult::Unknown,
    };
    claim(&env, candidate_conditions, result)
}

fn normalized_expect(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

/// The claims of the examples that the solver decides.
#[derive(Default)]
pub(super) struct ExampleClaims {
    pub(super) comparisons: Vec<ComparisonClaim>,
    pub(super) consistency: Vec<ExampleClaim>,
}

fn run_example(set: &SpecSet, doc: &Document, pkg: &Package, engine: Option<(&Model, &Instance)>, bounds: Bounds, example: &trion_language::document::Example, claims: &mut ExampleClaims, shared: &ExampleContext) -> Result<String, Diagnostic> {
    let at = || SpecRef::point(&example.file, example.line, &example.name);
    let invalid = |message: String| Diagnostic::error("example-invalid", format!("the example {} cannot run: {message}", example.name), vec![at()]);
    let input = example.input.as_deref().unwrap_or_default();
    match example.kind.as_str() {
        "syntax" => {
            let diags = match example.form.as_deref() {
                Some("fragment") => parse_document(input, "<example>").1,
                Some("statement") => parse_statement(input).1,
                other => return Err(invalid(format!("the form {other:?} is not `statement` or `fragment`"))),
            };
            let errors: Vec<&Diagnostic> = diags.iter().filter(|d| d.severity == Severity::Error).collect();
            Ok(match errors.first() {
                None => "accepted".to_string(),
                Some(first) => format!("rejected \"{}\"", first.code),
            })
        }
        "consistency" => {
            let (mut parsed, diags) = parse_statement(input);
            if let Some(error) = diags.iter().find(|d| d.severity == Severity::Error) {
                return Err(invalid(format!("the input does not parse: {}", error.message)));
            }
            parsed.namespace = doc.namespace.clone();
            parsed.imports = doc.imports.clone();
            // The input is read with the declarations and with the
            // definitions of the terms that it names, as a statement is
            // read alone.
            let isolated = shared.isolation.set_naming(&pkg.name, vec![parsed], input);
            let lex = Lexicon::of(&isolated);
            let mini = trion_language::reading::compile(&isolated, &lex, bounds.scope);
            // The example is decided as the package is: over its own unrolled
            // formulas, by the rows of the status.
            let (trace, _) = trace_of(&isolated, &mini, &lex, bounds.trace_length);
            let (own, standing) = encode(&trace, &mini, bounds);
            let authored = Authored::new(&isolated, &lex);
            let found = conflicts::search(&mini, &own, &standing, &authored, &mut Vec::new());
            let hard: Vec<(usize, usize)> = (0..mini.constraints.len()).filter(|&i| !authored.is_recommendation(&mini.constraints[i])).map(|i| (i, own.group(i))).collect();
            let status = proof::status_outcome(&own, own.background(), &hard);
            // A satisfiable example is consistent only when its statements
            // can be kept under each condition and in each situation.
            let satisfiable = status.status() == Status::Satisfiable;
            let conditions = if satisfiable { proof::conditions(&own, &background_of(&mini, &own), &members_of(&entries_of(&mini, &own, &authored)), &[]) } else { Vec::new() };
            let situations = found.situations.as_ref().filter(|_| satisfiable).and_then(|s| s.questions(&own)).unwrap_or_default();
            claims.consistency.push(ExampleClaim { name: example.name.clone(), expected: example.expect.clone(), bounds: used_bounds(&mini, bounds), pool: std::sync::Arc::new(own.formulas()), background: own.background().to_vec(), hard: hard.iter().map(|(_, f)| *f).collect(), status, conditions, situations });
            Ok(found.verdict().to_string())
        }
        // A reading example compares what the reader makes of its input
        // with an entry that a person wrote: the contract, the temporal
        // shape and the background axioms.
        "reading" => {
            let (mut parsed, diags) = parse_statement(input);
            if let Some(error) = diags.iter().find(|d| d.severity == Severity::Error) {
                return Err(invalid(format!("the input does not parse: {}", error.message)));
            }
            parsed.namespace = doc.namespace.clone();
            parsed.imports = doc.imports.clone();
            let ids: BTreeSet<String> = parsed.specs.iter().map(|s| s.display_id()).collect();
            // The input and the baseline are read with the same definitions:
            // those of the terms that the input names.
            let compile = |documents: Vec<Document>| shared.isolation.compile_naming(&pkg.name, documents, input);
            let baseline = compile(Vec::new());
            let mini = compile(vec![parsed]);
            // `form unrolled`: the formulas of the input over a trace of two
            // moments and the rest, which is what the solver decides.
            if example.form.as_deref() == Some("unrolled") {
                return Ok(unrolled_lines(&mini, &baseline, &ids, 2).join("\n"));
            }
            let mut lines = trion_language::reading::entry_lines(&mini, &baseline, &ids);
            // `form contract`: the assumption and the guarantee of each
            // statement of the input, without its temporal shape and its axioms.
            if example.form.as_deref() == Some("contract") {
                lines.retain(|line| line.starts_with("assume: ") || line.starts_with("guarantee: "));
            }
            Ok(lines.join("\n"))
        }
        "comparison" => {
            let (model, inst) = engine.expect("a comparison is decided in the environment of the package");
            let obligation = format!("comparison {}", example.name);
            let (base, candidate) = match (operand_formulas(set, model, &example.base), operand_formulas(set, model, &example.candidate)) {
                (Ok(base), Ok(candidate)) => (base, candidate),
                (Err(OperandError::Unresolved), _) | (_, Err(OperandError::Unresolved)) => return Err(invalid("the comparison names a statement that does not exist".to_string())),
                (Err(error), _) | (_, Err(error)) => return Err(operand_diagnostic(&error, &obligation, at())),
            };
            // One environment and one set of bounds serve the base and the candidate.
            let operands: Vec<Operand> = base.iter().chain(&candidate).map(|&i| Operand::of(&model.constraints[i])).collect();
            let env = Environment::of(model, inst, bounds).using_definitions(&operands);
            let mut claim = compare(&env, &example.name, &base, &candidate);
            claim.expected = Some(example.expect.clone());
            let observed = claim.result.name().to_string();
            claims.comparisons.push(claim);
            Ok(observed)
        }
        other => Err(invalid(format!("the kind `{other}` is not known"))),
    }
}

/// What every example of a set is read with.
struct ExampleContext {
    isolation: Isolation,
}

pub(super) fn run_examples(set: &SpecSet, model: &Model, inst: &Instance, bounds: Bounds, out: &mut Vec<Diagnostic>, claims: &mut ExampleClaims) -> Vec<ExampleOutcome> {
    let mut outcomes = Vec::new();
    let work: Vec<(&Package, &Document, &trion_language::document::Example)> = set.packages.iter().flat_map(|pkg| pkg.documents.iter().flat_map(move |doc| doc.examples.iter().map(move |example| (pkg, doc, example)))).collect();
    let baselines = ExampleContext { isolation: Isolation::of(set, bounds.scope) };
    // The examples are independent of each other: they run side by side, and
    // their results are gathered in the order of the package.
    let next = std::sync::atomic::AtomicUsize::new(0);
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get()).min(8).min(work.len().max(1));
    let mut results: Vec<Option<(Result<String, Diagnostic>, ExampleClaims)>> = Vec::new();
    results.resize_with(work.len(), || None);
    let results = std::sync::Mutex::new(results);
    // A comparison is decided in the environment of the package, which one
    // thread holds; every other example compiles its own input.
    let alone = |example: &trion_language::document::Example| example.kind != "comparison";
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| loop {
                let index = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some((pkg, doc, example)) = work.get(index) else { break };
                if !alone(example) {
                    continue;
                }
                let mut own = ExampleClaims::default();
                let observed = run_example(set, doc, pkg, None, bounds, example, &mut own, &baselines);
                results.lock().unwrap()[index] = Some((observed, own));
            });
        }
    });
    let mut results = results.into_inner().unwrap();
    for (index, (pkg, doc, example)) in work.iter().enumerate() {
        if !alone(example) {
            let mut own = ExampleClaims::default();
            let observed = run_example(set, doc, pkg, Some((model, inst)), bounds, example, &mut own, &baselines);
            results[index] = Some((observed, own));
        }
    }
    for ((_, _, example), result) in work.iter().zip(results) {
        let at = SpecRef::point(&example.file, example.line, &example.name);
        let (observed, mut own) = result.expect("every example was run");
        claims.comparisons.append(&mut own.comparisons);
        claims.consistency.append(&mut own.consistency);
        let observed = match observed {
            Ok(observed) => observed,
            Err(diagnostic) => {
                out.push(diagnostic);
                continue;
            }
        };
        // An unknown result satisfies no expectation: it is a result
        // of the analysis, never a property an example can expect.
        if observed == "unknown" || normalized_expect(&observed) != normalized_expect(&example.expect) {
            out.push(Diagnostic::error("example-failed", format!("the example {} expected {} and observed {observed}", example.name, example.expect), vec![at]));
        }
        outcomes.push(ExampleOutcome { name: example.name.clone(), kind: example.kind.clone(), expected: example.expect.clone(), observed, file: example.file.clone(), line: example.line });
    }
    outcomes
}

#[cfg(test)]
mod tests {
    use super::*;
    use trion_solver::Atom;

    fn event(key: &str) -> Formula {
        Formula::Atom(Atom::Event { key: key.to_string() })
    }

    #[test]
    fn an_inconsistent_environment_proves_no_equivalence() {
        let model = Model::default();
        // The formulas of a question are formulas of the instance that the environment reads.
        let instance = Instance::new(&[], &[], None);
        let (a, b) = (instance.add(&event("a")), instance.add(&event("b")));
        let verdict = |env: &Environment, left: usize, right: usize| prove_equivalence(env, &[left], &[right]).0.name();
        // In a consistent environment the two different sides are refuted.
        let env = Environment::of(&model, &instance, Bounds::default());
        assert_eq!(verdict(&env, a, b), "refuted");
        assert_eq!(verdict(&env, a, a), "proved");
        // Premises without an interpretation would entail both directions; the
        // equivalence is still not reported as proved.
        let mut broken = Environment::of(&model, &instance, Bounds::default());
        broken.premises = vec![instance.add(&event("p")), instance.add(&Formula::not(event("p")))];
        assert_eq!(verdict(&broken, a, b), "environment-inconsistent");
        assert_eq!(verdict(&broken, a, a), "environment-inconsistent");
    }

    #[test]
    fn an_equivalence_that_needs_more_than_the_bounds_is_unknown() {
        let model = Model::default();
        let both = |x: &str, y: &str| Formula::Or(vec![Formula::And(vec![event(x), event(y)]), Formula::And(vec![Formula::not(event(x)), Formula::not(event(y))])]);
        // `a` exactly when `b`, written in both orders: no side follows by propagation alone.
        let (a, b) = (both("a", "b"), both("b", "a"));
        let verdict = |bounds: Bounds| {
            let instance = Instance::new(&[], &[], bounds.decisions);
            let (left, right) = (instance.add(&a), instance.add(&b));
            prove_equivalence(&Environment::of(&model, &instance, bounds), &[left], &[right]).0.name()
        };
        assert_eq!(verdict(Bounds::default()), "proved");
        assert_eq!(verdict(Bounds { decisions: Some(0), ..Bounds::default() }), "unknown");
    }
}
