//! The `example` blocks of a set that demonstrate the conversion, and what
//! the obligations of the `check` blocks and of the comparisons are stated
//! with: the environment of a question and the contracts that it names.

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
    /// a proof obligation and no axiom: the details are not assumed to say
    /// what the statement says, so it is no premise.
    fn premise_of(&self, axiom: usize) -> usize {
        let c = &self.model.constraints[axiom];
        if c.kind == ConstraintKind::Refinement {
            return self.instance.add(&Formula::True);
        }
        self.instance.group(axiom)
    }

    /// The numbers of the formulas of a question in this environment.
    pub(super) fn query(&self, formulas: &[usize]) -> Vec<usize> {
        self.instance.background().iter().chain(&self.premises).chain(formulas).copied().collect()
    }
}

fn constraints_of(model: &Model, id: &str) -> Vec<usize> {
    let nested = format!("{id}/");
    (0..model.constraints.len()).filter(|&i| matches!(model.constraints[i].kind, ConstraintKind::Spec | ConstraintKind::Permission) && model.constraints[i].refs.first().is_some_and(|r| r.id == id || r.id.starts_with(&nested))).collect()
}

/// Why the operands of a question have no formulas.
pub(super) enum OperandError {
    /// No statement has the identifier.
    Unresolved,
    /// The statement is accepted and has no formal interpretation.
    Unsupported(String),
}

/// The contracts of the named statements, by their index in the model.
pub(super) fn operand_formulas(set: &SpecSet, model: &Model, ids: &[String]) -> Result<Vec<usize>, OperandError> {
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
pub(super) fn operand_diagnostic(error: &OperandError, obligation: &str, at: SpecRef) -> Diagnostic {
    match error {
        OperandError::Unresolved => Diagnostic::error("UNRESOLVED_REFERENCE", format!("the {obligation} names a statement that does not exist"), vec![at]),
        OperandError::Unsupported(id) => Diagnostic::error("UNSUPPORTED_SEMANTICS", format!("[{id}] has no supported formal interpretation, so the {obligation} cannot be established"), vec![at]),
    }
}

fn normalized_expect(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

fn run_example(doc: &Document, pkg: &Package, example: &trion_language::document::Example, shared: &ExampleContext) -> Result<String, Diagnostic> {
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
            let specs = parsed.specs.clone();
            let mini = compile(vec![parsed]);
            // The pattern of the example holds the two rules: each simple
            // sentence is exactly one contract, and each sentence of the
            // expansion of a composite sentence, read alone from its own
            // text, is the contract that the composite sentence has for it.
            for spec in specs.iter().filter(|spec| !matches!(spec.sentence.core, trion_language::syntax::ast::Core::Definition { .. })) {
                let id = spec.display_id();
                let count = super::properties::contracts_of(&mini, &id) + usize::from(super::properties::fault("one-contract"));
                if count != 1 {
                    return Err(Diagnostic::error("sentence-not-one-contract", format!("the example {} reads the simple sentence `{}` as {count} contracts, and a simple sentence is exactly one", example.name, spec.sentence.source), vec![at()]));
                }
                if spec.abbreviates.is_some() {
                    let (alone, diags) = parse_statement(&spec.sentence.source);
                    let reread = alone.specs.first().filter(|_| diags.iter().all(|d| d.severity != Severity::Error)).cloned();
                    let here = reread.map(|mut reread| {
                        if super::properties::fault("expansion") {
                            return vec!["seeded: a contract that only the composite sentence has".to_string()];
                        }
                        reread.id = spec.id.clone();
                        reread.abbreviates = spec.abbreviates.clone();
                        let mut document = Document { namespace: doc.namespace.clone(), imports: doc.imports.clone(), file: doc.file.clone(), application_mapping: doc.application_mapping.clone(), ..Document::default() };
                        document.specs.push(reread);
                        super::local_reading(&compile(vec![document]), &id)
                    });
                    if here.as_ref() != Some(&super::local_reading(&mini, &id)) {
                        return Err(Diagnostic::error("composite-not-its-expansion", format!("the example {}: `{}`, read alone, is not what the composite sentence says of it", example.name, spec.sentence.source), vec![at()]));
                    }
                }
            }
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
        other => Err(invalid(format!("the kind `{other}` is not known"))),
    }
}

/// Each example of consistency of a set, with its input read alone: the
/// set of the input with the declarations of its package and the
/// definitions of the terms that it names, its lexicon and its model.
pub(super) fn consistency_examples(set: &SpecSet, scope: usize) -> Vec<(&trion_language::document::Example, Result<(SpecSet, Lexicon, Model), String>)> {
    let isolation = Isolation::of(set, scope);
    let mut out = Vec::new();
    for pkg in &set.packages {
        for doc in &pkg.documents {
            for example in doc.examples.iter().filter(|e| e.kind == "consistency") {
                let input = example.input.as_deref().unwrap_or_default();
                let (mut parsed, diags) = parse_statement(input);
                if let Some(error) = diags.iter().find(|d| d.severity == Severity::Error) {
                    out.push((example, Err(format!("the input does not parse: {}", error.message))));
                    continue;
                }
                parsed.namespace = doc.namespace.clone();
                parsed.imports = doc.imports.clone();
                let mut isolated = isolation.set_naming(&pkg.name, vec![parsed], input);
                // The input is a document of its own: which of its actors are
                // the system is read from its statements, not from the
                // boundary of the package that holds the example.
                for doc in isolated.packages.iter_mut().flat_map(|p| p.documents.iter_mut()) {
                    doc.controls.clear();
                }
                let lex = Lexicon::of(&isolated);
                let mini = trion_language::reading::compile(&isolated, &lex, scope);
                out.push((example, Ok((isolated, lex, mini))));
            }
        }
    }
    out
}

/// What every example of a set is read with.
struct ExampleContext {
    isolation: Isolation,
}

/// The examples of the kinds that `kinds` accepts: of syntax and of a
/// reading, which demonstrate the conversion and decide nothing.
pub(super) fn run_examples_of(set: &SpecSet, bounds: Bounds, kinds: &(dyn Fn(&str) -> bool + Sync), out: &mut Vec<Diagnostic>) -> Vec<ExampleOutcome> {
    let mut outcomes = Vec::new();
    let work: Vec<(&Package, &Document, &trion_language::document::Example)> = set.packages.iter().flat_map(|pkg| pkg.documents.iter().flat_map(move |doc| doc.examples.iter().filter(|example| kinds(&example.kind)).map(move |example| (pkg, doc, example)))).collect();
    let baselines = ExampleContext { isolation: Isolation::of(set, bounds.scope) };
    // The examples are independent of each other: they run side by side, and
    // their results are gathered in the order of the package.
    let next = std::sync::atomic::AtomicUsize::new(0);
    let threads = std::thread::available_parallelism().map_or(1, |n| n.get()).min(8).min(work.len().max(1));
    let mut results: Vec<Option<Result<String, Diagnostic>>> = Vec::new();
    results.resize_with(work.len(), || None);
    let results = std::sync::Mutex::new(results);
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| loop {
                let index = next.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
                let Some((pkg, doc, example)) = work.get(index) else { break };
                let observed = run_example(doc, pkg, example, &baselines);
                results.lock().unwrap()[index] = Some(observed);
            });
        }
    });
    let results = results.into_inner().unwrap();
    for ((_, _, example), result) in work.iter().zip(results) {
        let at = SpecRef::point(&example.file, example.line, &example.name);
        let observed = result.expect("every example was run");
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

