//! What a statement expands to: the controlled English that its inherited
//! conditions, its variables and its diagram stand for, and the diagrams that
//! restate it.

use crate::document::Spec;
use crate::syntax::ast::*;
use serde::Serialize;

fn frames_text(frames: &Frames) -> String {
    frames.render().join(" ")
}

/// The steps of a flow in order, when the flow is one path without choices.
fn linear_path(flow: &Flow) -> Option<Vec<&FlowStep>> {
    if !flow.choices.is_empty() {
        return None;
    }
    let mut path = Vec::new();
    let mut current = flow.start.as_str();
    loop {
        path.push(flow.steps.iter().find(|s| s.name == current)?);
        let next: Vec<&String> = flow.edges.iter().filter(|(from, _)| from == current).map(|(_, to)| to).collect();
        match next.as_slice() {
            [] => break,
            [one] if path.len() <= flow.steps.len() => current = one,
            _ => return None,
        }
    }
    (path.len() == flow.steps.len()).then_some(path)
}

/// A flow without choices reads as an ordered action list; a flow with
/// choices keeps its notation, which already is the authored English.
fn lower_flows(node: &CompNode) -> CompNode {
    match node {
        CompNode::Flow(flow) => match linear_path(flow) {
            Some(path) => CompNode::Sequence { items: path.iter().map(|s| lower_flows(&s.node)).collect() },
            None => node.clone(),
        },
        CompNode::All { items } => CompNode::All { items: items.iter().map(lower_flows).collect() },
        CompNode::Some { items } => CompNode::Some { items: items.iter().map(lower_flows).collect() },
        CompNode::One { items } => CompNode::One { items: items.iter().map(lower_flows).collect() },
        CompNode::Sequence { items } => CompNode::Sequence { items: items.iter().map(lower_flows).collect() },
        CompNode::Leaf { .. } => node.clone(),
    }
}

/// The sentence as the reader formalizes it: a flow without choices is the
/// ordered action list that it expands to, so the diagram and its controlled
/// English have one model.
pub(crate) fn lowered(sentence: &Sentence) -> Sentence {
    let mut out = sentence.clone();
    if let Core::Deontic { vp: VpGroup::Composite(composition), .. } = &mut out.core {
        composition.root = lower_flows(&composition.root);
    }
    out
}

/// The sentences that the reader formalizes for a statement: the statement
/// itself, with each flow without choices lowered to the ordered action
/// list that it expands to.
pub(crate) fn formalized(spec: &Spec) -> Vec<Sentence> {
    vec![lowered(&spec.sentence)]
}

/// Where a generated expression came from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Origin {
    /// `statement`, `head`, `node`, `label`, `edge`, `step`, `start`, `finish`, `guard` or `otherwise`.
    pub kind: String,
    pub name: String,
    pub id: Option<String>,
    pub file: String,
    pub line: usize,
    pub text: String,
}

/// One controlled English expression of an expansion, with the authored
/// elements and the enclosing scopes that it was generated from.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct Expression {
    pub text: String,
    pub origins: Vec<Origin>,
    pub scopes: Vec<String>,
}

fn third_person(verb: &str) -> String {
    if verb == "have" {
        return "has".to_string();
    }
    if let Some(stem) = verb.strip_suffix('y').filter(|stem| !stem.ends_with(['a', 'e', 'i', 'o', 'u'])) {
        return format!("{stem}ies");
    }
    if ["s", "x", "z", "ch", "sh", "o"].iter().any(|e| verb.ends_with(e)) {
        return format!("{verb}es");
    }
    format!("{verb}s")
}

fn is_plural(group: &NpGroup) -> bool {
    match group {
        NpGroup::Single(np) => np.head.len() > 1 && np.head.ends_with('s') && !["ss", "us", "is"].iter().any(|e| np.head.ends_with(e)),
        NpGroup::Coordinated { conj, .. } => *conj == Conj::And,
    }
}

/// The complement of a guard: `is valid` becomes `is not valid`, and
/// `passes` becomes `does not pass`.
fn negated_clause(clause: &Clause) -> Clause {
    let mut out = clause.clone();
    match &mut out.body {
        ClauseBody::Copular { predicate, .. } => {
            let mut words: Vec<String> = match &*predicate {
                Predicate::Words { words, .. } => words.clone(),
                other => other.clone().render().split_whitespace().map(str::to_string).collect(),
            };
            if words.first().is_some_and(|w| w == "not") {
                words.remove(0);
            } else {
                words.insert(0, "not".to_string());
            }
            *predicate = Predicate::Words { words, nominal: None };
        }
        ClauseBody::Verbal { verb, negation, .. } => {
            if negation.take().is_some() {
                if !is_plural(&clause.subject) {
                    *verb = third_person(verb);
                }
            } else {
                *negation = Some(if is_plural(&clause.subject) { "do not" } else { "does not" }.to_string());
                *verb = crate::syntax::words::base_verb(verb);
            }
        }
    }
    out
}

fn negated_group(group: &ClauseGroup) -> ClauseGroup {
    let conj = match group.conj {
        Some(Conj::And) => Some(Conj::Or),
        Some(Conj::Or) => Some(Conj::And),
        None => None,
    };
    ClauseGroup { conj, items: group.items.iter().map(negated_clause).collect() }
}

/// The sentences of a flow with choices: one for each step on each path, under
/// the guards of that path and after the step before it.
fn choice_sentences(spec: &Spec, flow: &Flow, composition: &Composition) -> Option<Vec<(String, Vec<(&'static str, String)>)>> {
    let Core::Deontic { subject, modal, negated, .. } = &spec.sentence.core else { return None };
    let leaf = |name: &str| -> Option<(&Vp, Option<&Clause>)> {
        match &flow.steps.iter().find(|s| s.name == name)?.node {
            CompNode::Leaf { index, exception } => Some((composition.leaves.get(*index)?, exception.as_ref())),
            _ => None,
        }
    };
    let mut out: Vec<(String, Vec<(&'static str, String)>)> = Vec::new();
    // (step, guards of the path, the step before, the elements that led here)
    // The last part holds the guards that the whole path has passed.
    type Led = Vec<(&'static str, String)>;
    let mut stack: Vec<(String, Vec<ClauseGroup>, Option<String>, Led, Led)> = vec![(flow.start.clone(), vec![], None, vec![("start", flow.start.clone())], vec![])];
    let mut visits = 0;
    while let Some((name, guards, before, mut origins, passed)) = stack.pop() {
        visits += 1;
        if visits > 4096 {
            return None;
        }
        let (vp, exception) = leaf(&name)?;
        let mut frames = spec.sentence.frames.clone();
        frames.states.extend(guards.iter().map(|guard| Frame { keyword: "While".to_string(), clause: guard.clone() }));
        let after = match before.as_deref().and_then(leaf) {
            Some((previous, _)) if previous.verb != "be" && previous.complement.is_none() => {
                let verb = if is_plural(subject) { previous.verb.clone() } else { third_person(&previous.verb) };
                let clause = Clause { subject: subject.clone(), body: ClauseBody::Verbal { verb, particle: previous.particle.clone(), manner: previous.manner.clone(), object: previous.object.clone(), roles: previous.roles.clone(), content: previous.content.clone(), negation: None } };
                format!(" after {}", clause.render())
            }
            _ => String::new(),
        };
        let unless = exception.map(|c| format!(", unless {}", c.render())).unwrap_or_default();
        let not = if *negated { " not" } else { "" };
        let mut head = frames_text(&frames);
        for keyword in ["Where", "While", "When", "If"] {
            head = head.replace(&format!(", {keyword} "), &format!(", {} ", keyword.to_lowercase()));
        }
        let body = format!("{} {}{not} {}{after}{unless}.", subject.render(), modal.as_str(), vp.render());
        let text = capitalized(if head.is_empty() { body } else { format!("{head} {body}") });
        for led in &passed {
            if !origins.contains(led) {
                origins.push(led.clone());
            }
        }
        origins.push(("step", name.clone()));
        if flow.finish.contains(&name) {
            origins.push(("finish", name.clone()));
        }
        if !out.iter().any(|(known, _)| *known == text) {
            out.push((text, origins));
        }
        let mut next: Vec<(String, Vec<ClauseGroup>, Option<String>, Led, Led)> = Vec::new();
        for (_, to) in flow.edges.iter().filter(|(from, _)| *from == name) {
            next.push((to.clone(), guards.clone(), Some(name.clone()), vec![("edge", format!("{name} -> {to}"))], passed.clone()));
        }
        for choice in flow.choices.iter().filter(|c| c.after == name) {
            for (guard, to) in &choice.arms {
                let mut path = guards.clone();
                path.push(guard.clone());
                let led: Led = vec![("guard", format!("{name} -> {to}"))];
                let mut through = passed.clone();
                through.extend(led.clone());
                next.push((to.clone(), path, Some(name.clone()), led, through));
            }
            if let Some(to) = &choice.otherwise {
                let mut path = guards.clone();
                path.extend(choice.arms.iter().map(|(guard, _)| negated_group(guard)));
                let mut led: Led = vec![("otherwise", format!("{name} -> {to}"))];
                led.extend(choice.arms.iter().map(|(_, target)| ("guard", format!("{name} -> {target}"))));
                let mut through = passed.clone();
                through.extend(led.clone());
                next.push((to.clone(), path, Some(name.clone()), led, through));
            }
        }
        // Depth first, in the written order.
        stack.extend(next.into_iter().rev());
    }
    // A sentence that the parser would not read back is no expansion.
    out.iter().all(|(text, _)| crate::document::parse_sentence(text).is_ok()).then_some(out)
}

fn top_flow(spec: &Spec) -> Option<(&Flow, &Composition)> {
    match &spec.sentence.core {
        Core::Deontic { vp: VpGroup::Composite(composition), .. } => match &composition.root {
            CompNode::Flow(flow) => Some((flow, composition)),
            _ => None,
        },
        _ => None,
    }
}

/// The controlled English expressions that a statement expands to, each with
/// the nodes, edges, labels, steps and guards it came from and with the
/// scopes around them.
pub fn expressions(spec: &Spec) -> Vec<Expression> {
    let mut found = expressions_marked(spec);
    for expression in &mut found {
        expression.text = crate::document::without_binding_marks(&expression.text);
    }
    found
}

fn expressions_marked(spec: &Spec) -> Vec<Expression> {
    let origin = |kind: &str, name: &str| -> Option<Origin> {
        let element = spec.elements.iter().find(|e| e.kind == kind && e.name == name)?;
        Some(Origin { kind: element.kind.clone(), name: element.name.clone(), id: element.id.clone(), file: spec.file.clone(), line: element.line, text: element.text.clone() })
    };
    let all = || spec.elements.iter().map(|e| Origin { kind: e.kind.clone(), name: e.name.clone(), id: e.id.clone(), file: spec.file.clone(), line: e.line, text: e.text.clone() }).collect::<Vec<_>>();
    let statement = |kind: &str| Origin { kind: kind.to_string(), name: spec.display_id(), id: spec.id.clone(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
    if let Some((flow, composition)) = top_flow(spec) {
        if !flow.choices.is_empty() {
            if let Some(sentences) = choice_sentences(spec, flow, composition) {
                return sentences
                    .into_iter()
                    .map(|(text, led)| {
                        let mut origins = vec![statement("head")];
                        origins.extend(led.iter().filter_map(|(kind, name)| origin(kind, name)));
                        Expression { text, origins, scopes: spec.scopes.clone() }
                    })
                    .collect();
            }
        }
        let mut origins = vec![statement("head")];
        origins.extend(all());
        return vec![Expression { text: expand_whole(spec), origins, scopes: spec.scopes.clone() }];
    }
    let origins = if spec.elements.is_empty() { vec![statement("statement")] } else { all() };
    vec![Expression { text: expand_whole(spec), origins, scopes: spec.scopes.clone() }]
}

/// A relation statement read as an edge of a concept diagram.
#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct ConceptEdge {
    pub id: Option<String>,
    pub from: String,
    pub relation: String,
    pub to: String,
    pub file: String,
    pub line: usize,
}

/// The concept edge that says exactly what a universal relation statement
/// says: `Each order has exactly one buyer.` is `each order -> has -> exactly
/// one buyer;`. A statement that an edge cannot restate has no edge.
pub fn concept_edge(spec: &Spec) -> Option<ConceptEdge> {
    let s = &spec.sentence;
    let plain = s.frames.scopes.is_empty() && s.frames.states.is_empty() && s.frames.trigger.is_none() && s.exception.is_none() && s.purpose.is_none() && s.necessary.is_none() && s.iff.is_none();
    let Core::Relation { subject: NpGroup::Single(np), vp: VpGroup::Single(vp) } = &s.core else { return None };
    if !plain || !matches!(np.det, Some(Det::Each)) || spec.otherwise {
        return None;
    }
    let from = np.render();
    let whole = vp.render();
    let relation = match &vp.particle {
        Some(particle) => format!("{} {particle}", vp.verb),
        None => vp.verb.clone(),
    };
    let to = whole.strip_prefix(&relation)?.trim().to_string();
    if to.is_empty() || to.contains("->") || to.contains(';') {
        return None;
    }
    // The edge is kept only when its sentence is the statement again.
    let text = capitalized(format!("{from} {relation} {to}."));
    let again = crate::document::parse_sentence(&text).ok()?;
    (again.core == s.core).then(|| ConceptEdge { id: spec.id.clone(), from, relation, to, file: spec.file.clone(), line: spec.line })
}

/// A concept diagram that restates the given relation statements.
pub fn concept_notation(id: Option<&str>, edges: &[ConceptEdge]) -> String {
    let mut out = match id {
        Some(id) => format!("[{id}] concept:\n"),
        None => "concept:\n".to_string(),
    };
    for edge in edges {
        let label = edge.id.as_ref().map(|id| format!("[{id}] ")).unwrap_or_default();
        out.push_str(&format!("    {label}{} -> {} -> {};\n", edge.from, edge.relation, edge.to));
    }
    out
}

/// The steps of an ordered action list, when a flow can restate the statement.
pub fn flow_steps(spec: &Spec) -> Option<Vec<String>> {
    let Core::Deontic { vp: VpGroup::Composite(composition), .. } = &spec.sentence.core else { return None };
    let CompNode::Sequence { items } = &composition.root else { return None };
    spec.sentence.frames.trigger.as_ref()?;
    items
        .iter()
        .map(|item| match item {
            CompNode::Leaf { index, exception: None } => Some(crate::document::with_variables(&composition.leaves.get(*index)?.render())),
            _ => None,
        })
        .collect()
}

/// A flow diagram that restates an ordered action list: one step for each
/// action and one edge from each action to the next.
pub fn flow_notation(spec: &Spec) -> Option<String> {
    let steps = flow_steps(spec)?;
    let Core::Deontic { subject, modal, negated, .. } = &spec.sentence.core else { return None };
    let not = if *negated { " not" } else { "" };
    let head = capitalized(format!("{} {} {}{not} follow this flow:", frames_text(&spec.sentence.frames), subject.render(), modal.as_str()));
    let mut out = match &spec.id {
        Some(id) => format!("[{id}] {head}\n"),
        None => format!("{head}\n"),
    };
    for (i, action) in steps.iter().enumerate() {
        out.push_str(&format!("    step s{}: {action};\n", i + 1));
    }
    out.push_str("    start s1\n");
    for i in 1..steps.len() {
        out.push_str(&format!("    s{i} -> s{}\n", i + 1));
    }
    out.push_str(&format!("    finish s{}\n", steps.len()));
    Some(out)
}

fn capitalized(text: String) -> String {
    let mut chars = text.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().chain(chars).collect(),
        None => text,
    }
}

/// The statement with its inherited conditions written out and its variables
/// replaced. A concept edge expands to its generated sentence, and a flow
/// without choices to an ordered action list.
pub fn expand(spec: &Spec) -> String {
    crate::document::without_binding_marks(&expand_marked(spec))
}

/// The expansion with the mark of each bound variable left in place: the
/// form that is read again without the statement around it.
pub fn expand_with_marks(spec: &Spec) -> String {
    // A flow with choices keeps its notation, which is its controlled
    // English: the sentences of its paths are a view of it and say nothing
    // of its occurrences and of the sampling of its guards.
    if top_flow(spec).is_some_and(|(flow, _)| !flow.choices.is_empty()) {
        return spec.sentence.source.clone();
    }
    expand_whole(spec)
}

fn expand_marked(spec: &Spec) -> String {
    // A flow with choices reads as one sentence for each step on each path.
    if top_flow(spec).is_some_and(|(flow, _)| !flow.choices.is_empty()) {
        let found = expressions_marked(spec);
        if found.len() > 1 || found.first().is_some_and(|e| e.origins.iter().any(|o| o.kind == "step") && !e.text.contains("follow this flow")) {
            return found.into_iter().map(|e| e.text).collect::<Vec<_>>().join("\n");
        }
    }
    expand_whole(spec)
}

fn expand_whole(spec: &Spec) -> String {
    if let Some(expansion) = &spec.expansion {
        if !spec.scopes.is_empty() || spec.abbreviates.is_some() {
            return capitalized(spec.sentence.render());
        }
        return capitalized(expansion.clone());
    }
    let s = &spec.sentence;
    // The canonical rendering of a sentence that inherits nothing and binds
    // nothing must read again: where it does not, the sentence as written
    // is its own expansion.
    let composite = matches!(&s.core, Core::Deontic { vp: VpGroup::Composite(_), .. });
    if !composite && spec.scopes.is_empty() && spec.elements.is_empty() && spec.diagram.is_none() && !crate::document::has_binding_mark(&s.render()) {
        let rendered = capitalized(s.render());
        let (parsed, diags) = crate::document::parse_statement(&rendered);
        let read_again = !diags.iter().any(|d| d.severity == crate::diagnostic::Severity::Error) && parsed.specs.len() == 1 && {
            let mut again = parsed.specs[0].sentence.clone();
            again.source = s.source.clone();
            again == *s
        };
        return if read_again { rendered } else { s.source.split_whitespace().collect::<Vec<_>>().join(" ") };
    }
    if let Core::Deontic { vp: VpGroup::Composite(composition), .. } = &s.core {
        let lowered = Composition { root: lower_flows(&composition.root), leaves: composition.leaves.clone() };
        let mut sentence = s.clone();
        if let Core::Deontic { vp, .. } = &mut sentence.core {
            *vp = VpGroup::Composite(Box::new(lowered));
        }
        let frames = frames_text(&sentence.frames);
        let body = sentence.core.render();
        return capitalized(if frames.is_empty() { body } else { format!("{frames} {body}") });
    }
    capitalized(s.render())
}
