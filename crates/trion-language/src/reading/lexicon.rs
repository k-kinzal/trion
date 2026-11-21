//! Names: how the words of a statement resolve to the terms of a set.
//!
//! A [`Lexicon`] is read from the declarations of a set: its aliases, the
//! words of its declared names, its verbs and the terms that each namespace
//! declares. Every key of the model passes through it, so that two names of
//! one thing are one key.

use super::model::{base_verb, np_key, np_words};
use super::vocabulary::occurrences;
use crate::diagnostic::{Diagnostic, SpecRef};
use crate::document::{Document, SpecSet, Spec};
use crate::syntax::ast::{Core, Definiens, NpGroup};
use crate::syntax::parse::raw_words;
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

/// Whether a word is a lowercase article. Capitalized `A` is usually a name.
pub(super) fn is_article(w: &str) -> bool {
    matches!(w, "the" | "a" | "an")
}

/// Drops articles from a word list. A sentence-initial capitalized article
/// counts as one, and a word standing alone is never dropped, so that the
/// value `A` in `kind is A or B` survives.
fn without_articles(words: Vec<&str>) -> Vec<&str> {
    let count = words.len();
    words
        .into_iter()
        .enumerate()
        .filter(|(i, w)| {
            let has_next = i + 1 < count;
            !(has_next && (is_article(w) || (*i == 0 && matches!(*w, "The" | "A" | "An"))))
        })
        .map(|(_, w)| w)
        .collect()
}

pub(super) fn strip_backticks(w: &str) -> &str {
    if w.len() >= 3 && w.starts_with('`') && w.ends_with('`') {
        &w[1..w.len() - 1]
    } else {
        w
    }
}

/// How one namespace reads names. Every key in the model passes through
/// [`Lexicon::canon`], so two names of one thing can never escape a check.
/// An alias belongs to the namespace that declares it, like any other name.
#[derive(Debug, Clone, Default)]
pub struct Lexicon {
    /// The aliases of each namespace, as word sequences, longest first.
    members: Arc<BTreeMap<String, AliasList>>,
    /// The aliases readable from the current block.
    visible: AliasList,
    /// The verbs of the language: the fixed English verbs and the declared predicates.
    pub(crate) verbs: BTreeSet<String>,
    /// The words of the declared names, as they are spelled: a declared word
    /// keeps its spelling, and a plural meets the declared singular.
    declared_words: Arc<BTreeSet<String>>,
    /// The declared names, as folded word sequences: a closed-class word is
    /// a word of a name only inside one of them.
    declared_terms: Arc<BTreeSet<Vec<String>>>,
    scopes: Option<Arc<Scopes>>,
    namespace: String,
    /// The namespaces named by the current block's `use` declarations.
    uses: Vec<String>,
    qualifiers: BTreeMap<String, String>,
    derived: Arc<BTreeMap<String, Derived>>,
    predicates: Arc<BTreeSet<String>>,
    mapping: Arc<BTreeMap<String, String>>,
}

#[derive(Debug, Clone)]
pub(crate) struct Derived {
    pub origin: Document,
    pub reference: SpecRef,
    pub body: NpGroup,
}

type AliasList = Vec<(Vec<String>, String)>;

/// Which terms each namespace declares.
#[derive(Debug, Clone, Default)]
pub struct Scopes {
    /// Term to the namespaces that declare or define it.
    pub declared: BTreeMap<String, BTreeSet<String>>,
    pub namespaces: BTreeSet<String>,
    root: Option<String>,
    inference_cycles: BTreeSet<(String, String)>,
}

impl Scopes {
    /// The used namespaces that declare a term.
    pub fn import_candidates(&self, uses: &[String], term: &str) -> Vec<String> {
        let Some(owners) = self.declared.get(term) else { return Vec::new() };
        uses.iter().filter(|i| owners.contains(*i)).cloned().collect::<BTreeSet<_>>().into_iter().collect()
    }

    /// Resolves the namespace part of a qualified name: an absolute name, or
    /// the last components of a namespace the block uses.
    pub fn qualifier(&self, uses: &[String], qualifier: &str) -> Option<String> {
        if self.namespaces.contains(qualifier) {
            return Some(qualifier.to_string());
        }
        if let Some(root) = &self.root {
            if let Some(tail) = qualifier.strip_prefix(root) {
                let local = tail.strip_prefix('.').unwrap_or(tail);
                if (tail.is_empty() || tail.starts_with('.')) && self.namespaces.contains(local) {
                    return Some(local.to_string());
                }
            }
        }
        let mut candidates = uses.iter().filter(|i| i.ends_with(&format!(".{qualifier}")) && self.namespaces.contains(*i)).collect::<BTreeSet<_>>().into_iter();
        let candidate = candidates.next()?;
        candidates.next().is_none().then(|| candidate.clone())
    }

    /// The namespace that owns a term used in `namespace`: its own declaration,
    /// then a used namespace, and otherwise the namespace itself. A parent
    /// namespace gives nothing to its children.
    fn owner(&self, namespace: &str, uses: &[String], term: &str) -> String {
        if self.declared.get(term).is_some_and(|owners| owners.contains(namespace)) {
            return namespace.to_string();
        }
        self.import_candidates(uses, term).into_iter().next().unwrap_or_else(|| namespace.to_string())
    }
}

fn qualified(namespace: &str, term: &str) -> String {
    if namespace.is_empty() {
        term.to_string()
    } else {
        format!("{namespace}::{term}")
    }
}


/// The singular of a word by its ending alone. A word in `-ss`, `-us` or
/// `-is` is no plural (`class`, `status`, `analysis`).
pub(crate) fn singular_by_ending(word: &str) -> String {
    if word.len() < 4 || crate::syntax::words::is_no_plural(word) || !word.ends_with('s') || word.ends_with("ss") || word.ends_with("us") || word.ends_with("is") {
        return word.to_string();
    }
    if let Some(stem) = word.strip_suffix("ies").filter(|stem| stem.len() >= 2) {
        return format!("{stem}y");
    }
    for ending in ["sses", "shes", "ches", "xes", "zes"] {
        if word.ends_with(ending) {
            return word[..word.len() - 2].to_string();
        }
    }
    word[..word.len() - 1].to_string()
}

/// `true` for the base form of a verb that the language knows in itself.
fn known_verb(word: &str) -> bool {
    static VERBS: std::sync::OnceLock<BTreeSet<String>> = std::sync::OnceLock::new();
    VERBS.get_or_init(|| crate::syntax::parse::english_verbs().into_iter().map(base_verb).collect()).contains(word)
}

/// The singular spellings that a word may stand for.
fn singular_candidates(word: &str) -> Vec<String> {
    let mut out = Vec::new();
    if let Some(stem) = word.strip_suffix("ies") {
        out.push(format!("{stem}y"));
    }
    if let Some(stem) = word.strip_suffix("es") {
        out.push(stem.to_string());
    }
    if let Some(stem) = word.strip_suffix('s') {
        out.push(stem.to_string());
    }
    out
}

fn sorted_aliases(map: &BTreeMap<String, String>, declared: &Arc<BTreeSet<String>>) -> AliasList {
    let plain = Lexicon { declared_words: declared.clone(), ..Default::default() };
    let mut aliases: AliasList = map.iter().map(|(k, v)| (plain.canon(k).split_whitespace().map(str::to_string).collect(), plain.canon(v))).collect();
    aliases.sort_by_key(|(k, _)| std::cmp::Reverse(k.len()));
    aliases
}

impl Lexicon {
    /// A lexicon from the aliases of each namespace.
    pub fn new(aliases: &BTreeMap<String, BTreeMap<String, String>>) -> Self {
        Self::with_declared(aliases, BTreeSet::new())
    }

    /// A lexicon from the aliases of each namespace and the words of the
    /// declared names. The number of a word is decided by these and by its
    /// ending, never by what other statements hold.
    pub fn with_declared(aliases: &BTreeMap<String, BTreeMap<String, String>>, declared_words: BTreeSet<String>) -> Self {
        let declared_words = Arc::new(declared_words);
        let members = aliases.iter().map(|(ns, map)| (ns.clone(), sorted_aliases(map, &declared_words))).collect();
        let mut lex = Self { members: Arc::new(members), declared_words, ..Default::default() };
        lex.visible = lex.members.get("").cloned().unwrap_or_default();
        lex
    }

    pub fn with_scopes(mut self, scopes: Scopes) -> Self {
        self.scopes = Some(Arc::new(scopes));
        self
    }

    /// This lexicon as seen from a block that uses the given namespaces.
    fn scoped(&self, namespace: &str, uses: Vec<String>) -> Self {
        let mut out = self.clone();
        out.namespace = namespace.to_string();
        out.visible.clear();
        out.visible = self.members.get(namespace).cloned().unwrap_or_default();
        for used in &uses {
            for (alias, canonical) in self.members.get(used).into_iter().flatten() {
                if self.scopes.as_ref().is_some_and(|scopes| {
                    let spelling = alias.join(" ");
                    scopes.declared.get(&spelling).is_some_and(|owners| owners.contains(namespace))
                        || scopes.import_candidates(&uses, &spelling).len() > 1
                }) {
                    continue;
                }
                if out.visible.iter().any(|(existing, _)| existing == alias) {
                    continue;
                }
                let canonical = if canonical.contains("::") { canonical.clone() } else { qualified(used, canonical) };
                out.visible.push((alias.clone(), canonical));
            }
        }
        out.visible.sort_by_key(|(k, _)| std::cmp::Reverse(k.len()));
        out.uses = uses;
        out
    }

    /// This lexicon as seen from a namespace with no `use` declarations.
    pub fn in_namespace(&self, namespace: &str) -> Self {
        self.scoped(namespace, Vec::new())
    }

    /// This lexicon as seen from one namespace block.
    /// This lexicon without its aliases: every name is read as it is
    /// written. The reading of a sentence uses it, so that the contracts of
    /// a sentence follow from the sentence alone; that two names name one
    /// term is said beside the contracts, when they are verified.
    pub fn without_aliases(&self) -> Self {
        Self { visible: Vec::new(), ..self.clone() }
    }

    /// `true` when a namespace of the set declares an alias.
    pub fn has_aliases(&self) -> bool {
        self.members.values().any(|aliases| !aliases.is_empty())
    }

    pub fn in_document(&self, doc: &Document) -> Self {
        let mut lex = self.clone();
        lex.mapping = Arc::new(doc.application_mapping.clone());
        lex.qualifiers = doc.imports.iter().filter(|import| import.name != import.namespace)
            .map(|import| (import.name.clone(), import.namespace.clone())).collect();
        lex.scoped(&doc.namespace, doc.imports.iter().map(|i| i.namespace.clone()).collect())
    }

    pub(crate) fn is_applied(&self) -> bool {
        !self.mapping.is_empty()
    }

    /// The action identity of a declared predicate, including that of an alias.
    pub fn predicate_identity(&self, lemma: &str) -> Option<String> {
        let name = self.resolve(&self.canon(lemma));
        self.predicates.contains(&name).then_some(name)
    }

    pub(crate) fn derived(&self, name: &str) -> Option<&Derived> {
        self.derived.get(name)
    }



    /// The syntax and declaration scope of a class abbreviation.
    pub fn class_body(&self, name: &str) -> Option<(&NpGroup, Self)> {
        self.derived(name).map(|derived| (&derived.body, self.in_definition(derived)))
    }

    /// Resolve a definition in the namespace that owns it, using the mapping
    /// under which its body is being used.
    pub(crate) fn in_definition(&self, derived: &Derived) -> Self {
        let mut scoped = self.in_document(&derived.origin);
        scoped.mapping = Arc::clone(&self.mapping);
        scoped
    }

    pub(crate) fn local_name(&self, spelling: &str) -> String {
        let plain = Self { members: Arc::new(BTreeMap::new()), visible: Vec::new(), ..self.clone() };
        qualified(&self.namespace, &plain.canon(spelling))
    }

    fn declared_key(&self, key: &str) -> bool {
        let (namespace, term) = key.rsplit_once("::").unwrap_or(("", key));
        self.scopes.as_ref().and_then(|scopes| scopes.declared.get(term)).is_some_and(|owners| owners.contains(namespace))
    }

    fn grounded_key(&self, key: &str) -> bool {
        key.rsplit_once('#').is_some_and(|(name, index)| {
            !index.is_empty() && index.bytes().all(|byte| byte.is_ascii_digit()) && self.declared_key(name)
        })
    }

    pub(crate) fn known(&self, key: &str) -> bool {
        self.declared_key(key) || self.grounded_key(key)
    }

    fn qualifier(&self, name: &str) -> Option<String> {
        let scopes = self.scopes.as_ref()?;
        let canonical = self.qualifiers.get(name).map_or(name, String::as_str);
        scopes.qualifier(&self.uses, canonical)
    }

    /// The key of a term: its name, qualified by the namespace that owns it.
    pub fn resolve(&self, term: &str) -> String {
        let Some(scopes) = &self.scopes else { return term.to_string() };
        if self.grounded_key(term) {
            return term.to_string();
        }
        let name = if let Some((qualifier, name)) = term.split_once("::") {
            qualified(&self.qualifier(qualifier).unwrap_or_else(|| qualifier.to_string()), name)
        } else {
            qualified(&scopes.owner(&self.namespace, &self.uses, term), term)
        };
        self.mapping.get(&name).cloned().unwrap_or(name)
    }

    /// Resolves an explicitly written name before the caller checks its kind or
    /// decides whether its own declaration context can introduce it.
    pub fn resolve_explicit(&self, spelling: &str) -> Result<String, String> {
        if let Some(scopes) = &self.scopes {
            let plain = Self { members: Arc::new(BTreeMap::new()), visible: Vec::new(), ..self.clone() };
            let written = plain.canon(spelling);
            if let Some((qualifier, _)) = written.split_once("::") {
                if self.qualifier(qualifier).is_none() {
                    return Err(format!("namespace `{qualifier}` is unknown or ambiguous in this scope"));
                }
            } else if !scopes.declared.get(&written).is_some_and(|owners| owners.contains(&self.namespace)) {
                let candidates = scopes.import_candidates(&self.uses, &written);
                if candidates.len() > 1 {
                    return Err(format!("`{written}` is ambiguous between {}; write a qualified name", candidates.join(" and ")));
                }
            }
        }
        Ok(self.resolve(&self.canon(spelling)))
    }

    pub fn with_verbs(mut self, verbs: BTreeSet<String>) -> Self {
        self.verbs = verbs;
        self
    }

    /// Reads an alias written with its namespace: `orders::buyer`.
    fn qualified_alias(&self, words: &[String]) -> Option<(usize, String)> {
        let (qualifier, name) = words.first()?.split_once("::")?;
        let namespace = self.qualifier(qualifier)?;
        let mut wanted = vec![name.to_string()];
        wanted.extend(words[1..].iter().cloned());
        let (alias, canonical) = self.members.get(&namespace)?.iter().find(|(alias, _)| wanted.starts_with(alias.as_slice()))?;
        Some((alias.len(), if canonical.contains("::") { canonical.clone() } else { qualified(&namespace, canonical) }))
    }

    /// The spelling that a word of a name has in a key: a plural is its
    /// singular, and a word with a capital stays as it is written. A plural
    /// of a declared word is that word.
    pub fn number(&self, word: &str) -> String {
        if word.len() < 4 || word.contains("::") {
            return word.to_string();
        }
        let (head, last) = word.rsplit_once('-').map_or(("", word), |(head, last)| (head, last));
        if !head.is_empty() {
            let last = self.number(last);
            return format!("{head}-{last}");
        }
        if !last.chars().all(|c| c.is_ascii_alphabetic()) {
            return word.to_string();
        }
        let mut chars = last.chars();
        let first = chars.next().unwrap_or(' ');
        let rest = chars.as_str();
        let lowered = if first.is_ascii_uppercase() && rest.chars().all(|c| c.is_ascii_lowercase()) {
            // A capital inside a sentence is part of the word, whatever the
            // other statements declare: `Closed` stays. The capital that
            // only opens a sentence is dropped where the sentence is read.
            return word.to_string();
        } else if last.chars().all(|c| c.is_ascii_lowercase()) {
            last.to_string()
        } else {
            return word.to_string();
        };
        if crate::syntax::words::is_no_plural(&lowered) {
            return lowered;
        }
        // `organizes` and `caches` are forms of `organize` and `cache`.
        if let Some(verb) = singular_candidates(&lowered).into_iter().find(|c| known_verb(c)) {
            return verb;
        }
        singular_by_ending(&lowered)
    }

    /// Drops articles and literal quotes, then applies the aliases. This
    /// reads a declared name (a term, an alias, a value of a declaration);
    /// the key of a node of a sentence is built by the `key` module.
    pub fn canon(&self, text: &str) -> String {
        let words: Vec<String> = without_articles(raw_words(text).into_iter().map(|(_, w)| w).collect()).into_iter().map(str::to_string).collect();
        self.canon_words(&words).into_iter().map(|(text, _, _)| text).collect::<Vec<_>>().join(" ")
    }

    /// The names that a run of words spells: each declared name with the
    /// words that it covers, and each other word in the spelling of a key.
    pub(crate) fn canon_words(&self, raw: &[String]) -> Vec<(String, std::ops::Range<usize>, bool)> {
        let words: Vec<String> = raw.iter().map(|w| if w.len() >= 3 && w.starts_with('`') && w.ends_with('`') { strip_backticks(w).to_string() } else { self.number(w) }).collect();
        let canonical = self.qualified_alias(&words).filter(|(len, _)| *len == words.len()).map(|(_, name)| name)
            .or_else(|| self.visible.iter().find(|(alias, _)| alias == &words).map(|(_, name)| name.clone()));
        match canonical {
            Some(name) => vec![(name, 0..words.len(), true)],
            None => words.into_iter().enumerate().map(|(i, word)| (word, i..i + 1, false)).collect(),
        }
    }

    /// The declared names, as folded word sequences.
    pub fn with_terms(mut self, terms: BTreeSet<Vec<String>>) -> Self {
        self.declared_terms = Arc::new(terms);
        self
    }

    /// `true` when a word of a phrase stands inside a declared name that the phrase spells.
    /// Whether the words are a declared name.
    pub(crate) fn declares(&self, words: &[String]) -> bool {
        let folded: Vec<String> = words.iter().map(|w| crate::reading::meaning::fold_word(w)).collect();
        self.declared_terms.contains(&folded)
    }

    pub(crate) fn in_declared_term(&self, word: &str, phrase: &[String]) -> bool {
        let fold = crate::reading::meaning::fold_word;
        let word = fold(word);
        let phrase: Vec<String> = phrase.iter().map(|w| fold(w)).collect();
        self.declared_terms.iter().any(|term| term.len() > 1 && term.contains(&word) && phrase.windows(term.len()).any(|w| w == term.as_slice()))
    }
}


type AliasMap = BTreeMap<String, String>;

/// Collects each namespace's aliases, resolving chains within it. An alias is
/// a member of its namespace, so two namespaces may use one word differently.
fn collect_aliases(set: &SpecSet, out: &mut Vec<Diagnostic>) -> BTreeMap<String, AliasMap> {
    let mut direct: BTreeMap<String, AliasMap> = BTreeMap::new();
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let members = direct.entry(doc.namespace.clone()).or_default();
        for alias in &doc.aliases {
            let at = SpecRef { id: format!("{}:{}", alias.file, alias.line), file: alias.file.clone(), line: alias.line, text: format!("alias {} = {}", alias.term, alias.canonical) };
            match members.get(&alias.term) {
                Some(existing) if existing != &alias.canonical => out.push(Diagnostic::error("alias-conflict", format!("the alias `{}` already names `{existing}` in this namespace", alias.term), vec![at])),
                _ => {
                    members.insert(alias.term.clone(), alias.canonical.clone());
                }
            }
        }
    }
    let mut resolved = BTreeMap::new();
    for (namespace, members) in direct {
        let mut names = AliasMap::new();
        for term in members.keys() {
            let mut current = term;
            let mut steps = 0;
            while let Some(next) = members.get(current) {
                current = next;
                steps += 1;
                if steps > members.len() {
                    break;
                }
            }
            if steps > members.len() {
                out.push(Diagnostic::error("alias-cycle", format!("the alias `{term}` is part of a cycle"), vec![]));
            } else {
                names.insert(term.clone(), current.clone());
            }
        }
        resolved.insert(namespace, names);
    }
    resolved
}

/// The words of the declared names of a set, as they are spelled: terms,
/// primitives, measures, controlled terms, aliases and defined terms.
fn declared_words(set: &SpecSet) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    let mut add = |name: &str| out.extend(name.split_whitespace().map(|w| w.trim_matches('`').to_string()));
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        doc.vocabulary.iter().for_each(|d| add(&d.term));
        doc.primitives.iter().chain(&doc.measures).for_each(|d| add(&d.name));
        doc.controls.iter().for_each(|d| add(&d.name));
        doc.aliases.iter().for_each(|a| {
            add(&a.term);
            add(&a.canonical);
        });
        for spec in doc.specs.iter().chain(&doc.symbol_sources) {
            // A capital that only opens the sentence is no part of the name.
            if let Core::Definition { term, .. } = &spec.sentence.core {
                let mut words = np_words(term);
                let opening = spec.sentence.source.split_whitespace().next().unwrap_or_default();
                if let Some(first) = words.iter_mut().find(|w| w.as_str() == opening) {
                    let mut chars = first.chars();
                    if let Some(initial) = chars.next().filter(|c| c.is_ascii_uppercase()) {
                        if chars.as_str().chars().all(|c| c.is_ascii_lowercase()) {
                            *first = format!("{}{}", initial.to_ascii_lowercase(), chars.as_str());
                        }
                    }
                }
                add(&words.join(" "));
            }
        }
    }
    out
}

/// The verbs of the language: the fixed English verbs and the declared
/// predicates. What other statements use adds nothing.
fn language_verbs(set: &SpecSet) -> BTreeSet<String> {
    let mut out: BTreeSet<String> = crate::syntax::parse::english_verbs().into_iter().map(|v| base_verb(v)).collect();
    out.extend(set.packages.iter().flat_map(|p| &p.documents).flat_map(|d| &d.predicates).filter_map(|p| p.name.split_whitespace().next().map(base_verb)));
    out
}

/// Records which namespaces declare which terms.
fn build_scopes(set: &SpecSet, lex: &Lexicon) -> Scopes {
    let mut scopes = Scopes {
        root: set.packages.iter().find(|package| package.is_root)
            .map(|package| package.name.clone()),
        ..Default::default()
    };
    let mut inferred: BTreeMap<String, BTreeMap<String, BTreeSet<String>>> = BTreeMap::new();
    for doc in set.packages.iter().flat_map(|p| &p.documents).filter(|doc| doc.application_mapping.is_empty()) {
        let ns = &doc.namespace;
        let scoped = lex.in_document(doc);
        scopes.namespaces.insert(ns.clone());
        for decl in &doc.vocabulary {
            let written = scoped.local_name(&decl.term).rsplit("::").next().unwrap_or_default().to_string();
            scopes.declared.entry(written).or_default().insert(ns.clone());
        }
        let names = doc.primitives.iter().chain(&doc.measures).chain(&doc.individuals).map(|decl| &decl.name)
            .chain(doc.predicates.iter().map(|decl| &decl.name))
            .chain(doc.controls.iter().map(|decl| &decl.name))
            .chain(doc.aliases.iter().map(|decl| &decl.term));
        let raw = Lexicon { members: Arc::new(BTreeMap::new()), visible: Vec::new(), ..scoped.clone() };
        for name in names {
            scopes.declared.entry(raw.canon(name)).or_default().insert(ns.clone());
        }
        for spec in doc.specs.iter().chain(&doc.symbol_sources) {
            for (term, kind) in occurrences(&spec.sentence, &scoped) {
                if term.contains("::") || term.starts_with('$') {
                    continue;
                }
                if kind == "defined" {
                    scopes.declared.entry(term).or_default().insert(ns.clone());
                } else if kind != "action" && set.vocabulary_mode == crate::document::VocabularyMode::Inferred && super::grounding::describes(&spec.sentence.core) {
                    inferred.entry(term).or_default().entry(ns.clone()).or_default().extend(doc.imports.iter().map(|import| import.namespace.clone()));
                }
            }
        }
    }
    for (term, candidates) in inferred {
        let owners = scopes.declared.entry(term.clone()).or_default();
        // First register names whose candidate scopes have no imported candidate.
        // A chain resolves from the supplying end. A cycle without a declaration
        // has no inferred export.
        let mut pending = candidates;
        loop {
            let ready: Vec<_> = pending.iter().filter(|(ns, uses)| {
                owners.contains(*ns) || uses.iter().any(|import| owners.contains(import)) || uses.iter().all(|import| !pending.contains_key(import) || import == *ns)
            }).map(|(ns, _)| ns.clone()).collect();
            if ready.is_empty() {
                break;
            }
            for ns in ready {
                let uses = pending.remove(&ns).unwrap_or_default();
                if !uses.iter().any(|import| owners.contains(import)) {
                    owners.insert(ns);
                }
            }
        }
        scopes.inference_cycles.extend(pending.into_keys().map(|ns| (ns, term.clone())));
    }
    scopes
}

/// Reports names that a block cannot resolve to one owner.
fn check_scopes(set: &SpecSet, scopes: &Scopes, lex: &Lexicon, out: &mut Vec<Diagnostic>) {
    let mut seen = BTreeSet::new();
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let uses: Vec<String> = doc.imports.iter().map(|i| i.namespace.clone()).collect();
        for import in &doc.imports {
            let package_reference = import.reference_only
                && scopes.namespaces.iter().any(|namespace| namespace.starts_with(&format!("{}.", import.namespace)));
            if !scopes.namespaces.contains(&import.namespace) && !package_reference {
                let at = SpecRef { id: format!("{}:{}", import.file, import.line), file: import.file.clone(), line: import.line, text: format!("use {}", import.name) };
                out.push(Diagnostic::error("namespace-unknown", format!("the namespace `{}` does not exist", import.name), vec![at]));
            }
        }
        let mut scoped = lex.in_document(doc);
        scoped.members = Arc::new(BTreeMap::new());
        scoped.visible.clear();
        let mut check_names = |names: Vec<(String, &'static str)>, at: &SpecRef| {
            for (term, _) in names {
                if term.starts_with('$') {
                    out.push(Diagnostic::error("UNBOUND_VARIABLE", format!("`{term}` has no binder in this statement"), vec![at.clone()]));
                    continue;
                }
                if let Some((qualifier, name)) = term.split_once("::") {
                    // A modifier may stand before a qualified head: `applicable packages::declaration`.
                    let qualifier = qualifier.rsplit(' ').next().unwrap_or(qualifier);
                    let declared = scoped.qualifiers.get(qualifier).map_or(qualifier, String::as_str);
                    match scopes.qualifier(&uses, declared) {
                        None => out.push(Diagnostic::error("namespace-unknown", format!("the namespace `{qualifier}` is unknown or ambiguous in this scope"), vec![at.clone()])),
                        Some(namespace) if !scopes.declared.get(name).is_some_and(|owners| owners.contains(&namespace)) => {
                            out.push(Diagnostic::error("UNRESOLVED_TERM", format!("namespace `{namespace}` exports no symbol named `{name}`"), vec![at.clone()]));
                        }
                        _ => {}
                    }
                    continue;
                }
                if scopes.inference_cycles.contains(&(doc.namespace.clone(), term.clone())) && seen.insert((doc.namespace.clone(), term.clone())) {
                    out.push(Diagnostic::error("AMBIGUOUS_TERM", format!("mutually used namespaces could introduce `{term}`; declare its owner explicitly"), vec![at.clone()]));
                }
                let local = scopes.declared.get(&term).is_some_and(|owners| owners.contains(&doc.namespace));
                let candidates = scopes.import_candidates(&uses, &term);
                if !local && candidates.len() > 1 && seen.insert((doc.namespace.clone(), term.clone())) {
                    let diagnostic = Diagnostic::error("AMBIGUOUS_TERM", format!("`{term}` is declared by {}; write the namespace, as in `{}::{term}`", candidates.join(" and "), candidates[0]), vec![at.clone()]);
                    out.push(diagnostic.qualifying(&term, &candidates));
                }
            }
        };
        for alias in &doc.aliases {
            let at = SpecRef::point(&alias.file, alias.line, &format!("alias {} = {}", alias.term, alias.canonical));
            check_names(vec![(scoped.canon(&alias.canonical), "alias target")], &at);
        }
        for spec in doc.specs.iter().chain(&doc.symbol_sources) {
            let at = SpecRef { id: spec.display_id(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
            let mut names = occurrences(&spec.sentence, &scoped);
            if let Core::Definition { definiens: Definiens::Np { np, .. }, .. } = &spec.sentence.core {
                super::nominal::symbols(np, &scoped, &mut names);
            }
            check_names(names, &at);
        }
    }
}

/// Rejects two different meanings for one defined term in one namespace.
fn check_name_collisions(set: &SpecSet, lex: &Lexicon, out: &mut Vec<Diagnostic>) {
    let mut defined: BTreeMap<(String, String), &Spec> = BTreeMap::new();
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let scoped = lex.in_document(doc);
        for spec in doc.specs.iter().chain(&doc.symbol_sources) {
            let Core::Definition { term, definiens } = &spec.sentence.core else { continue };
            let key = (doc.namespace.clone(), np_key(term, &scoped));
            // An alias can give the term and its definiens one name: the definition then says nothing.
            if let Definiens::Np { np: NpGroup::Single(genus), roles } = definiens {
                if roles.is_empty() && genus.relative.is_none() && genus.of.is_none() && np_key(genus, &scoped) == key.1 && genus.render() != term.render() {
                    let at = SpecRef { id: spec.display_id(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
                    out.push(Diagnostic::warning("definition-collapsed", format!("the term and the definiens of this definition are both read as `{}`, so the definition says nothing: an alias gives the two one name", key.1), vec![at]));
                }
            }
            match defined.get(&key) {
                Some(first) if first.sentence.render() != spec.sentence.render() => {
                    let refs = [*first, spec].iter().map(|s| SpecRef { id: s.display_id(), file: s.file.clone(), line: s.line, text: s.sentence.source.clone() }).collect();
                    out.push(Diagnostic::error("NAME_COLLISION", format!("`{}` has two definitions in this namespace", key.1), refs));
                }
                _ => {
                    defined.insert(key, spec);
                }
            }
        }
    }
}

/// The name tables of a set, before the terms of each namespace are attached.
fn tables(set: &SpecSet, diagnostics: &mut Vec<Diagnostic>) -> (Lexicon, Scopes) {
    let aliases = collect_aliases(set, diagnostics);
    let lex = Lexicon::with_declared(&aliases, declared_words(set)).with_verbs(language_verbs(set));
    let terms = super::meaning::declared_terms(set, &lex);
    let lex = lex.with_terms(terms);
    let scopes = build_scopes(set, &lex);
    let initial = lex.clone().with_scopes(scopes.clone());
    let mut members = (*lex.members).clone();
    for doc in set.packages.iter().flat_map(|pkg| &pkg.documents) {
        let scoped = initial.in_document(doc);
        let Some(aliases) = members.get_mut(&doc.namespace) else { continue };
        for (spelling, target) in aliases {
            let written = spelling.join(" ");
            if doc.aliases.iter().any(|alias| scoped.local_name(&alias.term).rsplit("::").next() == Some(written.as_str())) {
                let resolved = scoped.resolve(target);
                *target = if resolved.contains("::") { resolved } else { format!("::{resolved}") };
            }
        }
    }
    let lex = Lexicon { members: Arc::new(members), ..lex };
    let resolved = lex.clone().with_scopes(scopes.clone());
    let mut derived = BTreeMap::new();
    let mut predicates = BTreeSet::new();
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let mut origin = Document { namespace: doc.namespace.clone(), imports: doc.imports.clone(), ..Document::default() };
        origin.file = doc.file.clone();
        let scoped = resolved.in_document(doc);
        predicates.extend(doc.predicates.iter().map(|decl| scoped.local_name(&decl.name)));
        for spec in doc.specs.iter().chain(&doc.symbol_sources) {
            if let Core::Definition { term, definiens: Definiens::Np { np, roles } } = &spec.sentence.core {
                if roles.is_empty() && super::nominal::definable(np) {
                    let id = if doc.namespace.is_empty() { spec.display_id() } else { format!("{}::{}", doc.namespace, spec.display_id()) };
                    let reference = SpecRef { id, file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
                    derived.insert(np_key(term, &scoped), Derived { origin: origin.clone(), reference, body: np.clone() });
                }
            }
        }
    }
    (Lexicon { derived: Arc::new(derived), predicates: Arc::new(predicates), ..lex }, scopes)
}

impl Lexicon {
    /// The lexicon of a set: how each of its namespaces reads names.
    pub fn of(set: &SpecSet) -> Lexicon {
        let (lex, scopes) = tables(set, &mut Vec::new());
        lex.with_scopes(scopes)
    }

    /// The lexicon of a set, with a report of what its names leave open: an
    /// alias that conflicts or forms a cycle, a namespace that does not
    /// exist, a term that several used namespaces declare, and a term with
    /// two definitions in one namespace.
    pub fn checked(set: &SpecSet, diagnostics: &mut Vec<Diagnostic>) -> Lexicon {
        let (lex, scopes) = tables(set, diagnostics);
        // The names are checked as they are written, before each resolves to its owner.
        check_scopes(set, &scopes, &lex, diagnostics);
        check_name_collisions(set, &lex, diagnostics);
        lex.with_scopes(scopes)
    }
}
