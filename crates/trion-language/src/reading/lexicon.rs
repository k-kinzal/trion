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
}

type AliasList = Vec<(Vec<String>, String)>;

/// Which terms each namespace declares.
#[derive(Debug, Clone, Default)]
pub struct Scopes {
    /// Term to the namespaces that declare or define it.
    pub declared: BTreeMap<String, BTreeSet<String>>,
    pub namespaces: BTreeSet<String>,
}

impl Scopes {
    /// The used namespaces that declare a term.
    pub fn import_candidates(&self, uses: &[String], term: &str) -> Vec<String> {
        let Some(owners) = self.declared.get(term) else { return Vec::new() };
        uses.iter().filter(|i| owners.contains(*i)).cloned().collect()
    }

    /// Resolves the namespace part of a qualified name: an absolute name, or
    /// the last components of a namespace the block uses.
    pub fn qualifier(&self, uses: &[String], qualifier: &str) -> Option<String> {
        if self.namespaces.contains(qualifier) {
            return Some(qualifier.to_string());
        }
        uses.iter().find(|i| i.as_str() == qualifier || i.ends_with(&format!(".{qualifier}"))).filter(|candidate| self.namespaces.contains(*candidate)).cloned()
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
        out.visible = self.members.get(namespace).cloned().unwrap_or_default();
        for used in &uses {
            for (alias, canonical) in self.members.get(used).into_iter().flatten() {
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
    pub fn in_document(&self, doc: &Document) -> Self {
        self.scoped(&doc.namespace, doc.imports.iter().map(|i| i.namespace.clone()).collect())
    }

    /// The key of a term: its name, qualified by the namespace that owns it.
    pub fn resolve(&self, term: &str) -> String {
        let Some(scopes) = &self.scopes else { return term.to_string() };
        if let Some((qualifier, name)) = term.split_once("::") {
            return qualified(&scopes.qualifier(&self.uses, qualifier).unwrap_or_else(|| qualifier.to_string()), name);
        }
        qualified(&scopes.owner(&self.namespace, &self.uses, term), term)
    }

    pub fn with_verbs(mut self, verbs: BTreeSet<String>) -> Self {
        self.verbs = verbs;
        self
    }

    /// Reads an alias written with its namespace: `orders::buyer`.
    fn qualified_alias(&self, words: &[String]) -> Option<(usize, String)> {
        let (qualifier, name) = words.first()?.split_once("::")?;
        let scopes = self.scopes.as_ref()?;
        let namespace = scopes.qualifier(&self.uses, qualifier)?;
        let mut wanted = vec![name.to_string()];
        wanted.extend(words[1..].iter().cloned());
        let (alias, canonical) = self.members.get(&namespace)?.iter().find(|(alias, _)| wanted.starts_with(alias.as_slice()))?;
        Some((alias.len(), if canonical.contains("::") { canonical.clone() } else { qualified(&namespace, canonical) }))
    }

    /// The spelling that a word of a name has in a key: a plural is its
    /// singular, and a capital that only opens a sentence is dropped. A
    /// declared spelling stays, and a plural of a declared word is that word.
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
        let declared = |w: &str| self.declared_words.contains(w);
        let mut chars = last.chars();
        let first = chars.next().unwrap_or(' ');
        let rest = chars.as_str();
        let lowered = if first.is_ascii_uppercase() && rest.chars().all(|c| c.is_ascii_lowercase()) {
            let lowered = format!("{}{rest}", first.to_ascii_lowercase());
            // `Clients` at the start of a sentence is `clients`; `English` stays.
            let plural = singular_by_ending(&lowered) != lowered;
            if declared(last) || !(declared(&lowered) || plural || singular_candidates(&lowered).iter().any(|c| declared(c))) {
                return word.to_string();
            }
            lowered
        } else if last.chars().all(|c| c.is_ascii_lowercase()) {
            last.to_string()
        } else {
            return word.to_string();
        };
        if crate::syntax::words::is_no_plural(&lowered) {
            return lowered;
        }
        if let Some(singular) = singular_candidates(&lowered).into_iter().find(|c| declared(c)) {
            return singular;
        }
        if declared(&lowered) {
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
        let mut out: Vec<(String, std::ops::Range<usize>, bool)> = Vec::new();
        let mut i = 0;
        'scan: while i < words.len() {
            if let Some((length, canonical)) = self.qualified_alias(&words[i..]) {
                out.push((canonical, i..i + length, true));
                i += length;
                continue 'scan;
            }
            // The longest name that starts here decides. A name that an alias
            // stands for may hold that alias (`statement` for `normative
            // statement`): the whole name is then read once, and the alias
            // inside it is not read again.
            let mut best: Option<(usize, &String)> = None;
            for (alias, canonical) in &self.visible {
                let target: Vec<&str> = canonical.rsplit("::").next().unwrap_or(canonical).split_whitespace().collect();
                let holds_alias = target.len() > alias.len() && target.windows(alias.len()).any(|w| w.iter().zip(alias).all(|(a, b)| a == b));
                let spelled = holds_alias && words.len() - i >= target.len() && words[i..i + target.len()].iter().zip(&target).all(|(a, b)| a == b);
                if spelled && best.is_none_or(|(length, _)| length < target.len()) {
                    best = Some((target.len(), canonical));
                }
                if words[i..].starts_with(alias.as_slice()) && best.is_none_or(|(length, _)| length < alias.len()) {
                    best = Some((alias.len(), canonical));
                }
            }
            if let Some((length, canonical)) = best {
                out.push((canonical.clone(), i..i + length, true));
                i += length;
                continue 'scan;
            }
            out.push((words[i].clone(), i..i + 1, false));
            i += 1;
        }
        out
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
        for spec in &doc.specs {
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
    let mut scopes = Scopes::default();
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let ns = &doc.namespace;
        let scoped = lex.in_document(doc);
        scopes.namespaces.insert(ns.clone());
        for decl in &doc.vocabulary {
            scopes.declared.entry(scoped.canon(&decl.term)).or_default().insert(ns.clone());
        }
        for spec in &doc.specs {
            for (term, kind) in occurrences(&spec.sentence, &scoped) {
                if kind == "defined" {
                    scopes.declared.entry(term).or_default().insert(ns.clone());
                }
            }
        }
    }
    scopes
}

/// Reports names that a block cannot resolve to one owner.
fn check_scopes(set: &SpecSet, scopes: &Scopes, lex: &Lexicon, out: &mut Vec<Diagnostic>) {
    let mut seen = BTreeSet::new();
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let uses: Vec<String> = doc.imports.iter().map(|i| i.namespace.clone()).collect();
        for import in &doc.imports {
            if !scopes.namespaces.contains(&import.namespace) {
                let at = SpecRef { id: format!("{}:{}", import.file, import.line), file: import.file.clone(), line: import.line, text: format!("use {}", import.name) };
                out.push(Diagnostic::error("namespace-unknown", format!("the namespace `{}` does not exist", import.name), vec![at]));
            }
        }
        let scoped = lex.in_document(doc);
        for spec in &doc.specs {
            let at = SpecRef { id: spec.display_id(), file: spec.file.clone(), line: spec.line, text: spec.sentence.source.clone() };
            for (term, kind) in occurrences(&spec.sentence, &scoped) {
                if kind == "action" || kind == "value" {
                    continue;
                }
                if let Some((qualifier, _)) = term.split_once("::") {
                    // A modifier may stand before a qualified head: `applicable packages::declaration`.
                    let qualifier = qualifier.rsplit(' ').next().unwrap_or(qualifier);
                    if scopes.qualifier(&uses, qualifier).is_none() {
                        out.push(Diagnostic::error("namespace-unknown", format!("the namespace `{qualifier}` does not exist"), vec![at.clone()]));
                    }
                    continue;
                }
                let local = scopes.declared.get(&term).is_some_and(|owners| owners.contains(&doc.namespace));
                let candidates = scopes.import_candidates(&uses, &term);
                if !local && candidates.len() > 1 && seen.insert((doc.namespace.clone(), term.clone())) {
                    out.push(Diagnostic::error("AMBIGUOUS_TERM", format!("`{term}` is declared by {}; write the namespace, as in `{}::{term}`", candidates.join(" and "), candidates[0]), vec![at.clone()]));
                }
            }
        }
    }
}

/// Rejects two different meanings for one defined term in one namespace.
fn check_name_collisions(set: &SpecSet, lex: &Lexicon, out: &mut Vec<Diagnostic>) {
    let mut defined: BTreeMap<(String, String), &Spec> = BTreeMap::new();
    for doc in set.packages.iter().flat_map(|p| &p.documents) {
        let scoped = lex.in_document(doc);
        for spec in &doc.specs {
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
    (lex, scopes)
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
