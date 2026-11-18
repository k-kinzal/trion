//! The notation scanner: a port of `api/parser/Scanner.scala`,
//! `ActiveNotation.scala` and the reduction step of `TokenList.scala`.
//!
//! The notations in scope are grouped by precedence and the groups are
//! scanned in increasing order. Scanning a token list with a group shifts
//! tokens from left to right; a token that matches the first delimiter of a
//! notation of the group opens that notation (the longest first delimiter
//! wins; notations that expect different markers are ambiguous), a token that
//! matches the next delimiter an open notation expects applies it, and a
//! notation whose remaining markers can be filled with the shifted tokens is
//! closed. A closed notation reduces the tokens it covers to one matched list,
//! whose arguments are unmatched lists that are scanned later, from the same
//! group on. When the input ends with an open notation that cannot close, the
//! scanner backtracks to the token that opened it and shifts that token
//! instead. Left-open notations close the open notations before them unless
//! their first delimiter associates to the right, so that `a - b + c` reads
//! as `(a - b) + c`.

use std::collections::HashMap;
use std::rc::Rc;

use crate::error::{Error, ErrorKind, Pos, Result};
use crate::lexer::{External, Lexed, Token};
use crate::notation::{Arity, Delim, Marker, Notation, Precedence};
use crate::uri::{GlobalName, LocalName};

/// A notation of a constant (`ParsingRule`).
#[derive(Debug)]
pub(crate) struct ParsingRule {
    pub(crate) name: GlobalName,
    pub(crate) aliases: Vec<LocalName>,
    pub(crate) notation: Rc<Notation>,
    pub(crate) arity: Arity,
    /// The number of arguments before the first delimiter.
    pub(crate) open_args: usize,
    /// The parsing markers with placeholder delimiters expanded.
    pub(crate) markers: Vec<Marker>,
    /// The first delimiter (or sequence separator) that triggers the rule.
    pub(crate) first_delim: Option<Delim>,
}

impl PartialEq for ParsingRule {
    fn eq(&self, o: &ParsingRule) -> bool {
        self.name == o.name && self.aliases == o.aliases && self.notation == o.notation
    }
}

impl ParsingRule {
    pub(crate) fn new(name: GlobalName, aliases: Vec<LocalName>, notation: Rc<Notation>) -> Result<ParsingRule> {
        let arity = notation.arity()?;
        let markers: Vec<Marker> = notation.parsing_markers().map(|m| m.expand(name.name(), &aliases)).collect();
        let first_delim = markers.iter().find_map(|m| match m {
            Marker::Delim(d) => Some(d.clone()),
            Marker::SeqArg(_, d) | Marker::LabelSeqArg(_, d, _) => Some(d.clone()),
            _ => None,
        });
        let open_args = notation.open_args(false);
        Ok(ParsingRule { name, aliases, notation, arity, markers, first_delim, open_args })
    }

    fn first_delim_len(&self) -> isize {
        self.first_delim.as_ref().map(|d| d.matched_text().chars().count() as isize).unwrap_or(-1)
    }
}

/// The rules of one precedence (`ParsingRuleGroup`), indexed by the first character of their first delimiter.
#[derive(Debug, Clone)]
pub(crate) struct RuleGroup {
    pub(crate) precedence: Precedence,
    pub(crate) rules: Vec<Rc<ParsingRule>>,
    by_first: HashMap<char, Vec<usize>>,
}

impl RuleGroup {
    fn new(precedence: Precedence) -> RuleGroup {
        RuleGroup { precedence, rules: Vec::new(), by_first: HashMap::new() }
    }
    fn push(&mut self, r: Rc<ParsingRule>) {
        if self.rules.iter().any(|o| **o == *r) {
            return;
        }
        if let Some(c) = r.first_delim.as_ref().and_then(|d| d.matched_text().chars().next()) {
            self.by_first.entry(c).or_default().push(self.rules.len());
        }
        self.rules.push(r);
    }
}

/// The rule table: groups in increasing order of precedence (`ParsingRuleTable`).
#[derive(Debug, Default, Clone)]
pub(crate) struct RuleTable {
    pub(crate) groups: Vec<RuleGroup>,
    /// The length in characters of the longest delimiter: how far the scanner looks ahead.
    longest_delim: usize,
}

impl RuleTable {
    pub(crate) fn add(&mut self, r: Rc<ParsingRule>) {
        for m in &r.markers {
            if let Marker::Delim(d) | Marker::SeqArg(_, d) | Marker::LabelSeqArg(_, d, _) | Marker::InstanceName(d) | Marker::Var { sep: Some(d), .. } = m {
                self.longest_delim = self.longest_delim.max(d.matched_text().chars().count());
            }
        }
        let p = r.notation.precedence();
        match self.groups.binary_search_by(|g| g.precedence.cmp(&p)) {
            Ok(i) => self.groups[i].push(r),
            Err(i) => {
                let mut g = RuleGroup::new(p);
                g.push(r);
                self.groups.insert(i, g);
            }
        }
    }
}

/// An element of a token list.
#[derive(Debug)]
#[allow(clippy::large_enum_variant)] // token lists are short-lived and scanned in place
pub(crate) enum Elem {
    Token(Token),
    External(External),
    Matched(Box<Matched>),
    Unmatched(Box<Unmatched>),
}

impl Elem {
    pub(crate) fn pos(&self) -> Pos {
        match self {
            Elem::Token(t) => t.pos,
            Elem::External(External::Term(_, p)) | Elem::External(External::Interpolation { pos: p, .. }) => *p,
            Elem::Matched(m) => m.pos,
            Elem::Unmatched(u) => u.tl.first().map(Elem::pos).unwrap_or_default(),
        }
    }
}

/// What a notation found for one argument or variable marker.
#[derive(Debug, Clone)]
pub(crate) enum FoundContent {
    /// A single argument.
    Simp(Marker),
    /// A sequence (possibly empty).
    Seq(Marker),
}

impl FoundContent {
    pub(crate) fn marker(&self) -> &Marker {
        match self {
            FoundContent::Simp(m) | FoundContent::Seq(m) => m,
        }
    }
}

/// A list reduced by a notation (`MatchedList`).
#[derive(Debug)]
pub(crate) struct Matched {
    pub(crate) rules: Vec<Rc<ParsingRule>>,
    pub(crate) tokens: Vec<(FoundContent, Vec<Unmatched>)>,
    pub(crate) pos: Pos,
}

/// A list that must become one subterm but has not been scanned yet (`UnmatchedList`).
#[derive(Debug)]
pub(crate) struct Unmatched {
    pub(crate) tl: Vec<Elem>,
    pub(crate) table: Rc<RuleTable>,
    pub(crate) group: usize,
}

impl Unmatched {
    pub(crate) fn from_lexed(lexed: Vec<Lexed>, table: Rc<RuleTable>) -> Unmatched {
        let tl = lexed
            .into_iter()
            .map(|l| match l {
                Lexed::Token(t) => Elem::Token(t),
                Lexed::External(e) => Elem::External(e),
            })
            .collect();
        Unmatched { tl, table, group: 0 }
    }

    /// Scans the list with all remaining groups; at most `max_open`
    /// notations may be open at once (beyond, an error of kind `Limit`), which
    /// bounds the depth of the scanned tree and the work per token.
    pub(crate) fn scan(&mut self, max_open: usize) -> Result<()> {
        let tl = Tokens::new(std::mem::take(&mut self.tl));
        let mut s = Scanner { tl, table: self.table.clone(), group: self.group, ci: 0, nct: 0, active: Vec::new(), max_open };
        for g in self.group..self.table.groups.len() {
            s.group = g;
            s.scan_group()?;
        }
        self.tl = s.tl.into_vec();
        Ok(())
    }
}

#[derive(Debug, Clone)]
enum Found {
    Delim(usize),
    Simp { start: usize, end: usize, marker: Marker },
    Seq { marker: Marker, args: Vec<(usize, usize)> },
}

impl Found {
    fn span(&self) -> Option<(usize, usize)> {
        match self {
            Found::Delim(p) => Some((*p, p + 1)),
            Found::Simp { start, end, .. } => Some((*start, *end)),
            Found::Seq { args, .. } => {
                if args.is_empty() {
                    None
                } else {
                    Some((args[0].0, args[args.len() - 1].1))
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Applicability {
    Applicable,
    NotApplicable,
}
use Applicability::*;

/// The operation remembered between `applicable`/`closable` and `apply`/`close`.
#[derive(Debug, Clone)]
enum Pending {
    DelimOnly,
    PickAllThenDelim(Marker),
    SinglesThenDelim(Vec<Marker>),
    SinglesAllThenDelim(Vec<Marker>),
    SeqSeparator(Marker, Delim),
    SeqLastThenDelim(Marker),
    SeqEmptyThenDelim(Marker),
    CloseSeqLast(Marker),
    CloseSeqEmpty(Marker),
    ClosePickAll(Marker),
    CloseSingles(Vec<Marker>),
}

struct Active {
    rules: Vec<Rc<ParsingRule>>,
    backtrack: (usize, usize),
    found: Vec<Found>,
    left: std::collections::VecDeque<Marker>,
    nct: usize,
    remember: Option<Pending>,
}

/// `ActiveNotation.matches`: the delimiter is the word, possibly continued by the single-character tokens that follow it.
fn matches(delim: &str, word: &str, future: &str) -> bool {
    if delim.chars().count() < word.chars().count() {
        return false;
    }
    let mut available = word.chars().chain(future.chars());
    delim.chars().all(|c| available.next() == Some(c))
}

fn delim_text(m: &Marker) -> Option<&str> {
    match m {
        Marker::Delim(d) => Some(d.matched_text()),
        _ => None,
    }
}

struct Picker {
    ci: usize,
    picked: usize,
}

impl Picker {
    fn pick(&mut self, len: usize) -> Result<(usize, usize)> {
        let end = self.ci.checked_sub(self.picked).ok_or_else(internal)?;
        let start = end.checked_sub(len).ok_or_else(internal)?;
        self.picked += len;
        Ok((start, end))
    }
}

fn internal() -> Error {
    Error::new(ErrorKind::Object, "the notation scanner reached an inconsistent state (MMT fails with an implementation error here)")
}

impl Active {
    fn new(rules: Vec<Rc<ParsingRule>>, backtrack: (usize, usize)) -> Active {
        let left = rules[0].markers.iter().cloned().collect();
        Active { rules, backtrack, found: Vec::new(), left, nct: 0, remember: None }
    }

    /// `splitOffSimples`: the leading simple child markers, and the index of the first other marker (`%w` is skipped).
    fn split_off_simples(&self) -> (Vec<Marker>, usize) {
        let mut ns = Vec::new();
        let mut i = 0;
        while i < self.left.len() {
            let m = &self.left[i];
            if m.is_simple_child() {
                ns.push(m.clone());
            } else if matches!(m, Marker::Delim(d) if d.text == "%w") {
            } else {
                break;
            }
            i += 1;
        }
        (ns, i)
    }

    fn on(&mut self, p: Pending) -> Applicability {
        self.remember = Some(p);
        Applicable
    }

    fn applicable(&mut self, word: &str, future: &str) -> Applicability {
        let (ns, rest) = self.split_off_simples();
        let next = self.left.get(rest).cloned();
        if let Some(s) = next.as_ref().and_then(delim_text) {
            if matches(s, word, future) {
                return match ns.len() {
                    0 => self.on(Pending::DelimOnly),
                    1 if self.nct > 0 => self.on(Pending::PickAllThenDelim(ns[0].clone())),
                    k if k == self.nct => self.on(Pending::SinglesThenDelim(ns)),
                    k if k < self.nct => self.on(Pending::SinglesAllThenDelim(ns)),
                    _ => NotApplicable,
                };
            }
        }
        if ns.is_empty() {
            if let Some(cm) = next.as_ref().filter(|m| m.is_child()) {
                if let Some(sep) = cm.sequence_via() {
                    if matches(sep.matched_text(), word, future) {
                        return self.on(Pending::SeqSeparator(cm.clone(), sep.clone()));
                    }
                    if let Some(s) = self.left.get(rest + 1).and_then(delim_text) {
                        if matches(s, word, future) {
                            return if self.nct > 0 { self.on(Pending::SeqLastThenDelim(cm.clone())) } else { self.on(Pending::SeqEmptyThenDelim(cm.clone())) };
                        }
                    }
                }
            }
        }
        NotApplicable
    }

    fn closable(&mut self) -> Applicability {
        let (ns, rest) = self.split_off_simples();
        let remaining = self.left.len() - rest;
        if ns.is_empty() && remaining == 1 && self.left[rest].is_child() && self.left[rest].sequence_via().is_some() {
            let m = self.left[rest].clone();
            return if self.nct > 0 {
                self.on(Pending::CloseSeqLast(m))
            } else if !self.in_seq(&m) {
                self.on(Pending::CloseSeqEmpty(m))
            } else {
                NotApplicable
            };
        }
        if remaining == 0 {
            if ns.len() == 1 && self.nct > 0 {
                return self.on(Pending::ClosePickAll(ns[0].clone()));
            }
            if self.nct == ns.len() {
                return self.on(Pending::CloseSingles(ns));
            }
        }
        NotApplicable
    }

    fn in_seq(&self, m: &Marker) -> bool {
        matches!(self.found.last(), Some(Found::Seq { marker, .. }) if marker.number() == m.number())
    }

    fn delete_simples(&mut self) {
        while let Some(m) = self.left.front() {
            if m.is_simple_child() || matches!(m, Marker::Delim(d) if d.text == "%w") {
                self.left.pop_front();
            } else {
                break;
            }
        }
    }

    fn delete_delim(&mut self, index: usize, word: &str) -> Result<()> {
        let d = match self.left.pop_front() {
            Some(Marker::Delim(d)) => d,
            _ => return Err(internal()),
        };
        self.found.push(Found::Delim(index));
        self.add_prepicked(&d, word);
        Ok(())
    }

    fn add_prepicked(&mut self, d: &Delim, word: &str) {
        let rest: Vec<char> = d.matched_text().chars().skip(word.chars().count()).collect();
        for c in rest.into_iter().rev() {
            self.left.push_front(Marker::Delim(Delim::new(c.to_string())));
        }
    }

    fn pick_all(&self, p: &mut Picker, m: &Marker) -> Result<Found> {
        let (start, end) = p.pick(self.nct)?;
        Ok(Found::Simp { start, end, marker: m.clone() })
    }

    fn pick_singles(&mut self, p: &mut Picker, ms: &[Marker]) -> Result<()> {
        let mut fs = Vec::new();
        for m in ms.iter().rev() {
            let (start, end) = p.pick(1)?;
            fs.push(Found::Simp { start, end, marker: m.clone() });
        }
        fs.reverse();
        self.found.extend(fs);
        Ok(())
    }

    fn pick_all_seq(&mut self, p: &mut Picker, m: &Marker) -> Result<()> {
        let (start, end) = p.pick(self.nct)?;
        if let Some(Found::Seq { marker, args }) = self.found.last_mut() {
            if marker.number() == m.number() {
                args.push((start, end));
                return Ok(());
            }
        }
        self.found.push(Found::Seq { marker: m.clone(), args: vec![(start, end)] });
        Ok(())
    }

    fn seq_done(&mut self, m: &Marker) {
        if !self.in_seq(m) {
            self.found.push(Found::Seq { marker: m.clone(), args: vec![] });
        }
    }

    /// Runs the remembered operation; returns true if no markers are left.
    fn run(&mut self, p: &mut Picker, index: usize, word: &str) -> Result<bool> {
        let pending = self.remember.take().ok_or_else(internal)?;
        match pending {
            Pending::DelimOnly => self.delete_delim(index, word)?,
            Pending::PickAllThenDelim(m) => {
                let f = self.pick_all(p, &m)?;
                self.found.push(f);
                self.left.pop_front();
                self.delete_delim(index, word)?;
            }
            Pending::SinglesThenDelim(ns) => {
                self.pick_singles(p, &ns)?;
                self.delete_simples();
                self.delete_delim(index, word)?;
            }
            Pending::SinglesAllThenDelim(ns) => {
                // ActiveNotation.applicable merges surplus tokens into the last of several adjacent
                // arguments here, but its implementation discards that argument and deletes more
                // markers than it found, so MMT fails; this is reported as an error instead
                let _ = ns;
                return Err(Error::new(ErrorKind::Object, format!("more tokens than arguments before the delimiter {word} (MMT's scanner fails on this input)")));
            }
            Pending::SeqSeparator(m, sep) => {
                self.pick_all_seq(p, &m)?;
                self.add_prepicked(&sep, word);
            }
            Pending::SeqLastThenDelim(m) => {
                self.pick_all_seq(p, &m)?;
                self.left.pop_front();
                self.delete_delim(index, word)?;
            }
            Pending::SeqEmptyThenDelim(m) => {
                self.seq_done(&m);
                self.left.pop_front();
                self.delete_delim(index, word)?;
            }
            Pending::CloseSeqLast(m) => {
                self.pick_all_seq(p, &m)?;
                self.left.pop_front();
            }
            Pending::CloseSeqEmpty(m) => {
                self.seq_done(&m);
                self.left.pop_front();
            }
            Pending::ClosePickAll(m) => {
                let f = self.pick_all(p, &m)?;
                self.found.push(f);
                self.left.pop_front();
            }
            Pending::CloseSingles(ns) => {
                self.pick_singles(p, &ns)?;
                self.delete_simples();
            }
        }
        Ok(self.left.is_empty())
    }

    fn span(&self) -> Result<(usize, usize)> {
        let from = self.found.iter().find_map(|f| f.span().map(|x| x.0)).ok_or_else(internal)?;
        let to = self.found.iter().rev().find_map(|f| f.span().map(|x| x.1)).ok_or_else(internal)?;
        Ok((from, to))
    }
}

/// The token list of a scanner as a gap buffer: `front` holds the elements
/// before the gap in order, `back` the elements after it in reverse order.
/// The scanner reduces only around its current position, so moving the gap
/// there makes a reduction cost the elements it covers, not the length of
/// the list.
struct Tokens {
    front: Vec<Elem>,
    back: Vec<Elem>,
}

impl Tokens {
    fn new(mut elems: Vec<Elem>) -> Tokens {
        elems.reverse();
        Tokens { front: Vec::new(), back: elems }
    }

    fn len(&self) -> usize {
        self.front.len() + self.back.len()
    }

    fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn get(&self, i: usize) -> Option<&Elem> {
        if i < self.front.len() {
            self.front.get(i)
        } else {
            let j = i - self.front.len();
            self.back.len().checked_sub(j + 1).and_then(|k| self.back.get(k))
        }
    }

    /// Moves the gap so that `n` elements are before it.
    fn focus(&mut self, n: usize) {
        while self.front.len() > n {
            if let Some(e) = self.front.pop() {
                self.back.push(e);
            }
        }
        while self.front.len() < n {
            match self.back.pop() {
                Some(e) => self.front.push(e),
                None => break,
            }
        }
    }

    fn into_vec(mut self) -> Vec<Elem> {
        let n = self.len();
        self.focus(n);
        self.front
    }
}

struct Scanner {
    tl: Tokens,
    table: Rc<RuleTable>,
    group: usize,
    ci: usize,
    nct: usize,
    /// Innermost last.
    active: Vec<Active>,
    max_open: usize,
}

impl Scanner {
    /// The single-character tokens directly after the current one, as far as the longest delimiter reaches.
    fn future_tokens(&self) -> String {
        let mut s = String::new();
        let mut i = self.ci + 1;
        let mut n = 0;
        while n < self.table.longest_delim {
            match self.tl.get(i) {
                Some(Elem::Token(t)) if !t.ws_before && t.word.chars().count() == 1 => {
                    s.push_str(&t.word);
                    i += 1;
                    n += 1;
                }
                _ => break,
            }
        }
        s
    }

    fn word(&self) -> String {
        match self.tl.get(self.ci) {
            Some(Elem::Token(t)) => t.word.clone(),
            _ => String::new(),
        }
    }

    fn outer_nct(&mut self) -> &mut usize {
        let n = self.active.len();
        if n == 0 {
            &mut self.nct
        } else {
            &mut self.active[n - 1].nct
        }
    }

    fn advance(&mut self) {
        *self.outer_nct() += 1;
    }

    fn check_active(&mut self, word: &str, future: &str) -> (usize, Applicability) {
        let mut closable = 0;
        for an in self.active.iter_mut().rev() {
            match an.applicable(word, future) {
                Applicable => return (closable, Applicable),
                NotApplicable => {
                    if an.closable() == Applicable {
                        closable += 1;
                    } else {
                        return (closable, NotApplicable);
                    }
                }
            }
        }
        (closable, NotApplicable)
    }

    fn apply_first(&mut self, left_open: bool) -> Result<()> {
        let word = self.word();
        let future = self.future_tokens();
        let n = self.active.len();
        if left_open {
            if n == 1 {
                self.active[0].nct = self.nct;
                self.nct = 0;
            } else {
                self.active[n - 1].nct = self.active[n - 2].nct;
                self.active[n - 2].nct = 0;
            }
            if self.active[n - 1].applicable(&word, &future) != Applicable {
                return Err(internal());
            }
        }
        let mut p = Picker { ci: self.ci, picked: 0 };
        let to_close = self.active[n - 1].run(&mut p, self.ci, &word)?;
        if left_open {
            let rest = self.active[n - 1].nct.checked_sub(p.picked).ok_or_else(internal)? + 1;
            if n == 1 {
                self.nct = rest;
            } else {
                self.active[n - 2].nct = rest;
            }
        }
        self.active[n - 1].nct = 0;
        if to_close {
            self.close_first(false)?;
        }
        Ok(())
    }

    fn close_first(&mut self, right_open: bool) -> Result<()> {
        let word = self.word();
        let mut an = self.active.pop().ok_or_else(internal)?;
        if right_open {
            let mut p = Picker { ci: self.ci, picked: 0 };
            an.run(&mut p, self.ci, &word)?;
        }
        let (from, to) = self.reduce(an)?;
        let nr = to - from;
        self.ci = (self.ci + 1).checked_sub(nr).ok_or_else(internal)?;
        Ok(())
    }

    /// `TokenList.reduce`: replaces the tokens covered by the notation by one matched list.
    fn reduce(&mut self, an: Active) -> Result<(usize, usize)> {
        let (from, to) = an.span()?;
        if to > self.tl.len() || from >= to {
            return Err(internal());
        }
        self.tl.focus(to);
        let pos = self.tl.get(from).ok_or_else(internal)?.pos();
        let mut taken: Vec<Option<Elem>> = self.tl.front.drain(from..).map(Some).collect();
        let mut take = |s: usize, e: usize| -> Result<Unmatched> {
            if s == e {
                return Err(Error::at(ErrorKind::Object, pos, "a notation matched an empty argument"));
            }
            let mut v = Vec::new();
            for i in s..e {
                let el = taken.get_mut(i.checked_sub(from).ok_or_else(internal)?).and_then(Option::take).ok_or_else(internal)?;
                v.push(el);
            }
            Ok(Unmatched { tl: v, table: self.table.clone(), group: self.group })
        };
        let mut tokens = Vec::new();
        for f in &an.found {
            match f {
                Found::Delim(_) => {}
                Found::Simp { start, end, marker } => tokens.push((FoundContent::Simp(marker.clone()), vec![take(*start, *end)?])),
                Found::Seq { marker, args } => {
                    let mut uls = Vec::new();
                    for (s, e) in args {
                        uls.push(take(*s, *e)?);
                    }
                    tokens.push((FoundContent::Seq(marker.clone()), uls));
                }
            }
        }
        let matched = Matched { rules: an.rules, tokens, pos };
        self.tl.front.push(Elem::Matched(Box::new(matched)));
        Ok((from, to))
    }

    fn close_all_possible(&mut self) -> Result<bool> {
        while let Some(an) = self.active.last_mut() {
            if an.closable() == Applicable {
                self.close_first(true)?;
            } else {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn restore(&mut self, an: &Active) {
        self.ci = an.backtrack.0;
        *self.outer_nct() = an.backtrack.1;
    }

    fn scan_group(&mut self) -> Result<()> {
        self.ci = 0;
        self.nct = 0;
        if self.tl.is_empty() {
            return Ok(());
        }
        loop {
            if let Some(Elem::Token(_)) = self.tl.get(self.ci) {
                let word = self.word();
                let future = self.future_tokens();
                let (closable, app) = self.check_active(&word, &future);
                match app {
                    Applicable => {
                        for _ in 0..closable {
                            self.close_first(true)?;
                        }
                        self.apply_first(false)?;
                    }
                    NotApplicable => {
                        let available = match self.active.last() {
                            None => self.nct,
                            Some(a) => a.nct,
                        };
                        let table = self.table.clone();
                        let group = &table.groups[self.group];
                        let mut openable: Vec<Rc<ParsingRule>> = Vec::new();
                        if let Some(c) = word.chars().next() {
                            if let Some(idxs) = group.by_first.get(&c) {
                                for &i in idxs {
                                    let r = &group.rules[i];
                                    let d = r.first_delim.as_ref().map(|d| d.matched_text()).unwrap_or("");
                                    let open = r.open_args;
                                    if matches(d, &word, &future) && (open == 0 || open <= available) {
                                        openable.push(r.clone());
                                    }
                                }
                            }
                        }
                        let longest = openable.iter().map(|r| r.first_delim_len()).max();
                        let longest: Vec<Rc<ParsingRule>> = openable.into_iter().filter(|r| Some(r.first_delim_len()) == longest).collect();
                        if let Some(hd) = longest.first().cloned() {
                            if !longest.iter().all(|r| r.notation.agree(&hd.notation)) {
                                let names: Vec<String> = longest.iter().map(|r| format!("{} (# {})", r.name, r.notation)).collect();
                                let pos = self.tl.get(self.ci).map(Elem::pos).unwrap_or_default();
                                return Err(Error::at(ErrorKind::Ambiguous, pos, format!("multiple notations apply: {}", names.join(", "))));
                            }
                            if hd.notation.is_left_open() {
                                let assoc_left = hd.first_delim.as_ref().map(|d| d.assoc_left).unwrap_or(true);
                                if assoc_left {
                                    for _ in 0..closable {
                                        self.close_first(true)?;
                                    }
                                }
                            }
                            let nct = match self.active.last() {
                                None => self.nct,
                                Some(a) => a.nct,
                            };
                            if self.active.len() >= self.max_open {
                                let pos = self.tl.get(self.ci).map(Elem::pos).unwrap_or_default();
                                return Err(Error::at(ErrorKind::Limit, pos, format!("more than {} notations (brackets included) are open at once", self.max_open)));
                            }
                            self.active.push(Active::new(longest, (self.ci, nct)));
                            self.apply_first(true)?;
                        } else {
                            self.advance();
                        }
                    }
                }
            } else {
                self.advance();
            }
            self.ci += 1;
            if self.ci < self.tl.len() {
                continue;
            }
            if !self.close_all_possible()? {
                let abort = self.active.pop().ok_or_else(internal)?;
                self.restore(&abort);
                self.advance();
                self.ci += 1;
                if self.ci < self.tl.len() {
                    continue;
                }
            }
            break;
        }
        if !self.active.is_empty() {
            let names: Vec<String> = self.active.iter().map(|a| a.rules[0].name.to_string()).collect();
            return Err(Error::at(ErrorKind::Object, self.tl.get(0).map(Elem::pos).unwrap_or_default(), format!("notation left open at the end of the object: {}", names.join(", "))));
        }
        Ok(())
    }
}
