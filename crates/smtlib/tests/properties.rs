//! Property tests.
//!
//! - The printer and the reader are inverse on every value of the syntax
//!   types (`parse(print(x)) == x`), in the strict dialect and in dialects
//!   with additions, on small values, on chains hundreds of levels deep,
//!   and on applications with thousands of arguments.
//! - The reader is total: random text and mangled scripts give a value or
//!   an error, never a panic, and what it reads prints back to text it
//!   reads to the same value.
//! - Values at the reader's depth limit are read, printed, compared,
//!   cloned, traversed and dropped on a 2 MiB stack; values built through
//!   the API 200 000 levels deep are printed, traversed and dropped there.

mod common;

use common::{deep, syntax};
use proptest::prelude::*;
use smtlib::lexicon::{Dialect, Symbol};
use smtlib::response::{GeneralResponse, ResponseKind};
use smtlib::sexpr::{read, read_all, SExpr, Spanned};
use smtlib::{Command, ErrorKind, Script, Sort, Term};

fn config() -> ProptestConfig {
    ProptestConfig { cases: 256, ..ProptestConfig::default() }
}

/// Runs `f` on a thread with a stack of 2 MiB (the default of a spawned
/// thread) and returns its result; a stack overflow aborts the test.
fn on_small_stack<T: Send + 'static>(f: impl FnOnce() -> T + Send + 'static) -> T {
    std::thread::Builder::new().stack_size(2 << 20).spawn(f).unwrap().join().unwrap()
}

proptest! {
    #![proptest_config(config())]

    #[test]
    fn sexpr_round_trip(e in syntax::sexpr()) {
        let text = e.to_string();
        let read: Vec<SExpr> = read_all(&text, &Dialect::strict()).unwrap().iter().map(Spanned::to_sexpr).collect();
        prop_assert_eq!(&read, &vec![e.clone()]);
        prop_assert_eq!(text.parse::<SExpr>().unwrap(), e);
    }

    #[test]
    fn symbol_round_trip(s in syntax::symbol()) {
        let text = s.to_string();
        prop_assert_eq!(text.parse::<Symbol>().unwrap(), s.clone());
        prop_assert_eq!(Term::parse(&text).unwrap(), Term::symbol(s.clone()));
        // Quoting a symbol that needs no quotes gives the same symbol (§3.1).
        prop_assert_eq!(Term::parse(&format!("|{}|", s.as_str())).unwrap(), Term::parse(&text).unwrap());
        prop_assert_eq!(text.starts_with('|'), !Dialect::strict().is_simple_symbol(s.as_str()));
    }

    #[test]
    fn sort_round_trip(s in syntax::sort()) {
        prop_assert_eq!(s.to_string().parse::<Sort>().unwrap(), s);
    }

    #[test]
    fn term_round_trip(t in syntax::term()) {
        prop_assert_eq!(t.to_string().parse::<Term>().unwrap(), t);
    }

    #[test]
    fn command_round_trip(c in syntax::command()) {
        prop_assert_eq!(c.to_string().parse::<Command>().unwrap(), c);
    }

    #[test]
    fn script_round_trip(s in syntax::script()) {
        prop_assert_eq!(s.to_string().parse::<Script>().unwrap(), s.clone());
        let located = Script::parse_located(&s.to_string(), &Dialect::strict()).unwrap();
        // Each command starts a line (a quoted symbol or a string may hold
        // line breaks, so the lines are not counted).
        prop_assert!(located.iter().all(|(p, _)| p.column() == 1));
        prop_assert!(located.windows(2).all(|w| w[0].0 < w[1].0));
        prop_assert_eq!(located.into_iter().map(|(_, c)| c).collect::<Vec<_>>(), s.commands().to_vec());
    }

    #[test]
    fn response_round_trip(r in syntax::response()) {
        let kind = match &r {
            GeneralResponse::Specific(specific) => specific.kind(),
            _ => ResponseKind::General,
        };
        prop_assert_eq!(GeneralResponse::parse_kind(&r.to_string(), kind, &Dialect::strict()).unwrap(), r);
    }

    // In a dialect with `'` as a symbol character, x' prints unquoted and
    // reads back as the same symbol; the strict dialect quotes it.
    #[test]
    fn dialect_round_trip(t in syntax::term()) {
        let primes = Dialect::strict().with_symbol_char('\'').unwrap();
        prop_assert_eq!(Term::parse_in(&t.to_text(&primes), &primes).unwrap(), t);
    }

    // In a dialect with extended literals and a choice binder, terms that
    // use them print and read back; a symbol spelled like an extended
    // literal is quoted.
    #[test]
    fn extended_dialect_round_trip(t in syntax::dialect_term()) {
        let dialect = Dialect::strict().with_extended_literals().with_binder(Symbol::new("choice").unwrap()).unwrap();
        prop_assert_eq!(Term::parse_in(&t.to_text(&dialect), &dialect).unwrap(), t.clone());
        // The response reader reads terms in the dialect it is given.
        let text = format!("(({} {}))", t.to_text(&dialect), t.to_text(&dialect));
        let value = GeneralResponse::parse_kind(&text, ResponseKind::GetValue, &dialect).unwrap();
        prop_assert_eq!(value.to_text(&dialect), text);
    }

    // Traversal agrees with the structure: the pre-order iterator visits as
    // many terms as the fold counts, and `children` gives the subterms
    // that the fold combines.
    #[test]
    fn traversal_counts_agree(t in syntax::term()) {
        let count = t.fold(|_, children: Vec<usize>| 1 + children.into_iter().sum::<usize>());
        prop_assert_eq!(t.iter().count(), count);
        let first = t.iter().next().unwrap();
        prop_assert!(std::ptr::eq(first, &t));
        // The children appear in the text of the term, in order.
        let text = t.to_string();
        let mut from = 0;
        for child in t.children() {
            let found = text[from..].find(&child.to_string());
            prop_assert!(found.is_some(), "{} not after {} in {}", child, from, text);
            from += found.unwrap_or(0) + 1;
        }
    }

    // Chains of every shape up to 900 levels of parentheses, within the
    // default limit of 1000.
    #[test]
    fn deep_term_round_trip(t in deep::term(900)) {
        prop_assert_eq!(t.to_string().parse::<Term>().unwrap(), t);
    }


    // The reader never panics on arbitrary text; when it reads a script,
    // the script prints back to text that reads to the same script.
    #[test]
    fn reader_is_total(text in "[ -~\n\t\r|\\\\é]{0,80}") {
        if let Ok(script) = Script::parse(&text) {
            prop_assert_eq!(script.to_string().parse::<Script>().unwrap(), script);
        }
        let _ = Term::parse(&text);
        let _ = Sort::parse(&text);
        for kind in [ResponseKind::General, ResponseKind::GetModel, ResponseKind::GetValue, ResponseKind::GetInfo, ResponseKind::GetProof] {
            let _ = GeneralResponse::parse_kind(&text, kind, &Dialect::strict());
        }
        let extended = Dialect::strict().with_extended_literals().with_symbol_char('\'').unwrap();
        if let Ok(script) = Script::parse_in(&text, &extended) {
            prop_assert_eq!(Script::parse_in(&script.to_text(&extended), &extended).unwrap(), script);
        }
    }

    // Printed scripts with characters deleted, duplicated or replaced: the
    // reader gives a script or an error with a position inside the text.
    #[test]
    fn mangled_scripts(s in syntax::script(), edits in prop::collection::vec((any::<prop::sample::Index>(), 0u8..3, prop::sample::select(vec!['(', ')', '|', '"', ' ', ';', ':', '#', '_', '!', 'a', '0'])), 1..6)) {
        let mut chars: Vec<char> = s.to_string().chars().collect();
        for (at, edit, c) in edits {
            if chars.is_empty() {
                chars.push(c);
                continue;
            }
            let i = at.index(chars.len());
            match edit {
                0 => { chars.remove(i); }
                1 => chars.insert(i, chars[i]),
                _ => chars[i] = c,
            }
        }
        let text: String = chars.into_iter().collect();
        match Script::parse(&text) {
            Ok(script) => prop_assert_eq!(script.to_string().parse::<Script>().unwrap(), script),
            Err(e) => {
                let p = e.position().unwrap();
                let lines = text.split('\n').count() + text.matches('\r').count();
                prop_assert!(p.line() <= lines.max(1), "{e} beyond {lines} lines");
            }
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 12, ..ProptestConfig::default() })]

    // Applications with up to 3000 arguments, some of them binders with up
    // to 3000 variables.
    #[test]
    fn wide_term_round_trip(t in deep::wide(3000)) {
        prop_assert_eq!(t.to_string().parse::<Term>().unwrap(), t);
    }
}

#[test]
fn values_are_send_and_sync() {
    fn check<T: Send + Sync + 'static>() {}
    check::<smtlib::Error>();
    check::<Dialect>();
    check::<SExpr>();
    check::<Spanned>();
    check::<Sort>();
    check::<Term>();
    check::<Command>();
    check::<Script>();
    check::<GeneralResponse>();
}

/// The deepest nesting of parentheses in `text` (no string or quoted
/// symbol in it holds a parenthesis).
fn parens_depth(text: &str) -> usize {
    let (mut depth, mut max) = (0usize, 0usize);
    for c in text.chars() {
        match c {
            '(' => {
                depth += 1;
                max = max.max(depth);
            }
            ')' => depth -= 1,
            _ => {}
        }
    }
    max
}

// At the depth limit of the default dialect every shape is read, printed,
// compared, cloned, debug-printed, traversed and dropped on a 2 MiB stack in
// this build (a debug build under `cargo test`); one level more is an error
// of kind Depth at the parenthesis that crosses the limit.
#[test]
fn the_depth_limit_fits_a_small_stack() {
    on_small_stack(|| {
        let limit = Dialect::DEFAULT_MAX_DEPTH;
        for shape in deep::SHAPES {
            // The most levels whose text nests at most `limit` parentheses.
            let (mut low, mut high) = (0, limit);
            while low < high {
                let middle = (low + high).div_ceil(2);
                if parens_depth(&deep::chain(shape, middle).to_string()) <= limit {
                    low = middle;
                } else {
                    high = middle - 1;
                }
            }
            let levels = low;
            let term = deep::chain(shape, levels);
            let text = term.to_string();
            assert!(parens_depth(&text) > limit - 3, "{shape:?}: {}", parens_depth(&text));
            let read = Term::parse(&text).unwrap_or_else(|e| panic!("{shape:?}: {e}"));
            assert!(read == term, "{shape:?}");
            let copy = read.clone();
            assert_eq!(copy.iter().count(), term.iter().count());
            assert_eq!(copy.to_string(), text);
            assert!(format!("{copy:?}").len() > levels);
            drop((read, copy, term));
            let deeper = "(f ".repeat(limit) + "(f x)" + &")".repeat(limit);
            let error = Term::parse(&deeper).unwrap_err();
            assert_eq!((error.kind(), error.position().map(|p| p.column())), (ErrorKind::Depth, Some(3 * limit + 1)), "{error}");
        }
        let sort = deep::sort_chain(limit - 1);
        assert_eq!(sort.to_string().parse::<Sort>().unwrap(), sort);
        let e = deep::sexpr_chain(limit);
        assert_eq!(e.to_string().parse::<SExpr>().unwrap(), e);
        let script = format!("(assert {})", deep::chain(deep::Shape::Application, limit - 1));
        assert_eq!(Script::parse(&script).unwrap().to_string().trim_end(), script);
    });
}

// A smaller limit is honoured exactly.
#[test]
fn a_chosen_depth_limit_is_honoured() {
    let dialect = Dialect::strict().with_max_depth(10);
    let at = "(f ".repeat(10) + "x" + &")".repeat(10);
    assert!(Term::parse_in(&at, &dialect).is_ok());
    let over = format!("(f {at})");
    assert_eq!(Term::parse_in(&over, &dialect).unwrap_err().kind(), ErrorKind::Depth);
    assert_eq!(read(&over, &dialect).unwrap_err().kind(), ErrorKind::Depth);
}

// Values built through the API far deeper than the reader admits are
// printed, traversed, folded and dropped without recursion.
#[test]
fn values_built_deeper_than_the_reader_admits() {
    on_small_stack(|| {
        const DEPTH: usize = 200_000;
        for shape in deep::SHAPES {
            let term = deep::chain(shape, DEPTH);
            let text = term.to_string();
            assert!(text.len() > DEPTH, "{shape:?}");
            assert_eq!(term.iter().count(), term.fold(|_, c: Vec<usize>| 1 + c.into_iter().sum::<usize>()), "{shape:?}");
            assert_eq!(term.to_sexpr().to_string(), text);
            assert_eq!(Term::parse(&text).unwrap_err().kind(), ErrorKind::Depth);
            drop(term);
        }
        let sort = deep::sort_chain(DEPTH);
        assert_eq!(sort.fold(|_, c: Vec<usize>| 1 + c.into_iter().max().unwrap_or(0)), DEPTH + 1);
        assert!(sort.to_string().len() > DEPTH);
        drop(sort);
        let e = deep::sexpr_chain(DEPTH);
        let text = e.to_string();
        assert!(text.len() > DEPTH);
        let spanned = e.to_spanned(smtlib::Position::START);
        assert!(spanned.describe().ends_with("..."));
        drop((e, spanned));
    });
}
