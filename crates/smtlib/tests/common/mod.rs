//! Generators and tool helpers shared by the property tests and the
//! differential tests.
//!
//! `syntax` generates arbitrary values of the syntax types (any symbol, any
//! term shape, any command), for round trips; `deep` generates values far
//! deeper and wider than `syntax`; `sorted` generates the text of scripts
//! that are well sorted by construction, so that a solver that also checks
//! sorts while it parses has nothing but the syntax to object to.

#![allow(dead_code)]

use proptest::prelude::*;
use smtlib::command::{Command, ConstructorDec, DatatypeDec, FunctionDec, FunctionDef, Script, SelectorDec, SortDec};
use smtlib::lexicon::{Binary, Decimal, ExtendedConstant, Hexadecimal, Keyword, Numeral, Reserved, SpecConstant, StringLiteral, Symbol};
use smtlib::response::{CheckSatResponse, GeneralResponse, ModelResponse, SpecificSuccessResponse};
use smtlib::sexpr::{Atom, SExpr};
use smtlib::term::{Attribute, AttributeValue, Identifier, Index, MatchCase, NonEmpty, Pattern, QualIdentifier, Sort, SortedVar, Term, VarBinding};
use std::path::PathBuf;
use std::process::{Command as Process, Stdio};

pub mod syntax {
    use super::*;

    fn non_empty<T: std::fmt::Debug + Clone + 'static>(s: impl Strategy<Value = T> + 'static, max: usize) -> BoxedStrategy<NonEmpty<T>> {
        prop::collection::vec(s, 1..=max).prop_map(|v| NonEmpty::new(v).unwrap()).boxed()
    }

    /// Any symbol: simple-looking names, reserved words, names starting
    /// with digits, names with spaces, quotes, parentheses, line breaks and
    /// non-ASCII characters.
    pub fn symbol() -> BoxedStrategy<Symbol> {
        prop_oneof![
            4 => "[a-zA-Z~!@$%^&*_+=<>.?/-][a-zA-Z0-9~!@$%^&*_+=<>.?/-]{0,5}",
            1 => prop::sample::select(Reserved::ALL.iter().map(|r| r.as_str().to_string()).collect::<Vec<_>>()),
            1 => "[0-9][a-z0-9]{0,3}",
            1 => "[a-z \"'();:#\t\n]{0,6}",
            1 => "[a-zé λ]{1,4}",
            1 => "x'{1,2}",
        ]
        .prop_map(|name: String| Symbol::new(&name).unwrap())
        .boxed()
    }

    pub fn keyword() -> BoxedStrategy<Keyword> {
        "[a-zA-Z0-9~!@$%^&*_+=<>.?/-]{1,6}".prop_map(|n: String| Keyword::new(&n).unwrap()).boxed()
    }

    pub fn numeral() -> BoxedStrategy<Numeral> {
        prop_oneof![any::<u64>().prop_map(Numeral::from), "[1-9][0-9]{20,30}".prop_map(|d: String| Numeral::new(&d).unwrap())].boxed()
    }

    pub fn spec_constant() -> BoxedStrategy<SpecConstant> {
        prop_oneof![
            numeral().prop_map(SpecConstant::Numeral),
            (numeral(), "[0-9]{1,4}").prop_map(|(n, f)| SpecConstant::Decimal(Decimal::from_parts(&n, &f).unwrap())),
            "[0-9a-fA-F]{1,6}".prop_map(|d: String| SpecConstant::Hexadecimal(Hexadecimal::new(&d).unwrap())),
            "[01]{1,8}".prop_map(|d: String| SpecConstant::Binary(Binary::new(&d).unwrap())),
            "[ -~\t\n\ré]{0,8}".prop_map(|s: String| SpecConstant::String(StringLiteral::new(&s).unwrap())),
        ]
        .boxed()
    }

    pub fn atom() -> BoxedStrategy<Atom> {
        prop_oneof![
            spec_constant().prop_map(Atom::Constant),
            symbol().prop_map(Atom::Symbol),
            prop::sample::select(Reserved::ALL.to_vec()).prop_map(Atom::Reserved),
            keyword().prop_map(Atom::Keyword),
        ]
        .boxed()
    }

    pub fn sexpr() -> BoxedStrategy<SExpr> {
        atom().prop_map(SExpr::Atom).prop_recursive(4, 24, 4, |inner| prop::collection::vec(inner, 0..4).prop_map(SExpr::List)).boxed()
    }

    pub fn identifier() -> BoxedStrategy<Identifier> {
        let index = prop_oneof![numeral().prop_map(Index::Numeral), symbol().prop_map(Index::Symbol)];
        prop_oneof![
            3 => symbol().prop_map(Identifier::simple),
            1 => (symbol(), non_empty(index, 3)).prop_map(|(s, i)| Identifier::indexed(s, i)),
        ]
        .boxed()
    }

    pub fn sort() -> BoxedStrategy<Sort> {
        identifier().prop_map(Sort::simple).prop_recursive(3, 12, 3, |inner| (identifier(), non_empty(inner, 3)).prop_map(|(id, args)| Sort::apply(id, args))).boxed()
    }

    pub fn attribute_value() -> BoxedStrategy<AttributeValue> {
        prop_oneof![spec_constant().prop_map(AttributeValue::Constant), symbol().prop_map(AttributeValue::Symbol), prop::collection::vec(sexpr(), 0..3).prop_map(AttributeValue::List)].boxed()
    }

    pub fn attribute() -> BoxedStrategy<Attribute> {
        (keyword(), prop::option::of(attribute_value())).prop_map(|(keyword, value)| match value { Some(v) => Attribute::with_value(keyword, v), None => Attribute::flag(keyword) }).boxed()
    }

    pub fn qual_identifier() -> BoxedStrategy<QualIdentifier> {
        (identifier(), prop::option::weighted(0.2, sort())).prop_map(|(identifier, sort)| match sort { Some(s) => QualIdentifier::annotated(identifier, s), None => QualIdentifier::plain(identifier) }).boxed()
    }

    pub fn sorted_var() -> BoxedStrategy<SortedVar> {
        (symbol(), sort()).prop_map(|(variable, sort)| SortedVar::new(variable, sort)).boxed()
    }

    pub fn term() -> BoxedStrategy<Term> {
        let leaf = prop_oneof![spec_constant().prop_map(Term::Constant), qual_identifier().prop_map(Term::Identifier)];
        leaf.prop_recursive(4, 32, 4, |inner| {
            let pattern = prop_oneof![symbol().prop_map(Pattern::Symbol), Just(Pattern::Wildcard), (symbol(), non_empty(prop::option::weighted(0.8, symbol()), 3)).prop_map(|(c, v)| Pattern::Constructor(c, v))];
            prop_oneof![
                3 => (qual_identifier(), non_empty(inner.clone(), 4)).prop_map(|(q, a)| Term::Application(q, a)),
                1 => (non_empty((symbol(), inner.clone()).prop_map(|(variable, term)| VarBinding::new(variable, term)), 3), inner.clone()).prop_map(|(b, t)| Term::Let(b, Box::new(t))),
                1 => (non_empty(sorted_var(), 3), inner.clone()).prop_map(|(v, t)| Term::Lambda(v, Box::new(t))),
                1 => (non_empty(sorted_var(), 3), inner.clone()).prop_map(|(v, t)| Term::Forall(v, Box::new(t))),
                1 => (non_empty(sorted_var(), 3), inner.clone()).prop_map(|(v, t)| Term::Exists(v, Box::new(t))),
                1 => (inner.clone(), non_empty((pattern, inner.clone()).prop_map(|(pattern, term)| MatchCase::new(pattern, term)), 3)).prop_map(|(t, c)| Term::Match(Box::new(t), c)),
                1 => (inner, non_empty(attribute(), 3)).prop_map(|(t, a)| Term::Annotated(Box::new(t), a)),
            ]
        })
        .boxed()
    }

    /// Terms of a dialect with extended literals and a `choice` binder:
    /// [`term`] with extended literals among the constants and choice
    /// binders among the shapes.
    pub fn dialect_term() -> BoxedStrategy<Term> {
        let extended = prop_oneof![
            numeral().prop_map(ExtendedConstant::NegativeNumeral),
            (numeral(), "[0-9]{1,3}").prop_map(|(n, f)| ExtendedConstant::NegativeDecimal(Decimal::from_parts(&n, &f).unwrap())),
            (any::<bool>(), numeral(), 1u64..1000).prop_map(|(negative, n, d)| ExtendedConstant::fraction(negative, n, Numeral::from(d)).unwrap()),
        ];
        let leaf = prop_oneof![spec_constant().prop_map(Term::Constant), extended.prop_map(|e| Term::Constant(SpecConstant::Extended(e))), qual_identifier().prop_map(Term::Identifier)];
        leaf.prop_recursive(3, 16, 3, |inner| {
            prop_oneof![
                2 => (qual_identifier(), non_empty(inner.clone(), 3)).prop_map(|(q, a)| Term::Application(q, a)),
                1 => (sorted_var(), inner.clone()).prop_map(|(v, t)| Term::Binder(Symbol::new("choice").unwrap(), NonEmpty::one(v), Box::new(t))),
                1 => (non_empty(sorted_var(), 2), inner).prop_map(|(v, t)| Term::Lambda(v, Box::new(t))),
            ]
        })
        .boxed()
    }

    fn function_def() -> BoxedStrategy<FunctionDef> {
        (symbol(), prop::collection::vec(sorted_var(), 0..3), sort(), term()).prop_map(|(name, parameters, sort, body)| FunctionDef::new(name, parameters, sort, body)).boxed()
    }

    fn function_dec() -> BoxedStrategy<FunctionDec> {
        (symbol(), prop::collection::vec(sorted_var(), 0..3), sort()).prop_map(|(name, parameters, sort)| FunctionDec::new(name, parameters, sort)).boxed()
    }

    fn datatype_dec() -> BoxedStrategy<DatatypeDec> {
        let constructor = (symbol(), prop::collection::vec((symbol(), sort()).prop_map(|(symbol, sort)| SelectorDec::new(symbol, sort)), 0..3)).prop_map(|(symbol, selectors)| ConstructorDec::new(symbol, selectors));
        (prop::collection::vec(symbol(), 0..3), non_empty(constructor, 3)).prop_map(|(parameters, constructors)| DatatypeDec::new(parameters, constructors)).boxed()
    }

    pub fn command() -> BoxedStrategy<Command> {
        prop_oneof![
            term().prop_map(Command::Assert),
            Just(Command::CheckSat),
            prop::collection::vec(term(), 0..3).prop_map(Command::CheckSatAssuming),
            symbol().prop_map(Command::DeclareSortParameter),
            (symbol(), sort(), term()).prop_map(|(s, t, b)| Command::DefineConst(s, t, b)),
            (symbol(), sort()).prop_map(|(s, t)| Command::DeclareConst(s, t)),
            (symbol(), datatype_dec()).prop_map(|(s, d)| Command::DeclareDatatype(s, d)),
            non_empty(((symbol(), numeral()).prop_map(|(symbol, arity)| SortDec::new(symbol, arity)), datatype_dec()), 2).prop_map(Command::DeclareDatatypes),
            (symbol(), prop::collection::vec(sort(), 0..3), sort()).prop_map(|(s, a, r)| Command::DeclareFun(s, a, r)),
            (symbol(), numeral()).prop_map(|(s, n)| Command::DeclareSort(s, n)),
            function_def().prop_map(Command::DefineFun),
            function_def().prop_map(Command::DefineFunRec),
            non_empty((function_dec(), term()), 2).prop_map(Command::DefineFunsRec),
            (symbol(), prop::collection::vec(symbol(), 0..3), sort()).prop_map(|(s, p, t)| Command::DefineSort(s, p, t)),
            "[ -~\n]{0,6}".prop_map(|s: String| Command::Echo(StringLiteral::new(&s).unwrap())),
            Just(Command::Exit),
            Just(Command::GetAssertions),
            Just(Command::GetAssignment),
            keyword().prop_map(Command::GetInfo),
            Just(Command::GetModel),
            keyword().prop_map(Command::GetOption),
            Just(Command::GetProof),
            Just(Command::GetUnsatAssumptions),
            Just(Command::GetUnsatCore),
            non_empty(term(), 3).prop_map(Command::GetValue),
            numeral().prop_map(Command::Pop),
            numeral().prop_map(Command::Push),
            Just(Command::Reset),
            Just(Command::ResetAssertions),
            attribute().prop_map(Command::SetInfo),
            symbol().prop_map(Command::SetLogic),
            attribute().prop_map(Command::SetOption),
        ]
        .boxed()
    }

    pub fn script() -> BoxedStrategy<Script> {
        prop::collection::vec(command(), 0..6).prop_map(Script::new).boxed()
    }

    /// Responses. Specific responses whose text is `success`,
    /// `unsupported` or a list headed by `error` are excluded: the reader
    /// gives those their general meaning (see `GeneralResponse::from_spanned_in`).
    pub fn response() -> BoxedStrategy<GeneralResponse> {
        let general_word = |e: &SExpr| match e {
            SExpr::Atom(Atom::Symbol(s)) => s.as_str() == "success" || s.as_str() == "unsupported",
            SExpr::List(items) => matches!(items.first(), Some(SExpr::Atom(Atom::Symbol(s))) if s.as_str() == "error"),
            _ => false,
        };
        let specific = prop_oneof![
            prop::sample::select(vec![CheckSatResponse::Sat, CheckSatResponse::Unsat, CheckSatResponse::Unknown]).prop_map(SpecificSuccessResponse::CheckSat),
            "[ -~]{0,6}".prop_map(|s: String| SpecificSuccessResponse::Echo(StringLiteral::new(&s).unwrap())),
            prop::collection::vec(term(), 0..3).prop_map(SpecificSuccessResponse::GetAssertions),
            prop::collection::vec((symbol(), any::<bool>()), 0..3).prop_map(SpecificSuccessResponse::GetAssignment),
            non_empty(attribute(), 3).prop_map(SpecificSuccessResponse::GetInfo),
            prop::collection::vec(
                prop_oneof![function_def().prop_map(ModelResponse::DefineFun), function_def().prop_map(ModelResponse::DefineFunRec), non_empty((function_dec(), term()), 2).prop_map(ModelResponse::DefineFunsRec)],
                0..3
            )
            .prop_map(SpecificSuccessResponse::GetModel),
            attribute_value().prop_map(SpecificSuccessResponse::GetOption),
            sexpr().prop_map(SpecificSuccessResponse::GetProof),
            prop::collection::vec(term(), 0..3).prop_map(SpecificSuccessResponse::GetUnsatAssumptions),
            prop::collection::vec(symbol(), 0..3).prop_map(SpecificSuccessResponse::GetUnsatCore),
            non_empty((term(), term()), 3).prop_map(SpecificSuccessResponse::GetValue),
        ];
        prop_oneof![
            1 => Just(GeneralResponse::Success),
            1 => Just(GeneralResponse::Unsupported),
            1 => "[ -~]{0,6}".prop_map(|s: String| GeneralResponse::Error(StringLiteral::new(&s).unwrap())),
            8 => specific.prop_filter("reads as a general response", move |r| !general_word(&r.to_sexpr())).prop_map(GeneralResponse::Specific),
        ]
        .boxed()
    }
}

pub mod deep {
    //! Values far deeper or wider than `syntax` builds: chains of one
    //! shape at a chosen depth, and applications with many arguments.

    use super::*;

    fn sym(name: &str) -> Symbol {
        Symbol::new(name).unwrap()
    }

    /// The shapes a chain can nest through.
    #[derive(Debug, Clone, Copy, PartialEq, Eq)]
    pub enum Shape {
        Application,
        Let,
        Forall,
        Lambda,
        Match,
        Annotated,
        Indexed,
        Mixed,
    }

    pub const SHAPES: [Shape; 8] = [Shape::Application, Shape::Let, Shape::Forall, Shape::Lambda, Shape::Match, Shape::Annotated, Shape::Indexed, Shape::Mixed];

    /// How many levels of parentheses one level of `shape` opens around
    /// the term inside it.
    pub fn parens(shape: Shape) -> usize {
        match shape {
            Shape::Application | Shape::Annotated => 1,
            Shape::Indexed => 1,
            Shape::Let | Shape::Match => 3,
            Shape::Forall | Shape::Lambda => 1,
            Shape::Mixed => 3,
        }
    }

    /// A term that nests `depth` levels of `shape`, built bottom-up without
    /// recursion.
    pub fn chain(shape: Shape, depth: usize) -> Term {
        let mut term = Term::symbol(sym("x"));
        for level in 0..depth {
            let shape = if shape == Shape::Mixed { SHAPES[level % 7] } else { shape };
            term = wrap(shape, term);
        }
        term
    }

    fn wrap(shape: Shape, term: Term) -> Term {
        let f = || QualIdentifier::plain(Identifier::simple(sym("f")));
        let int = SortedVar::new(sym("x"), Sort::int());
        match shape {
            Shape::Application | Shape::Mixed => Term::Application(f(), NonEmpty::one(term)),
            Shape::Indexed => Term::Application(QualIdentifier::plain(Identifier::indexed(sym("g"), NonEmpty::one(Index::Numeral(Numeral::from(1u64))))), NonEmpty::one(term)),
            Shape::Let => Term::Let(NonEmpty::one(VarBinding::new(sym("x"), term)), Box::new(Term::symbol(sym("x")))),
            Shape::Forall => Term::Forall(NonEmpty::one(int), Box::new(term)),
            Shape::Lambda => Term::Lambda(NonEmpty::one(int), Box::new(term)),
            Shape::Match => Term::Match(Box::new(Term::symbol(sym("l"))), NonEmpty::one(MatchCase::new(Pattern::Wildcard, term))),
            Shape::Annotated => Term::Annotated(Box::new(term), NonEmpty::one(Attribute::named(sym("n")))),
        }
    }

    /// A sort that nests `depth` levels of `(Array Int …)`.
    pub fn sort_chain(depth: usize) -> Sort {
        let array = Identifier::simple(sym("Array"));
        let mut sort = Sort::int();
        for _ in 0..depth {
            sort = Sort::apply(array.clone(), NonEmpty::new(vec![Sort::int(), sort]).unwrap());
        }
        sort
    }

    /// An S-expression that nests `depth` lists.
    pub fn sexpr_chain(depth: usize) -> SExpr {
        let mut e = SExpr::symbol(sym("a"));
        for _ in 0..depth {
            e = SExpr::List(vec![e, SExpr::symbol(sym("b"))]);
        }
        e
    }

    /// Deep chains of every shape, of depth up to `max` levels of
    /// parentheses.
    pub fn term(max: usize) -> BoxedStrategy<Term> {
        (prop::sample::select(SHAPES.to_vec()), 1..=max).prop_map(|(shape, parens_)| chain(shape, parens_ / parens(shape))).boxed()
    }

    /// Applications with up to `max` arguments: constants, symbols, and
    /// lists of up to `max` sorted variables.
    pub fn wide(max: usize) -> BoxedStrategy<Term> {
        let leaf = prop_oneof![syntax::spec_constant().prop_map(Term::Constant), syntax::symbol().prop_map(Term::symbol)];
        let binder = prop::collection::vec(syntax::symbol(), 1..=max).prop_map(|names| Term::Forall(NonEmpty::new(names.into_iter().map(|n| SortedVar::new(n, Sort::int())).collect()).unwrap(), Box::new(Term::symbol(sym("p")))));
        prop::collection::vec(prop_oneof![20 => leaf, 1 => binder], 1..=max).prop_map(|args| Term::Application(QualIdentifier::plain(Identifier::simple(sym("f"))), NonEmpty::new(args).unwrap())).boxed()
    }
}

pub mod sorted {
    //! The text of scripts in QF_UFLIA that are well sorted by
    //! construction: integer and Boolean constants, an uninterpreted
    //! function, a defined function, linear arithmetic, `let` and `ite`, with
    //! push and pop balanced.

    use super::*;

    const PREAMBLE: &str = "(set-logic QF_UFLIA)\n(declare-const x0 Int)\n(declare-const x1 Int)\n(declare-const |x 2| Int)\n(declare-const b0 Bool)\n(declare-fun f (Int) Int)\n(define-fun g ((a Int) (b Bool)) Int (ite b a (- a)))\n";

    pub fn int(depth: u32) -> BoxedStrategy<String> {
        let leaf = prop_oneof![(0u64..50).prop_map(|n| n.to_string()), (1u64..50).prop_map(|n| format!("(- {n})")), prop::sample::select(vec!["x0", "x1", "|x 2|"]).prop_map(String::from)].boxed();
        if depth == 0 {
            return leaf;
        }
        let sub = int(depth - 1);
        prop_oneof![
            2 => leaf,
            1 => prop::collection::vec(sub.clone(), 2..4).prop_map(|a| format!("(+ {})", a.join(" "))),
            1 => prop::collection::vec(sub.clone(), 1..3).prop_map(|a| format!("(- {})", a.join(" "))),
            1 => ((0u64..9), sub.clone()).prop_map(|(c, t)| format!("(* {c} {t})")),
            1 => sub.clone().prop_map(|t| format!("(f {t})")),
            1 => (sub.clone(), boolean(depth - 1)).prop_map(|(t, b)| format!("(g {t} {b})")),
            1 => (boolean(depth - 1), sub.clone(), sub).prop_map(|(c, t, e)| format!("(ite {c} {t} {e})")),
        ]
        .boxed()
    }

    pub fn boolean(depth: u32) -> BoxedStrategy<String> {
        let leaf = prop_oneof![Just("true".to_string()), Just("false".to_string()), Just("b0".to_string())].boxed();
        if depth == 0 {
            return leaf;
        }
        let sub = boolean(depth - 1);
        let t = int(depth - 1);
        prop_oneof![
            1 => leaf,
            2 => (prop::sample::select(vec!["=", "<", "<=", ">", ">=", "distinct"]), prop::collection::vec(t.clone(), 2..4)).prop_map(|(op, a)| format!("({op} {})", a.join(" "))),
            1 => sub.clone().prop_map(|b| format!("(not {b})")),
            1 => (prop::sample::select(vec!["and", "or", "=>", "xor", "="]), prop::collection::vec(sub.clone(), 2..4)).prop_map(|(op, a)| format!("({op} {})", a.join(" "))),
            1 => (t, sub).prop_map(|(v, b)| format!("(let ((x0 {v})) {b})")),
        ]
        .boxed()
    }

    /// A script: the preamble, then assertions with push, pop and
    /// check-sat among them.
    pub fn script() -> BoxedStrategy<String> {
        prop::collection::vec((boolean(3), 0u8..4), 1..5)
            .prop_map(|asserts| {
                let mut text = PREAMBLE.to_string();
                let mut depth = 0;
                for (formula, action) in asserts {
                    match action {
                        0 => {
                            text.push_str("(push 1)\n");
                            depth += 1;
                        }
                        1 if depth > 0 => {
                            text.push_str("(check-sat)\n(pop 1)\n");
                            depth -= 1;
                        }
                        _ => {}
                    }
                    text.push_str(&format!("(assert {formula})\n"));
                }
                text.push_str("(check-sat)\n");
                text
            })
            .boxed()
    }
}

/// A reference tool: its path and the version it reported.
pub struct Tool {
    pub path: PathBuf,
    pub version: String,
}

/// Finds `name` in the repository's `.tools/bin`, then on `PATH`, runs it
/// with `version_args` and checks that the first line of its answer
/// contains `version`. Panics with what is missing otherwise: a test that
/// calls this never passes without the tool.
pub fn tool(name: &str, version_args: &[&str], version: &str) -> Tool {
    let local = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../.tools/bin").join(name);
    let path = if local.is_file() { local } else { PathBuf::from(name) };
    let output = Process::new(&path).args(version_args).output().unwrap_or_else(|e| panic!("{name} {version} is needed in .tools/bin or on PATH: `{}` cannot be run ({e})", path.display()));
    let text = String::from_utf8_lossy(&output.stdout).into_owned();
    let first = text.lines().next().unwrap_or("").to_string();
    assert!(first.contains(version), "{name} {version} is needed; `{}` reports {first:?}", path.display());
    Tool { path, version: first }
}

pub fn cvc5() -> Tool {
    tool("cvc5", &["--version"], "1.4.2")
}

pub fn z3() -> Tool {
    tool("z3", &["--version"], "4.15.4")
}

impl Tool {
    /// Runs the tool with `args` on `input` (as stdin); returns the exit
    /// status success and the standard output and error.
    pub fn run(&self, args: &[&str], input: &str) -> (bool, String, String) {
        use std::io::Write;
        let mut child = Process::new(&self.path).args(args).stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap_or_else(|e| panic!("cannot run {}: {e}", self.path.display()));
        child.stdin.take().unwrap().write_all(input.as_bytes()).unwrap();
        let output = child.wait_with_output().unwrap();
        (output.status.success(), String::from_utf8_lossy(&output.stdout).into_owned(), String::from_utf8_lossy(&output.stderr).into_owned())
    }
}
