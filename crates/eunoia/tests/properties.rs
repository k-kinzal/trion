//! Property tests.
//!
//! - **Round trip**: for arbitrary abstract syntax (every command and term
//!   form, arbitrary symbol names including those that must be quoted,
//!   literals of every category, strings with quotes), printing and reading
//!   back gives the same value: `parse(print(x)) == x`. Terms are generated up
//!   to depth 8, then wrapped in up to 5 000 further levels of applications,
//!   `let`s, annotations and binders; scripts have up to 64 commands; symbols
//!   are made of any Unicode characters (quoted when they must be).
//! - **Positions**: a script read at an offset ([`eunoia::parse_script_at`])
//!   is the script read alone, with its positions shifted.
//! - **Reader totality**: random text, and printed scripts mangled by
//!   inserting, deleting and swapping characters, are read without a panic;
//!   whatever reads is printed and reads back to the same value.

use eunoia::{parse_script, parse_script_at, parse_term, Annotation, Application, Attribute, Command, ConstructorDec, DatatypeDec, Keyword, LetForm, LetTerm, Literal, LiteralCategory, NonEmpty, Position, ProgramDecl, RuleConclusion, RuleDecl, RulePremises, Script, Step, StrLit, Symbol, Term, TypedParam};
use proptest::prelude::*;

// ------------------------------------------------------------ round trip

fn symbol() -> impl Strategy<Value = Symbol> {
    prop_oneof![
        4 => prop::sample::select(vec!["x", "f", "Int", "@p1", "eo::add", "->", "_", "as", "+", "a.b", "<=", "x1", "Bool", "Type", "true"]).prop_map(|s| Symbol::new(s).unwrap()),
        1 => "[ -{}~]{0,5}".prop_filter_map("not a symbol", |s| Symbol::new(s).ok()),
        1 => "(?s:.{0,5})".prop_filter_map("not a symbol", |s| Symbol::new(s).ok()),
    ]
}

fn keyword() -> impl Strategy<Value = Keyword> {
    prop::sample::select(vec!["list", "type", "implicit", "opaque", "right-assoc-nil", "chainable", "binder", "x-y"]).prop_map(|s| Keyword::new(s).unwrap())
}

fn literal() -> impl Strategy<Value = Literal> {
    prop_oneof![
        any::<i64>().prop_map(|n| Literal::numeral(n as i128)),
        ("-?[0-9]{1,4}", "[0-9]{1,3}").prop_map(|(a, b)| Literal::new(LiteralCategory::Decimal, format!("{a}.{b}")).unwrap()),
        ("-?[0-9]{1,4}", "[1-9][0-9]{0,2}").prop_map(|(a, b)| Literal::new(LiteralCategory::Rational, format!("{a}/{b}")).unwrap()),
        "[01]{1,8}".prop_map(|s| Literal::new(LiteralCategory::Binary, s).unwrap()),
        "[0-9a-fA-F]{1,6}".prop_map(|s| Literal::new(LiteralCategory::Hexadecimal, s).unwrap()),
        "[ -~]{0,6}".prop_map(|s| Literal::string(s).unwrap()),
    ]
}

fn term() -> impl Strategy<Value = Term> {
    let leaf = prop_oneof![symbol().prop_map(Term::Symbol), literal().prop_map(Term::Literal)];
    leaf.prop_recursive(8, 64, 4, |inner| {
        prop_oneof![
            3 => (symbol(), prop::collection::vec(inner.clone(), 1..4)).prop_filter_map("not an application", |(h, args)| Application::new(Term::Symbol(h), args).ok().map(Term::Apply)),
            1 => (prop::sample::select(vec!["_", "as"]), inner.clone(), prop::collection::vec(inner.clone(), 1..3), prop::collection::vec(inner.clone(), 1..3)).prop_filter_map("not a qualified application", |(q, a, b, args)| {
                let mut head_args = vec![a];
                head_args.extend(b);
                let head = Application::new(Term::symbol(q).unwrap(), head_args).ok()?;
                Application::new(Term::Apply(head), args).ok().map(Term::Apply)
            }),
            1 => (symbol(), prop::collection::vec((symbol(), inner.clone()), 1..3), prop::collection::vec(inner.clone(), 1..3)).prop_filter_map("not a binder", |(h, vars, args)| Application::binder(h, vars, args).ok().map(Term::Apply)),
            1 => (any::<bool>(), prop::collection::vec((symbol(), inner.clone()), 1..3), inner.clone()).prop_map(|(d, bindings, body)| Term::Let(LetTerm::new(if d { LetForm::EoDefine } else { LetForm::Let }, bindings, body))),
            1 => (inner.clone(), prop::collection::vec(attribute(inner.clone()), 1..3)).prop_map(|(t, attributes)| Term::Annotated(Annotation::new(t, NonEmpty::from_vec(attributes).unwrap()))),
        ]
    })
}

fn attribute(t: impl Strategy<Value = Term>) -> impl Strategy<Value = Attribute> {
    (keyword(), prop::option::of(t)).prop_map(|(keyword, value)| Attribute { keyword, value })
}

fn param() -> impl Strategy<Value = TypedParam> {
    (symbol(), term(), prop::collection::vec(attribute(term()), 0..2)).prop_map(|(name, ty, attributes)| TypedParam { name, ty, attributes })
}

fn strlit() -> impl Strategy<Value = StrLit> {
    "[ -~]{0,8}".prop_map(|s| StrLit::new(s).unwrap())
}

fn datatype() -> impl Strategy<Value = DatatypeDec> {
    (prop::collection::vec(symbol(), 0..2), prop::collection::vec((symbol(), prop::collection::vec((symbol(), term()), 0..2)), 1..3)).prop_map(|(params, cs)| DatatypeDec { params, constructors: NonEmpty::from_vec(cs.into_iter().map(|(name, selectors)| ConstructorDec { name, selectors }).collect()).unwrap() })
}

fn step() -> impl Strategy<Value = Step> {
    (symbol(), prop::option::of(term()), symbol(), prop::option::of(prop::collection::vec(term(), 0..3)), prop::option::of(prop::collection::vec(term(), 0..3))).prop_map(|(name, conclusion, rule, premises, args)| Step { name, conclusion, rule, premises, args })
}

fn rule() -> impl Strategy<Value = RuleDecl> {
    (
        symbol(),
        prop::collection::vec(param(), 0..3),
        prop::option::of(term()),
        prop::option::of(prop_oneof![prop::collection::vec(term(), 0..3).prop_map(RulePremises::Premises), (term(), term()).prop_map(|(pattern, constructor)| RulePremises::PremiseList { pattern, constructor })]),
        prop::option::of(prop::collection::vec(term(), 0..3)),
        prop::option::of(prop::collection::vec((term(), term()), 0..2)),
        (any::<bool>(), term()).prop_map(|(e, t)| if e { RuleConclusion::Explicit(t) } else { RuleConclusion::Conclusion(t) }),
        prop::collection::vec(Just(Attribute::flag("sorry").unwrap()), 0..2),
    )
        .prop_map(|(name, params, assumption, premises, args, requires, conclusion, attributes)| RuleDecl { name, params, assumption, premises, args, requires, conclusion, attributes })
}

fn command() -> impl Strategy<Value = Command> {
    let attrs = || prop::collection::vec(attribute(term()), 0..2);
    prop_oneof![
        (symbol(), term()).prop_map(|(name, formula)| Command::Assume { name, formula }),
        (symbol(), term()).prop_map(|(name, formula)| Command::AssumePush { name, formula }),
        step().prop_map(Command::Step),
        step().prop_map(Command::StepPop),
        (symbol(), term(), attrs()).prop_map(|(name, ty, attributes)| Command::DeclareConst { name, ty, attributes }),
        (symbol(), prop::collection::vec(param(), 0..3), term(), attrs()).prop_map(|(name, params, ty, attributes)| Command::DeclareParameterizedConst { name, params, ty, attributes }),
        (prop::sample::select(vec![LiteralCategory::Numeral, LiteralCategory::Decimal, LiteralCategory::Rational, LiteralCategory::Binary, LiteralCategory::Hexadecimal, LiteralCategory::String]), term()).prop_map(|(category, ty)| Command::DeclareConsts { category, ty }),
        (symbol(), datatype()).prop_map(|(name, datatype)| Command::DeclareDatatype { name, datatype }),
        prop::collection::vec((symbol(), 0u32..3, datatype()), 1..3).prop_map(Command::DeclareDatatypes),
        (symbol(), any::<u32>()).prop_map(|(name, arity)| Command::DeclareSort { name, arity }),
        rule().prop_map(Command::DeclareRule),
        (symbol(), prop::collection::vec(param(), 0..3), term(), attrs()).prop_map(|(name, params, body, attributes)| Command::Define { name, params, body, attributes }),
        (symbol(), prop::collection::vec(param(), 0..3), prop::collection::vec(term(), 1..3), term(), prop::option::of(prop::collection::vec((term(), term()), 0..3))).prop_map(|(name, params, arg_types, return_type, cases)| Command::Program(ProgramDecl { name, params, arg_types: NonEmpty::from_vec(arg_types).unwrap(), return_type, cases })),
        strlit().prop_map(Command::Include),
        (strlit(), prop::option::of(term())).prop_map(|(file, normalize)| Command::Reference { file, normalize }),
        prop::option::of(strlit()).prop_map(Command::Echo),
        Just(Command::Exit),
        Just(Command::Reset),
        (keyword(), prop::option::of(term())).prop_map(|(keyword, value)| Command::SetOption { keyword, value }),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn terms_round_trip(t in term()) {
        let printed = t.to_string();
        let back = parse_term(&printed);
        prop_assert!(back.is_ok(), "{:?}: {}", back, printed);
        prop_assert_eq!(back.unwrap(), t);
    }

    #[test]
    fn scripts_round_trip(commands in prop::collection::vec(command(), 0..64)) {
        let script = Script::new(commands);
        let printed = script.to_string();
        let back = parse_script(&printed);
        prop_assert!(back.is_ok(), "{:?}: {}", back, printed);
        prop_assert_eq!(back.unwrap(), script);
    }
}

/// How a deep term wraps the one inside it.
#[derive(Debug, Clone, Copy)]
enum Wrap {
    Apply,
    LetBody,
    LetValue,
    Annotate,
    Binder,
}

fn wrap(t: Term, w: Wrap) -> Term {
    let sym = |s: &str| Symbol::new(s).unwrap();
    match w {
        Wrap::Apply => Term::Apply(Application::new(Term::Symbol(sym("f")), vec![t, Term::Symbol(sym("y"))]).unwrap()),
        Wrap::LetBody => Term::Let(LetTerm::new(LetForm::Let, vec![(sym("x"), Term::Symbol(sym("y")))], t)),
        Wrap::LetValue => Term::Let(LetTerm::new(LetForm::EoDefine, vec![(sym("x"), t)], Term::Symbol(sym("x")))),
        Wrap::Annotate => Term::Annotated(Annotation::new(t, NonEmpty::new(Attribute::with_value("named", Term::Symbol(sym("n"))).unwrap()))),
        Wrap::Binder => Term::Apply(Application::binder(sym("lambda"), vec![(sym("x"), t)], vec![Term::Symbol(sym("x"))]).unwrap()),
    }
}

fn deep_term() -> impl Strategy<Value = Term> {
    let w = prop::sample::select(vec![Wrap::Apply, Wrap::LetBody, Wrap::LetValue, Wrap::Annotate, Wrap::Binder]);
    (term(), prop::collection::vec(w, 0..5000)).prop_map(|(t, ws)| ws.into_iter().fold(t, wrap))
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    #[test]
    fn deep_terms_round_trip(t in deep_term()) {
        let printed = t.to_string();
        let back = parse_term(&printed);
        prop_assert!(back.is_ok(), "{:?}", back.map(|_| ()));
        prop_assert_eq!(back.unwrap(), t);
    }

    #[test]
    fn scripts_read_at_an_offset_are_shifted(commands in prop::collection::vec(command(), 1..8), line in 1u32..1000, column in 1u32..1000) {
        let text = Script::new(commands).to_string();
        let alone = parse_script(&text).unwrap();
        let at = parse_script_at(&text, Position::new(line, column)).unwrap();
        prop_assert_eq!(&at, &alone);
        for i in 0..alone.len() {
            let (a, b) = (alone.position(i).unwrap(), at.position(i).unwrap());
            prop_assert_eq!(b.line, a.line + line - 1);
            prop_assert_eq!(b.column, if a.line == 1 { a.column + column - 1 } else { a.column });
        }
    }
}

// ------------------------------------------------------------ reader totality

/// A printed script, mangled by edits at positions chosen by the generator.
fn mangled() -> impl Strategy<Value = String> {
    let edit = (any::<prop::sample::Index>(), 0u8..4, prop::sample::select(vec!['(', ')', '|', '"', ':', ';', ' ', '\n', '#', 'b', 'x', '-', '.', '/', '0', '7', '@', 'é', '_', '!']));
    (prop::collection::vec(command(), 1..5), prop::collection::vec(edit, 0..6)).prop_map(|(commands, edits)| {
        let mut chars: Vec<char> = Script::new(commands).to_string().chars().collect();
        for (at, kind, c) in edits {
            let i = at.index(chars.len() + 1);
            match kind {
                0 => chars.insert(i, c),
                1 if i < chars.len() => {
                    chars.remove(i);
                }
                2 if i + 1 < chars.len() => chars.swap(i, i + 1),
                _ => chars.truncate(i),
            }
        }
        chars.into_iter().collect()
    })
}

/// Reads `text` as a script and as a term; whatever reads must print and
/// read back to the same value.
fn read_without_panic(text: &str) -> Result<(), TestCaseError> {
    if let Ok(script) = parse_script(text) {
        prop_assert_eq!(parse_script(&script.to_string()).ok(), Some(script));
    }
    if let Ok(term) = parse_term(text) {
        prop_assert_eq!(parse_term(&term.to_string()).ok(), Some(term));
    }
    let _ = parse_script_at(text, Position::new(u32::MAX, u32::MAX));
    Ok(())
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(1024))]

    #[test]
    fn random_text_does_not_panic(text in "(?s:.{0,200})") {
        read_without_panic(&text)?;
    }

    #[test]
    fn mangled_scripts_do_not_panic(text in mangled()) {
        read_without_panic(&text)?;
    }
}
