//! Property tests.
//!
//! - **Round trip:** proof terms and commands are generated from parts that
//!   include what the grammar excludes (symbols that spell number literals,
//!   `choice` applied or over several variables, `lambda`, wildcard
//!   patterns, predefined keywords as extra attributes, reserved words and
//!   command names as symbols). The constructors refuse the excluded ones
//!   with a typed error, and for every value they accept — deep ones up to
//!   the nesting limit and proofs of hundreds of commands included —
//!   reading the printed text gives back the same value.
//! - **Depth:** the nesting the constructors count is the nesting of the
//!   printed text: a term wrapped to exactly the reader's limit inside an
//!   `assume` is accepted, and one level more is refused with
//!   [`ErrorKind::Depth`].
//! - **Reader totality:** reading arbitrary text, and printed proofs with
//!   characters deleted, inserted or cut off, returns a value or an error
//!   and never panics.

use alethe::{Anchor, Assume, Command, ContextAssignment, DefineFun, ErrorKind, Proof, Step};
use proptest::prelude::*;
use smtlib::command::FunctionDef;
use smtlib::lexicon::{Decimal, ExtendedConstant, Keyword, Numeral, SpecConstant, StringLiteral, Symbol};
use smtlib::term::{Attribute, AttributeValue, Identifier, Index, MatchCase, NonEmpty, Pattern, QualIdentifier, Sort, SortedVar, Term, VarBinding};

fn config() -> ProptestConfig {
    ProptestConfig { cases: 256, ..ProptestConfig::default() }
}

mod syntax {
    use super::*;
    use smtlib::sexpr::{Atom, SExpr};

    pub(super) fn symbol() -> impl Strategy<Value = Symbol> {
        prop_oneof![
            16 => "[a-zA-Z~!@$%^&*_+=<>.?/-][a-zA-Z0-9~!@$%^&*_+=<>.?/-]{0,6}",
            2 => "[ -\\[\\]-{}~]{0,6}",
            1 => prop::sample::select(vec!["-1", "-1/2", "-0.5", "choice", "cl", "assume", "step", "anchor", "define-fun", "let", "match", "_", "!", "@", "->", "lambda", ":="]).prop_map(str::to_string),
        ]
        .prop_filter_map("a symbol", |s| Symbol::new(&s).ok())
    }

    fn numeral() -> impl Strategy<Value = Numeral> {
        prop_oneof![Just("0".to_string()), "[1-9][0-9]{0,20}"].prop_map(|s| Numeral::new(&s).expect("a numeral"))
    }

    fn decimal() -> impl Strategy<Value = Decimal> {
        (numeral(), "[0-9]{1,5}").prop_map(|(w, f)| Decimal::new(&format!("{}.{f}", w.as_str())).expect("a decimal"))
    }

    pub(super) fn constant() -> impl Strategy<Value = SpecConstant> {
        let nonzero = || numeral().prop_filter("nonzero", |n| n.as_str() != "0");
        prop_oneof![
            numeral().prop_map(SpecConstant::Numeral),
            decimal().prop_map(SpecConstant::Decimal),
            nonzero().prop_map(|n| SpecConstant::Extended(ExtendedConstant::NegativeNumeral(n))),
            decimal().prop_map(|d| SpecConstant::Extended(ExtendedConstant::NegativeDecimal(d))),
            (any::<bool>(), numeral(), nonzero()).prop_map(|(negative, numerator, denominator)| SpecConstant::Extended(ExtendedConstant::fraction(negative, numerator, denominator).expect("a nonzero denominator"))),
            "[ -!#-~]{0,6}".prop_map(|s| SpecConstant::String(StringLiteral::new(&s).expect("a string"))),
            "[0-9a-f]{1,4}".prop_map(|s| SpecConstant::Hexadecimal(smtlib::lexicon::Hexadecimal::new(&s).expect("hex"))),
            "[01]{1,6}".prop_map(|s| SpecConstant::Binary(smtlib::lexicon::Binary::new(&s).expect("binary"))),
        ]
    }

    pub(super) fn sort() -> impl Strategy<Value = Sort> {
        let leaf = prop_oneof![symbol().prop_map(|s| Sort::named(s.as_str()).expect("a sort")), Just(Sort::named("Int").expect("Int"))];
        leaf.prop_recursive(2, 6, 2, |inner| (symbol(), prop::collection::vec(inner, 1..3)).prop_map(|(s, args)| Sort::apply(Identifier::simple(s), NonEmpty::new(args).expect("args"))))
    }

    fn sorted_var() -> impl Strategy<Value = SortedVar> {
        (symbol(), sort()).prop_map(|(variable, sort)| SortedVar::new(variable, sort))
    }

    fn qual_identifier() -> impl Strategy<Value = QualIdentifier> {
        prop_oneof![
            4 => symbol().prop_map(|s| QualIdentifier::plain(Identifier::simple(s))),
            1 => (symbol(), sort()).prop_map(|(s, sort)| QualIdentifier::annotated(Identifier::simple(s), sort)),
            1 => (symbol(), numeral()).prop_map(|(s, n)| QualIdentifier::plain(Identifier::indexed(s, NonEmpty::one(Index::Numeral(n))))),
        ]
    }

    pub(super) fn sexpr() -> impl Strategy<Value = SExpr> {
        let atom = prop_oneof![
            constant().prop_map(|c| SExpr::Atom(Atom::Constant(c))),
            symbol().prop_map(|s| SExpr::Atom(Atom::Symbol(s))),
            Just(SExpr::Atom(Atom::Reserved(smtlib::Reserved::Let))),
            "[a-z]{1,4}".prop_map(|k| SExpr::Atom(Atom::Keyword(Keyword::new(&k).expect("keyword")))),
        ];
        atom.prop_recursive(3, 12, 3, |inner| prop::collection::vec(inner, 0..4).prop_map(SExpr::List))
    }

    pub(super) fn attribute() -> impl Strategy<Value = Attribute> {
        let keyword = prop_oneof![
            4 => "[a-z][a-z0-9-]{0,5}",
            1 => prop::sample::select(vec!["rule", "premises", "args", "discharge", "step", "named", "="]).prop_map(str::to_string),
        ]
        .prop_filter_map("a keyword", |k| Keyword::new(&k).ok());
        let value = prop_oneof![
            Just(None),
            constant().prop_map(|c| Some(AttributeValue::Constant(c))),
            symbol().prop_map(|s| Some(AttributeValue::Symbol(s))),
            prop::collection::vec(sexpr(), 0..3).prop_map(|items| Some(AttributeValue::List(items))),
        ];
        (keyword, value).prop_map(|(keyword, value)| match value {
            Some(value) => Attribute::with_value(keyword, value),
            None => Attribute::flag(keyword),
        })
    }

    pub(super) fn term() -> impl Strategy<Value = Term> {
        let leaf = prop_oneof![constant().prop_map(Term::Constant), qual_identifier().prop_map(Term::Identifier)];
        leaf.prop_recursive(4, 24, 3, |inner| {
            prop_oneof![
                4 => (qual_identifier(), prop::collection::vec(inner.clone(), 1..4)).prop_map(|(q, args)| Term::Application(q, NonEmpty::new(args).expect("args"))),
                1 => (prop::collection::vec((symbol(), inner.clone()), 1..3), inner.clone()).prop_map(|(b, body)| Term::Let(NonEmpty::new(b.into_iter().map(|(variable, term)| VarBinding::new(variable, term)).collect()).expect("bindings"), Box::new(body))),
                1 => (prop::collection::vec(sorted_var(), 1..3), inner.clone()).prop_map(|(v, body)| Term::Forall(NonEmpty::new(v).expect("vars"), Box::new(body))),
                1 => (prop::collection::vec(sorted_var(), 1..3), inner.clone()).prop_map(|(v, body)| Term::Exists(NonEmpty::new(v).expect("vars"), Box::new(body))),
                1 => (prop::collection::vec(sorted_var(), 1..3), inner.clone()).prop_map(|(v, body)| Term::Binder(Symbol::new("choice").expect("choice"), NonEmpty::new(v).expect("vars"), Box::new(body))),
                1 => (inner.clone(), prop::collection::vec(attribute(), 1..3)).prop_map(|(t, a)| Term::Annotated(Box::new(t), NonEmpty::new(a).expect("attributes"))),
                1 => (inner.clone(), prop::collection::vec((pattern(), inner.clone()), 1..3)).prop_map(|(t, cases)| Term::Match(Box::new(t), NonEmpty::new(cases.into_iter().map(|(pattern, term)| MatchCase::new(pattern, term)).collect()).expect("cases"))),
                1 => (prop::collection::vec(sorted_var(), 1..2), inner.clone()).prop_map(|(v, body)| Term::Lambda(NonEmpty::new(v).expect("vars"), Box::new(body))),
            ]
        })
    }

    fn pattern() -> impl Strategy<Value = Pattern> {
        prop_oneof![
            2 => symbol().prop_map(Pattern::Symbol),
            1 => Just(Pattern::Wildcard),
            2 => (symbol(), prop::collection::vec(prop_oneof![4 => symbol().prop_map(Some), 1 => Just(None)], 1..3)).prop_map(|(c, vars)| Pattern::Constructor(c, NonEmpty::new(vars).expect("vars"))),
        ]
    }

    /// A command built with the constructors from generated parts, which
    /// include what the grammar excludes (number-literal symbols, `choice`
    /// applied or over several variables, SMT-LIB 2.7 terms, predefined
    /// keywords as extra attributes); the constructors refuse those.
    pub(super) fn command() -> impl Strategy<Value = alethe::Result<Command>> {
        let terms = || prop::collection::vec(term(), 0..3);
        let symbols = || prop::collection::vec(symbol(), 0..3);
        let attributes = || prop::collection::vec(attribute(), 0..2);
        prop_oneof![
            (symbol(), term(), attributes()).prop_map(|(id, term, attributes)| {
                let assume = Assume::new(id, term)?;
                attributes.into_iter().try_fold(assume, |a, x| a.with_attribute(x)).map(Command::Assume)
            }),
            (symbol(), terms(), symbol(), symbols(), terms(), symbols(), attributes()).prop_map(|(id, clause, rule, premises, args, discharge, attributes)| {
                let mut step = Step::new(id, clause, rule)?;
                if let Some(p) = NonEmpty::new(premises) {
                    step = step.with_premises(p)?;
                }
                if let Some(a) = NonEmpty::new(args) {
                    step = step.with_args(a)?;
                }
                if let Some(d) = NonEmpty::new(discharge) {
                    step = step.with_discharge(d)?;
                }
                attributes.into_iter().try_fold(step, |s, x| s.with_attribute(x)).map(Command::Step)
            }),
            (symbol(), prop::collection::vec(prop_oneof![sorted_var().prop_map(ContextAssignment::Fixed), (sorted_var(), term()).prop_map(|(v, t)| ContextAssignment::Mapping(v, t))], 0..3), attributes()).prop_map(|(step, context, attributes)| {
                let mut anchor = Anchor::new(step)?;
                if let Some(c) = NonEmpty::new(context) {
                    anchor = anchor.with_context(c)?;
                }
                attributes.into_iter().try_fold(anchor, |a, x| a.with_attribute(x)).map(Command::Anchor)
            }),
            (symbol(), prop::collection::vec(sorted_var(), 0..3), sort(), term()).prop_map(|(name, parameters, sort, body)| DefineFun::new(FunctionDef::new(name, parameters, sort, body)).map(Command::DefineFun)),
        ]
    }

    /// The commands the constructors accept among `results`; every refusal
    /// must be a typed error of the grammar.
    pub(super) fn accepted(results: Vec<alethe::Result<Command>>) -> Result<Vec<Command>, TestCaseError> {
        let mut out = Vec::new();
        for r in results {
            match r {
                Ok(c) => out.push(c),
                Err(e) => prop_assert!(matches!(e.kind(), ErrorKind::Syntax | ErrorKind::Unsupported | ErrorKind::Construction), "{e}"),
            }
        }
        Ok(out)
    }

    /// A term nested `depth` levels deep, each level an application of a
    /// generated head, a negation or an annotation.
    pub(super) fn deep_term(max: usize) -> impl Strategy<Value = Term> {
        let name = || prop::sample::select(vec!["f", "g", "not", "@h", "|q s|", "cl", "step"]).prop_map(|s| Symbol::new(s.trim_matches('|')).expect("a symbol"));
        let leaf = prop_oneof![constant().prop_map(Term::Constant), name().prop_map(|s| Term::Identifier(QualIdentifier::plain(Identifier::simple(s))))];
        (prop::collection::vec(prop_oneof![name().prop_map(Some), Just(None)], 1..max), leaf).prop_map(|(levels, leaf)| {
            levels.into_iter().fold(leaf, |inner, level| match level {
                Some(head) => Term::Application(QualIdentifier::plain(Identifier::simple(head)), NonEmpty::new(vec![inner, Term::Constant(SpecConstant::Numeral(Numeral::new("1").expect("1")))]).expect("args")),
                None => Term::Annotated(Box::new(inner), NonEmpty::one(Attribute::flag(Keyword::new("k").expect("k")))),
            })
        })
    }
}


/// The nesting of the printed text of `term`, measured on the text by the
/// `smtlib` reader without a limit.
fn printed_depth(term: &Term) -> usize {
    let text = term.to_sexpr().to_text(alethe::dialect());
    let node = smtlib::sexpr::read(&text, &alethe::dialect().clone().with_max_depth(usize::MAX)).expect("printed text reads");
    let mut deepest = 0;
    let mut stack = vec![(&node, 0)];
    while let Some((node, depth)) = stack.pop() {
        if let Some(items) = node.as_list() {
            deepest = deepest.max(depth + 1);
            stack.extend(items.iter().map(|i| (i, depth + 1)));
        }
    }
    deepest
}

/// Text made of the characters that matter to the reader.
fn noise() -> impl Strategy<Value = String> {
    prop::collection::vec(prop_oneof![
        4 => Just("(".to_string()),
        4 => Just(")".to_string()),
        2 => Just(" ".to_string()),
        1 => Just("\n".to_string()),
        2 => prop::sample::select(vec!["assume", "step", "anchor", "define-fun", "cl", ":rule", ":premises", ":args", ":discharge", ":step", ":=", "choice", "lambda", "let", "forall", "match", "_", "!", ":named", "@", "->", "-1", "1/2", "-0.5", "|-1|", "#b01", "#xAF", "\"s\"", "|q s|", ";c\n", "0", "x", "Int"]).prop_map(str::to_string),
        1 => "[ -~]{1,3}",
    ], 0..60)
    .prop_map(|parts| parts.concat())
}

/// A printed proof with one edit: a character deleted, a character
/// inserted, or the text cut off.
fn mangled() -> impl Strategy<Value = String> {
    (prop::collection::vec(syntax::command(), 1..4), any::<prop::sample::Index>(), prop::sample::select(vec!['(', ')', ' ', '|', '"', ':', '-', '/', '.', '#', ';', 'x']), 0..3u8).prop_map(|(commands, at, c, edit)| {
        let mut text: Vec<char> = Proof::new(commands.into_iter().filter_map(Result::ok).collect()).to_text().chars().collect();
        if text.is_empty() {
            return String::new();
        }
        let i = at.index(text.len());
        match edit {
            0 => {
                text.remove(i);
            }
            1 => text.insert(i, c),
            _ => text.truncate(i),
        }
        text.into_iter().collect()
    })
}

proptest! {
    #![proptest_config(config())]

    #[test]
    fn term_round_trip(t in syntax::term()) {
        match alethe::term::validate(&t) {
            Ok(()) => {
                let text = alethe::term::to_text(&t);
                prop_assert_eq!(alethe::term::parse(&text).map_err(|e| format!("{e}: {text}")), Ok(t));
            }
            Err(e) => prop_assert!(matches!(e.kind(), ErrorKind::Syntax | ErrorKind::Unsupported), "{e}"),
        }
    }

    #[test]
    fn proof_round_trip(commands in prop::collection::vec(syntax::command(), 0..6)) {
        let proof = Proof::new(syntax::accepted(commands)?);
        let text = proof.to_text();
        prop_assert_eq!(Proof::parse(&text).map_err(|e| format!("{e}\n{text}")), Ok(proof));
    }

    #[test]
    fn printing_is_stable_under_whitespace(commands in prop::collection::vec(syntax::command(), 1..4)) {
        let proof = Proof::new(syntax::accepted(commands)?);
        let spaced = proof.to_text().replace(' ', "\n  \t").replace('(', "( ");
        // Spaces inside string literals and quoted symbols change their value; only compare when there are none.
        if !spaced.contains('"') && !spaced.contains('|') {
            prop_assert_eq!(Proof::parse(&spaced).map_err(|e| e.to_string()), Ok(proof));
        }
    }

    #[test]
    fn reading_never_panics(text in noise()) {
        let _ = Proof::parse(&text);
        let _ = alethe::term::parse(&text);
        let _ = alethe::read_output(&text);
    }

    #[test]
    fn reading_mangled_proofs_never_panics(text in mangled()) {
        let _ = Proof::parse(&text);
        let _ = alethe::read_output(&format!("unsat\n(\n{text}\n)\n"));
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 16, ..ProptestConfig::default() })]

    #[test]
    fn the_counted_depth_is_the_printed_depth(t in syntax::term()) {
        prop_assume!(alethe::term::validate(&t).is_ok());
        {
            let not = || QualIdentifier::plain(Identifier::simple(Symbol::new("not").expect("not")));
            // `(assume a0 t)` nests one more than `t`.
            let room = alethe::dialect().max_depth() - 1 - printed_depth(&t);
            let mut wrapped = t;
            for _ in 0..room {
                wrapped = Term::Application(not(), NonEmpty::one(wrapped));
            }
            let a0 = Symbol::new("a0").expect("a0");
            let at_limit = Assume::new(a0.clone(), wrapped.clone()).map_err(|e| e.to_string());
            prop_assert!(at_limit.is_ok(), "{:?}", at_limit);
            let over = Assume::new(a0, Term::Application(not(), NonEmpty::one(wrapped))).map(|_| ()).map_err(|e| e.kind());
            prop_assert_eq!(over, Err(ErrorKind::Depth));
        }
    }

    #[test]
    fn deep_proofs_round_trip(t in syntax::deep_term(alethe::dialect().max_depth() - 3)) {
        let proof = Proof::new(vec![Command::Assume(Assume::new(Symbol::new("a0").expect("a0"), t).expect("an assume"))]);
        let text = proof.to_text();
        prop_assert_eq!(Proof::parse(&text).map_err(|e| e.to_string()), Ok(proof));
    }

    #[test]
    fn large_proofs_round_trip(commands in prop::collection::vec(syntax::command(), 200..400)) {
        let proof = Proof::new(syntax::accepted(commands)?);
        prop_assert!(proof.commands().len() >= 20, "{}", proof.commands().len());
        let text = proof.to_text();
        prop_assert_eq!(Proof::parse(&text).map_err(|e| e.to_string()), Ok(proof));
    }
}
