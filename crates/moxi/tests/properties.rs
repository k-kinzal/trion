//! Property tests of the reader and the printer.
//!
//! - Printing is total and reading inverts it: for generated syntax
//!   (scripts of every command and attribute, nested composite systems,
//!   `:query` and `:queries`, and responses of every item including
//!   `:model`; symbols that need quoting, reserved words, primes; every kind
//!   of constant, indexed and annotated identifiers, `let`, quantifiers,
//!   `match` and `:named`, nested sorts), shrinkable by proptest, `parse(print(x)) == x`, and printing the result
//!   again gives the same text. The scripts the differential tests send to
//!   the reference tool (`common::generate`) round-trip too.
//! - Deep and large syntax: terms nested up to the reader's limit read,
//!   print and read back; deeper text is an error with a position, never a
//!   stack overflow; scripts with many commands, variables and arguments
//!   read and print.
//! - The reader returns an error, never panics, on random text and on
//!   generated scripts with text inserted at a random place.

mod common;

use std::str::FromStr;
use moxi::response::{Answer, Certificate, CheckSystemResponse, Model, QueryResult, ResponseItem, State, Trace, Trail, Verbosity};
use moxi::{CheckAttribute, CheckSystem, Command, Condition, ConditionKind, DeclareConst, DefineFun, DefineSort, DefineSystem, ErrorKind, Query, Script, Subsystem};
use proptest::prelude::*;
use smtlib::command::FunctionDef;
use smtlib::lexicon::{Binary, Decimal, ExtendedConstant, Hexadecimal, Numeral, SpecConstant, StringLiteral, Symbol};
use smtlib::response::ModelResponse;
use smtlib::term::{Attribute, Identifier, Index, MatchCase, Pattern, QualIdentifier, SortedVar, VarBinding};
use smtlib::{NonEmpty, Sort, Term};

fn non_empty<T: std::fmt::Debug>(items: impl Strategy<Value = Vec<T>>) -> impl Strategy<Value = NonEmpty<T>> {
    items.prop_map(|v| NonEmpty::new(v).expect("generated non-empty"))
}

/// Symbols: mostly simple ones, some with primes, some that must be
/// printed quoted (spaces, digits first, reserved words, the empty symbol).
fn symbol() -> impl Strategy<Value = Symbol> {
    prop_oneof![
        8 => "[a-z][a-z0-9_.']{0,5}",
        2 => "[ -\\[\\]-{}~é]{0,6}",
        1 => prop::sample::select(vec!["reset", "let", "as", "_", "!", "par", "check-sat", "declare-fun", "'", "x'", "BINARY", "true"]).prop_map(str::to_string),
    ]
    .prop_map(|s| Symbol::new(&s).expect("no | or \\ is generated"))
}

fn numeral() -> impl Strategy<Value = Numeral> {
    "0|[1-9][0-9]{0,24}".prop_map(|s| Numeral::new(&s).expect("a numeral"))
}

fn sort() -> impl Strategy<Value = Sort> {
    let leaf = prop_oneof![
        Just(Sort::bool()),
        Just(Sort::int()),
        symbol().prop_map(|s| Sort::simple(Identifier::simple(s))),
        numeral().prop_map(|n| Sort::simple(Identifier::indexed(Symbol::new("BitVec").unwrap(), NonEmpty::one(Index::Numeral(n))))),
    ];
    leaf.prop_recursive(3, 12, 3, |inner| (symbol(), non_empty(prop::collection::vec(inner, 1..3))).prop_map(|(s, args)| Sort::apply(Identifier::simple(s), args)))
}

fn sorted_var() -> impl Strategy<Value = SortedVar> {
    (symbol(), sort()).prop_map(|(variable, sort)| SortedVar::new(variable, sort))
}

fn term() -> impl Strategy<Value = Term> {
    let leaf = prop_oneof![
        numeral().prop_map(|n| Term::Constant(SpecConstant::Numeral(n))),
        "(0|[1-9][0-9]{0,2})\\.[0-9]{1,3}".prop_map(|d| Term::Constant(SpecConstant::Decimal(Decimal::new(&d).unwrap()))),
        "[0-9a-fA-F]{1,6}".prop_map(|h| Term::Constant(SpecConstant::Hexadecimal(Hexadecimal::new(&h).unwrap()))),
        "[01]{1,8}".prop_map(|b| Term::Constant(SpecConstant::Binary(Binary::new(&b).unwrap()))),
        "[ -~é\n]{0,6}".prop_map(|t| Term::Constant(SpecConstant::String(StringLiteral::new(&t).unwrap()))),
        (symbol(), numeral()).prop_map(|(s, n)| Term::Identifier(QualIdentifier::plain(Identifier::indexed(s, NonEmpty::one(Index::Numeral(n)))))),
        symbol().prop_map(|s| Term::Identifier(QualIdentifier::plain(Identifier::simple(s)))),
        (symbol(), sort()).prop_map(|(s, sort)| Term::Identifier(QualIdentifier::annotated(Identifier::simple(s), sort))),
    ];
    leaf.prop_recursive(6, 48, 4, |inner| {
        prop_oneof![
            4 => (symbol(), non_empty(prop::collection::vec(inner.clone(), 1..4))).prop_map(|(f, args)| Term::Application(QualIdentifier::plain(Identifier::simple(f)), args)),
            1 => (non_empty(prop::collection::vec((symbol(), inner.clone()).prop_map(|(variable, term)| VarBinding::new(variable, term)), 1..3)), inner.clone()).prop_map(|(b, body)| Term::Let(b, Box::new(body))),
            1 => (non_empty(prop::collection::vec(sorted_var(), 1..3)), inner.clone()).prop_map(|(vs, body)| Term::Forall(vs, Box::new(body))),
            1 => (non_empty(prop::collection::vec(sorted_var(), 1..3)), inner.clone()).prop_map(|(vs, body)| Term::Exists(vs, Box::new(body))),
            1 => (inner.clone(), non_empty(prop::collection::vec((pattern(), inner.clone()).prop_map(|(pattern, term)| MatchCase::new(pattern, term)), 1..3))).prop_map(|(t, cases)| Term::Match(Box::new(t), cases)),
            1 => (inner.clone(), symbol()).prop_map(|(t, n)| Term::Annotated(Box::new(t), NonEmpty::one(Attribute::named(n)))),
            1 => (inner.clone(), prop::collection::vec(inner, 1..3)).prop_map(|(t, ps)| Term::Annotated(Box::new(t), NonEmpty::one(Attribute::pattern(ps)))),
        ]
    })
}

/// SMT-LIB 2.6 patterns: a symbol, or a constructor applied to variables.
fn pattern() -> impl Strategy<Value = Pattern> {
    prop_oneof![
        symbol().prop_map(Pattern::Symbol),
        (symbol(), non_empty(prop::collection::vec(symbol().prop_map(Some), 1..3))).prop_map(|(c, vs)| Pattern::Constructor(c, vs)),
    ]
}

fn vars() -> impl Strategy<Value = Option<Vec<SortedVar>>> {
    prop::option::of(prop::collection::vec(sorted_var(), 0..4))
}

fn define_system() -> impl Strategy<Value = DefineSystem> {
    let subsystem = (symbol(), symbol(), prop::collection::vec(symbol(), 0..4)).prop_map(|(n, s, a)| Subsystem::new(n, s, a));
    (symbol(), vars(), vars(), vars(), prop::collection::vec(subsystem, 0..3), prop::option::of(term()), prop::option::of(term()), prop::option::of(term())).prop_map(|(name, input, output, local, subsystems, init, trans, inv)| {
        let mut s = DefineSystem::new(name);
        if let Some(v) = input {
            s = s.with_input(v).expect("generated within the grammar");
        }
        if let Some(v) = output {
            s = s.with_output(v).expect("generated within the grammar");
        }
        if let Some(v) = local {
            s = s.with_local(v).expect("generated within the grammar");
        }
        for sub in subsystems {
            s = s.with_subsystem(sub);
        }
        if let Some(t) = init {
            s = s.with_init(t).expect("generated within the grammar");
        }
        if let Some(t) = trans {
            s = s.with_trans(t).expect("generated within the grammar");
        }
        if let Some(t) = inv {
            s = s.with_inv(t).expect("generated within the grammar");
        }
        s
    })
}

fn query() -> impl Strategy<Value = Query> {
    (symbol(), prop::collection::vec(symbol(), 0..4)).prop_map(|(n, g)| Query::new(n, g))
}

fn check_system() -> impl Strategy<Value = CheckSystem> {
    let kind = prop::sample::select(vec![ConditionKind::Assumption, ConditionKind::Fairness, ConditionKind::Reachable, ConditionKind::Current]);
    let attribute = prop_oneof![
        (kind, symbol(), term()).prop_map(|(k, l, f)| CheckAttribute::Condition(Condition::new(k, l, f).expect("generated within the grammar"))),
        query().prop_map(CheckAttribute::Query),
        non_empty(prop::collection::vec(query(), 1..3)).prop_map(CheckAttribute::Queries),
    ];
    (symbol(), vars(), vars(), vars(), prop::collection::vec(attribute, 0..5)).prop_map(|(name, input, output, local, attributes)| {
        let mut c = CheckSystem::new(name);
        if let Some(v) = input {
            c = c.with_input(v).expect("generated within the grammar");
        }
        if let Some(v) = output {
            c = c.with_output(v).expect("generated within the grammar");
        }
        if let Some(v) = local {
            c = c.with_local(v).expect("generated within the grammar");
        }
        for a in attributes {
            c = c.with_attribute(a);
        }
        c
    })
}

fn function_def() -> impl Strategy<Value = FunctionDef> {
    (symbol(), prop::collection::vec(sorted_var(), 0..3), sort(), term()).prop_map(|(name, parameters, sort, body)| FunctionDef::new(name, parameters, sort, body))
}

fn command() -> impl Strategy<Value = Command> {
    prop_oneof![
        1 => symbol().prop_map(Command::SetLogic),
        1 => (symbol(), numeral()).prop_map(|(s, n)| Command::DeclareSort(s, n)),
        1 => (symbol(), prop::collection::vec(symbol(), 0..3), sort()).prop_map(|(s, ps, t)| Command::DefineSort(DefineSort::new(s, ps, t).expect("generated within the grammar"))),
        1 => (symbol(), sort()).prop_map(|(c, s)| Command::DeclareConst(DeclareConst::new(c, s).expect("generated within the grammar"))),
        1 => function_def().prop_map(|def| Command::DefineFun(DefineFun::new(def).expect("generated within the grammar"))),
        1 => (symbol(), prop::collection::vec(symbol(), 0..4)).prop_map(|(s, v)| Command::DeclareEnumSort(s, v)),
        3 => define_system().prop_map(|s| Command::DefineSystem(Box::new(s))),
        3 => check_system().prop_map(|c| Command::CheckSystem(Box::new(c))),
    ]
}

fn response() -> impl Strategy<Value = CheckSystemResponse> {
    let answer = prop::sample::select(vec![Answer::Sat, Answer::Unsat, Answer::Unknown]);
    let item = prop_oneof![
        (symbol(), answer, prop::option::of(symbol()), prop::option::of(symbol()), prop::option::of(symbol())).prop_map(|(n, r, m, t, c)| {
            let mut q = QueryResult::new(n, r);
            if let Some(m) = m {
                q = q.with_model(m);
            }
            if let Some(t) = t {
                q = q.with_trace(t);
            }
            if let Some(c) = c {
                q = q.with_certificate(c);
            }
            ResponseItem::Query(q)
        }),
        (symbol(), symbol(), symbol()).prop_map(|(n, p, l)| ResponseItem::Trace(Trace::new(n, p, l))),
        (symbol(), prop::collection::vec(function_def().prop_map(ModelResponse::DefineFun), 0..3)).prop_map(|(n, d)| ResponseItem::Model(Model::new(n, d).expect("generated within the grammar"))),
        (symbol(), prop::collection::vec((numeral(), prop::collection::vec((symbol(), term()), 0..3)).prop_map(|(k, a)| State::new(k, a).expect("generated within the grammar")), 0..3)).prop_map(|(n, s)| ResponseItem::Trail(Trail::new(n, s))),
        (symbol(), term(), numeral()).prop_map(|(n, f, k)| ResponseItem::Certificate(Certificate::new(n, f, k).expect("generated within the grammar"))),
    ];
    (prop::sample::select(vec![Verbosity::Full, Verbosity::Compact]), prop::collection::vec(item, 0..6)).prop_map(|(v, items)| CheckSystemResponse::new(v, items))
}

/// A term the MoXI reader cannot produce: an extended constant (`-1`,
/// `1/2`), which would print as `(- 1)` or `(/ 1 2)`, or a binder of another
/// dialect.
fn foreign() -> impl Strategy<Value = Term> {
    prop_oneof![
        prop::sample::select(vec!["-1", "-0.5", "1/2", "-3/4"]).prop_map(|t| Term::Constant(SpecConstant::Extended(ExtendedConstant::parse(t).expect("an extended constant")))),
        (symbol(), sorted_var(), term()).prop_map(|(b, v, body)| Term::Binder(b, NonEmpty::one(v), Box::new(body))),
    ]
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(256))]

    // The printer is total over what the syntax types can hold: a term with
    // a part only another dialect has is refused by every constructor
    // (construction error), and the same term without it is accepted and
    // reads back equal.
    #[test]
    fn foreign_terms_are_refused_and_the_rest_round_trips(base in term(), part in prop::option::of(foreign())) {
        let and = QualIdentifier::plain(Identifier::simple(Symbol::new("and").unwrap()));
        let t = match &part {
            Some(p) => Term::Application(and, NonEmpty::new(vec![base.clone(), p.clone()]).unwrap()),
            None => base,
        };
        let results = [
            DefineSystem::new(Symbol::new("S").unwrap()).with_trans(t.clone()).map(|s| Command::DefineSystem(Box::new(s))),
            Condition::new(ConditionKind::Current, Symbol::new("c").unwrap(), t.clone()).map(|c| Command::CheckSystem(Box::new(CheckSystem::new(Symbol::new("S").unwrap()).with_attribute(CheckAttribute::Condition(c))))),
            DefineFun::new(FunctionDef::new(Symbol::new("f").unwrap(), vec![], Sort::bool(), t.clone())).map(Command::DefineFun),
        ];
        for result in results {
            match (&part, result) {
                (Some(_), Err(e)) => prop_assert_eq!(e.kind(), ErrorKind::Construction),
                (Some(_), Ok(c)) => return Err(TestCaseError::fail(format!("accepted a foreign term: {c}"))),
                (None, Ok(c)) => prop_assert_eq!(Command::from_str(&c.to_string()).unwrap(), c),
                (None, Err(e)) => return Err(TestCaseError::fail(format!("{e}"))),
            }
        }
        let state = State::new(Numeral::new("0").unwrap(), vec![(Symbol::new("x").unwrap(), t)]);
        prop_assert_eq!(state.map_err(|e| e.kind()).err(), part.map(|_| ErrorKind::Construction));
    }

    #[test]
    fn generated_commands_round_trip(commands in prop::collection::vec(command(), 0..6)) {
        let script: Script = commands.into_iter().collect();
        let printed = script.to_string();
        let reread = Script::from_str(&printed).map_err(|e| TestCaseError::fail(format!("{e}\n{printed}")))?;
        prop_assert_eq!(&reread, &script, "{}", printed);
        prop_assert_eq!(reread.to_string(), printed);
        for command in script.commands() {
            prop_assert_eq!(&Command::from_str(&command.to_string()).unwrap(), command);
        }
    }

    #[test]
    fn generated_responses_round_trip(response in response()) {
        let printed = response.to_string();
        let reread = CheckSystemResponse::from_str(&printed).map_err(|e| TestCaseError::fail(format!("{e}\n{printed}")))?;
        prop_assert_eq!(&reread, &response, "{}", printed);
        prop_assert_eq!(reread.to_string(), printed);
    }

    #[test]
    fn generated_script_texts_round_trip(seed in any::<u64>()) {
        let text = common::generate::script(seed).text;
        let parsed = Script::from_str(&text).map_err(|e| TestCaseError::fail(format!("{e}\n{text}")))?;
        let printed = parsed.to_string();
        prop_assert_eq!(&Script::from_str(&printed).unwrap(), &parsed);
    }

    #[test]
    fn the_reader_never_panics(text in "[()a-z0-9:'|!_ \"#;\\\\.é’\\n-]{0,80}") {
        if let Ok(script) = Script::from_str(&text) {
            prop_assert_eq!(Script::from_str(&script.to_string()).unwrap(), script);
        }
        if let Ok(response) = CheckSystemResponse::from_str(&text) {
            prop_assert_eq!(CheckSystemResponse::from_str(&response.to_string()).unwrap(), response);
        }
        let _ = moxi::parse_term(&text);
    }

    #[test]
    fn mangled_scripts_never_panic(seed in any::<u64>(), cut in any::<usize>(), insert in "[()a-z0-9:'| ]{0,6}") {
        let text = common::generate::script(seed).text;
        let mut at = cut % (text.len() + 1);
        while !text.is_char_boundary(at) {
            at -= 1;
        }
        let mangled = format!("{}{insert}{}", &text[..at], &text[at..]);
        if let Ok(parsed) = Script::from_str(&mangled) {
            prop_assert_eq!(Script::from_str(&parsed.to_string()).unwrap(), parsed);
        }
    }
}

/// `(define-system S :init (not … (not x) …))` with `depth` parentheses in
/// all, the command's own included.
fn nested_init(depth: usize) -> String {
    format!("(define-system S :init {}x{})", "(not ".repeat(depth - 1), ")".repeat(depth - 1))
}

/// The deepest nesting of parentheses in `text`, outside string literals and
/// quoted symbols (the printer writes no comments).
fn text_depth(text: &str) -> usize {
    let (mut depth, mut deepest, mut in_string, mut in_quoted) = (0usize, 0usize, false, false);
    for c in text.chars() {
        match c {
            '"' if !in_quoted => in_string = !in_string,
            '|' if !in_string => in_quoted = !in_quoted,
            '(' if !in_string && !in_quoted => {
                depth += 1;
                deepest = deepest.max(depth);
            }
            ')' if !in_string && !in_quoted => depth -= 1,
            _ => {}
        }
    }
    deepest
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(64))]

    // The constructors count the nesting of a term's text as the reader
    // does, for every form the generator makes (let, quantifiers, match,
    // annotations, `as`, indexed identifiers, …): a generated term wrapped
    // in `not`s up to exactly the limit is accepted and reads back, one
    // `not` more is a depth error.
    #[test]
    fn constructors_count_depth_as_the_reader_does(t in term()) {
        let limit = moxi::dialect().max_depth();
        let own = text_depth(&t.to_text(&moxi::dialect()));
        let not = QualIdentifier::plain(Identifier::simple(Symbol::new("not").unwrap()));
        let wrap = |t: Term, n: usize| (0..n).fold(t, |t, _| Term::Application(not.clone(), NonEmpty::one(t)));
        // `(define-system S :init t)`: one parenthesis around the term.
        let fits = limit - 1 - own;
        let system = DefineSystem::new(Symbol::new("S").unwrap()).with_init(wrap(t.clone(), fits)).unwrap();
        let command = Command::DefineSystem(Box::new(system));
        prop_assert_eq!(text_depth(&command.to_string()), limit);
        prop_assert_eq!(Command::from_str(&command.to_string()).unwrap(), command);
        let error = DefineSystem::new(Symbol::new("S").unwrap()).with_init(wrap(t, fits + 1)).unwrap_err();
        prop_assert_eq!(error.kind(), ErrorKind::Depth);
    }
}

// Nesting up to the readers' limit reads, prints, reads back, compares and
// drops on a thread with a 2 MiB stack (the documentation of
// `moxi::dialect`, smtlib's default limit); the same term built with
// constructors is equal.
#[test]
fn deep_terms_within_the_limit_round_trip() {
    std::thread::Builder::new().stack_size(2 << 20).spawn(deep_round_trip).unwrap().join().unwrap();
}

fn deep_round_trip() {
    let limit = moxi::dialect().max_depth();
    let script = Script::from_str(&nested_init(limit)).unwrap();
    assert_eq!(Script::from_str(&script.to_string()).unwrap(), script);
    let not = QualIdentifier::plain(Identifier::simple(Symbol::new("not").unwrap()));
    let mut term = Term::Identifier(QualIdentifier::plain(Identifier::simple(Symbol::new("x").unwrap())));
    for _ in 0..limit - 1 {
        term = Term::Application(not.clone(), NonEmpty::one(term));
    }
    let built = Script::new(vec![Command::DefineSystem(Box::new(DefineSystem::new(Symbol::new("S").unwrap()).with_init(term).unwrap()))]);
    assert_eq!(built, script);
}

// Deeper text is rejected with an error of kind Depth at the
// parenthesis that exceeds the limit, in every reader, however deep.
#[test]
fn nesting_beyond_the_limit_is_an_error() {
    let limit = moxi::dialect().max_depth();
    for depth in [limit + 1, 100_000] {
        let error = Script::from_str(&nested_init(depth)).unwrap_err();
        assert_eq!(error.kind(), ErrorKind::Depth, "{error}");
        assert_eq!((error.position().unwrap().line(), error.position().unwrap().column()), (1, 24 + 5 * (limit - 1)), "{error}");
        let deep_vars = format!("(define-system S :input {}{})", "(".repeat(depth), ")".repeat(depth));
        assert_eq!(Script::from_str(&deep_vars).unwrap_err().kind(), ErrorKind::Depth);
        let response = format!("(check-system-response :verbosity full :certificate (c :inv {}x{} :k 0))", "(not ".repeat(depth), ")".repeat(depth));
        assert_eq!(CheckSystemResponse::from_str(&response).unwrap_err().kind(), ErrorKind::Depth);
        assert_eq!(moxi::parse_term(&format!("{}x{}", "(not ".repeat(depth), ")".repeat(depth))).unwrap_err().kind(), ErrorKind::Depth);
    }
}

// Large but shallow syntax: 10 000 commands, a system with 10 000
// variables and a conjunction of 10 000 arguments read and print.
#[test]
fn large_scripts_read_and_print() {
    let n = 10_000;
    let many: String = (0..n).map(|k| format!("(declare-const c{k} Bool)\n")).collect();
    let script = Script::from_str(&many).unwrap();
    assert_eq!(script.commands().len(), n);
    assert_eq!(script.to_string(), many);
    let vars: String = (0..n).map(|k| format!("(x{k} Bool)")).collect();
    let conjunction: String = (0..n).map(|k| format!(" x{k}")).collect();
    let wide = format!("(define-system S :local ({vars}) :inv (and{conjunction}))");
    let script = Script::from_str(&wide).unwrap();
    let Command::DefineSystem(system) = &script.commands()[0] else { panic!() };
    assert_eq!(system.local().map(<[_]>::len), Some(n));
    assert_eq!(Script::from_str(&script.to_string()).unwrap(), script);
}
