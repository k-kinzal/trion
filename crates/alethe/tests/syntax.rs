//! The concrete syntax (§2.1, Figure 2) at its edges: what reads, what is
//! printed back, what is rejected and where; the constructors; errors;
//! deep input; and the splitting of solver output.

use alethe::{read_output, read_proofs, Anchor, Assume, Command, ContextAssignment, DefineFun, ErrorKind, Proof, SolverResponse, Step};
use smtlib::command::FunctionDef;
use smtlib::lexicon::{Keyword, Numeral, Symbol};
use smtlib::response::CheckSatResponse;
use smtlib::term::{Attribute, AttributeValue, NonEmpty, Sort, SortedVar, Term};

fn err(text: &str) -> alethe::Error {
    Proof::parse(text).expect_err(text)
}

fn at(error: &alethe::Error) -> (usize, usize) {
    let p = error.position().expect("a position");
    (p.line(), p.column())
}

fn round_trip(text: &str) -> Proof {
    let proof = Proof::parse(text).unwrap_or_else(|e| panic!("{text}: {e}"));
    assert_eq!(proof.to_text(), format!("{text}\n"), "the printer gives back the canonical text");
    proof
}

fn sym(s: &str) -> Symbol {
    Symbol::new(s).expect("a symbol")
}

fn term(text: &str) -> Term {
    smtlib::Term::parse(text).expect("an SMT-LIB term")
}

#[test]
fn errors_carry_line_and_column() {
    let e = err("(assume a0 p)\n(step t1 (or p) :rule hole)");
    assert_eq!((e.kind(), at(&e)), (ErrorKind::Syntax, (2, 10)));
    assert!(e.message().contains("(cl …)"), "{e}");
    let e = err("(assume a0 p)\n  (step t1 (cl) :rule)");
    assert_eq!((e.kind(), at(&e)), (ErrorKind::Syntax, (2, 3)));
    let e = err("(assume a0 p))");
    assert_eq!((e.kind(), at(&e)), (ErrorKind::Syntax, (1, 14)));
    let e = err("(assume a0 1abc)");
    assert_eq!((e.kind(), at(&e)), (ErrorKind::Lexical, (1, 12)));
    assert_eq!(err("(assume a0 (f 1/0))").kind(), ErrorKind::Lexical);
    assert_eq!(err("(frob a0 p)").kind(), ErrorKind::Syntax);
    assert_eq!(err("(assume a0 p").kind(), ErrorKind::Syntax);
    let e = err("(step t1 (cl) :rule hole)\n(step t2 (cl (f |-1|)) :rule hole)");
    assert_eq!((e.kind(), at(&e)), (ErrorKind::Syntax, (2, 17)), "the position of the excluded symbol itself");
    let e = err("(step t1 (cl (forall ((x Int)) (lambda ((y Int)) y))) :rule hole)");
    assert_eq!((e.kind(), at(&e)), (ErrorKind::Unsupported, (1, 14)), "the position of the term");
    assert!(std::error::Error::source(&e).is_none() && !e.to_string().is_empty());
}

#[test]
fn the_order_of_the_predefined_annotations_is_strict() {
    round_trip("(step t1 (cl) :rule resolution :premises (a b) :args (1 x) :discharge (c) :extra 1)");
    for text in [
        "(step t1 (cl) :premises (a b) :rule resolution)",
        "(step t1 (cl) :rule resolution :args (1) :premises (a b))",
        "(step t1 (cl) :rule resolution :premises (a) :premises (b))",
        "(step t1 (cl) :rule subproof :discharge (a) :args (1))",
        "(step t1 (cl) :rule resolution :extra 1 :premises (a))",
        "(anchor :args ((x S)) :step t1)",
        "(anchor :step t1 :foo 1 :args ((x S)))",
    ] {
        assert_eq!(err(text).kind(), ErrorKind::Syntax, "{text}");
    }
}

#[test]
fn empty_annotations_are_omitted_not_empty() {
    for text in ["(step t1 (cl) :rule hole :premises ())", "(step t1 (cl) :rule hole :args ())", "(step t1 (cl) :rule subproof :discharge ())", "(anchor :step t1 :args ())"] {
        assert_eq!(err(text).kind(), ErrorKind::Syntax, "{text}");
    }
}

#[test]
fn extra_attributes_are_kept_and_printed() {
    let proof = round_trip("(assume a0 p :origin \"input\" :flag)\n(step t1 (cl p) :rule hole :premises (a0) :note (1 \"two\" :three (4)) :time 1.5 :flag)\n(anchor :step t2 :args ((x U)) :depth 1)");
    match &proof.commands()[1] {
        Command::Step(s) => assert_eq!(s.attributes().len(), 3),
        other => panic!("{other}"),
    }
    match &proof.commands()[0] {
        Command::Assume(a) => assert_eq!(a.attributes().len(), 2),
        other => panic!("{other}"),
    }
}

#[test]
fn rule_names_and_commands() {
    let proof = round_trip("(step t1 (cl (= (let ((x a)) x) a)) :rule let)\n(define-fun f ((x Int) (y Int)) Bool (< x y))\n(define-fun c () Int 3)");
    match &proof.commands()[0] {
        Command::Step(s) => assert_eq!(s.rule().as_str(), "let"),
        other => panic!("{other}"),
    }
    match &proof.commands()[1] {
        Command::DefineFun(d) => assert_eq!(d.definition().parameters().len(), 2),
        other => panic!("{other}"),
    }
    round_trip("(step t1 (cl) :rule |my rule|)");
}

#[test]
fn contexts() {
    let proof = round_trip("(anchor :step t1 :args ((x U) (:= (y U) x) (:= (z Int) (+ 1 -2))))");
    match &proof.commands()[0] {
        Command::Anchor(a) => {
            assert_eq!(a.context().len(), 3);
            assert!(matches!(&a.context()[1], ContextAssignment::Mapping(v, _) if v.variable().as_str() == "y"));
        }
        other => panic!("{other}"),
    }
    let e = err("(anchor :step t1 :args ((:= y x)))");
    assert_eq!(e.kind(), ErrorKind::Syntax);
    assert!(e.message().contains("changelog"), "{e}");
    assert_eq!(err("(anchor :step t1 :args ((:= (y U))))").kind(), ErrorKind::Syntax);
    assert_eq!(err("(anchor :step t1 :args (x))").kind(), ErrorKind::Syntax);
}

/// Figure 2: "A ⟨symbol⟩ is an SMT-LIB ⟨symbol⟩ that is not a
/// −⟨numeral⟩/⟨positive_numeral⟩, −⟨numeral⟩, or −⟨decimal⟩." Unquoted,
/// such a token is a number literal; quoted, it is the excluded symbol.
#[test]
fn number_literals_are_not_symbols() {
    round_trip("(step t1 (cl (= (* -1 x) (- x))) :rule hole :args (-1 -1.5 1/2 -3/4 0.0))");
    round_trip("(step t1 (cl (= -x |-y z|)) :rule hole)");
    for text in ["(assume -1 p)", "(step -1/2 (cl) :rule hole)", "(step t1 (cl) :rule hole :premises (-1))", "(anchor :step t1 :args ((-1 Int)))", "(define-fun -1.0 () Int 1)"] {
        assert_eq!(err(text).kind(), ErrorKind::Syntax, "{text}");
    }
    for text in [
        "(step |-1| (cl) :rule hole)",
        "(step t1 (cl) :rule |-1/2|)",
        "(assume a0 (f |-0.5|))",
        "(assume a0 (! p :named |-1|))",
        "(assume a0 (forall ((|-2| Int)) true))",
        "(assume a0 (let ((|-2| 1)) true))",
        "(assume a0 p :note (a |-3|))",
        "(anchor :step t1 :args ((x |-4|)))",
        "(define-fun f ((x Int)) |-5| 1)",
    ] {
        assert_eq!(err(text).kind(), ErrorKind::Syntax, "{text}");
    }
}

#[test]
fn unsupported_constructs_say_so() {
    // SMT-LIB 2.7 constructs that a ⟨proof_term⟩ (SMT-LIB 2.6, Figure 2) lacks.
    for text in [
        "(assume a0 (lambda ((x Int)) x))",
        "(step t1 (cl (match x ((_ true)))) :rule hole)",
        "(step t1 (cl (match x (((cons _ t) true)))) :rule hole)",
    ] {
        let e = err(text);
        assert_eq!(e.kind(), ErrorKind::Unsupported, "{text}");
        assert!(e.message().contains("SMT-LIB 2.7"), "{e}");
    }
    // `@` and `->` are HO-Core theory symbols, not grammar: symbols in 2.6
    // and 2.7 alike, read and printed back like any other.
    for text in [
        "(step t1 (cl (@ f x)) :rule hole)",
        "(anchor :step t1 :args ((f (-> Int Int))))",
        "(define-fun g ((f (-> Int Int))) Int 0)",
        "(define-fun g () (-> Int Int) f)",
    ] {
        round_trip(text);
    }
}

#[test]
fn the_choice_binder() {
    let proof = round_trip("(step t1 (cl (P (choice ((x U)) (P x)))) :rule hole)");
    let Command::Step(step) = &proof.commands()[0] else { panic!("a step") };
    let Term::Application(_, args) = &step.clause()[0] else { panic!("an application") };
    assert!(matches!(&args[0], Term::Binder(name, vars, _) if name.as_str() == "choice" && vars.len() == 1));
    assert_eq!(err("(step t1 (cl (choice ((x U) (y U)) (P x))) :rule hole)").kind(), ErrorKind::Syntax);
    assert_eq!(err("(step t1 (cl (choice x)) :rule hole)").kind(), ErrorKind::Syntax);
}

/// A proof is solver output and uses the solvers' namespace (§1, §4.1);
/// `@x` and `.x` are simple symbols in every SMT-LIB dialect.
#[test]
fn solver_names_are_symbols() {
    round_trip("(define-fun @d () Bool true)\n(define-fun .e () Bool @d)\n(anchor :step t1 :args ((@x U)))\n(step t1.t0 (cl (= (! (P @x) :named @n) (forall ((.y U)) (P .y)))) :rule hole)\n(step t1 (cl (= @d .e)) :rule bind)");
}

/// §4.1 (pp. 22–24), verbatim from the typeset document's text layer.
const BITBLASTING: [&str; 3] = [
    "In concrete syntax, to avoid name clashes with user defined functions, bbterm is written as @bbterm, bit_of as @bit_of, bvsize as @bvsize, and bv as @bv.",
    "We write (_ @bv𝑛 𝑖 ) for bv𝑖𝑛 , where the space before 𝑛 (in the concrete-syntax term) is omitted for historical reasons.",
    "Each bv𝑖𝑛 is the bitvector constant that represents the bitvector of length 𝑛 that encodes the integer 𝑖. Formally, it corresponds to nat2bv[n](i), where nat2bv is defined as in the SMT-LIB standard.",
];

#[test]
fn the_helper_functions_of_bitblasting() {
    for helper in ["@bbterm", "@bit_of", "@bvsize", "@bv."] {
        assert!(BITBLASTING[0].contains(helper), "{helper}");
    }
    round_trip("(step t1 (cl (= x (@bbterm true false)) ((_ @bit_of 1) x) (= (@bvsize x) 2) (= x (_ @bv2 3))) :rule hole)");
    // BITBLASTING[1], [2]: the suffix of @bv is the length 𝑛, the index is the value 𝑖.
    assert!(BITBLASTING[1].contains("(_ @bv𝑛 𝑖 )") && BITBLASTING[2].contains("of length 𝑛 that encodes the integer 𝑖"));
    let n = |s: &str| Numeral::new(s).expect("a numeral");
    let constant = alethe::term::bv_constant(&n("8"), &n("165"));
    assert_eq!(alethe::term::to_text(&constant), "(_ @bv8 165)");
    assert_eq!(alethe::term::as_bv_constant(&alethe::term::parse("(_ @bv8 165)").expect("reads")), Some((n("8"), n("165"))));
    for other in ["(@bv 165 8)", "(_ bv165 8)", "(_ @bv8 165 1)", "(_ @bvx 1)", "(_ @bv01 1)", "(as (_ @bv8 1) (_ BitVec 8))"] {
        assert_eq!(alethe::term::as_bv_constant(&alethe::term::parse(other).expect(other)), None, "{other}");
    }
}

#[test]
fn constructors_keep_the_grammar() {
    let step = Step::new(sym("t1"), vec![term("(not p)"), term("q")], sym("resolution"))
        .and_then(|s| s.with_premises(NonEmpty::new(vec![sym("a0"), sym("a1")]).expect("premises")))
        .and_then(|s| s.with_args(NonEmpty::one(term("p"))))
        .and_then(|s| s.with_discharge(NonEmpty::one(sym("a0"))))
        .and_then(|s| s.with_attribute(Attribute::with_value(Keyword::new("note").expect("keyword"), AttributeValue::Symbol(sym("x")))))
        .expect("a step");
    let anchor = Anchor::new(sym("t2"))
        .and_then(|a| a.with_context(NonEmpty::new(vec![ContextAssignment::Fixed(SortedVar::new(sym("x"), Sort::named("U").expect("U"))), ContextAssignment::Mapping(SortedVar::new(sym("y"), Sort::named("U").expect("U")), term("x"))]).expect("context")))
        .expect("an anchor");
    let define = DefineFun::new(FunctionDef::new(sym("d"), vec![], Sort::named("Bool").expect("Bool"), term("true"))).expect("a definition");
    let assume = Assume::new(sym("a0"), term("(not p)")).expect("an assumption");
    let proof: Proof = [Command::Assume(assume), Command::DefineFun(define), Command::Anchor(anchor), Command::Step(step)].into_iter().collect();
    assert_eq!(proof.to_text(), "(assume a0 (not p))\n(define-fun d () Bool true)\n(anchor :step t2 :args ((x U) (:= (y U) x)))\n(step t1 (cl (not p) q) :rule resolution :premises (a0 a1) :args (p) :discharge (a0) :note x)\n");
    assert_eq!(Proof::parse(&proof.to_text()).expect("reads back"), proof);

    assert_eq!(Assume::new(sym("-1"), term("p")).expect_err("an excluded index").kind(), ErrorKind::Syntax);
    assert_eq!(Assume::new(sym("a0"), term("(lambda ((x Int)) x)")).expect_err("lambda").kind(), ErrorKind::Unsupported);
    assert_eq!(Step::new(sym("t1"), vec![], sym("-1/2")).expect_err("an excluded rule").kind(), ErrorKind::Syntax);
    let premise = Step::new(sym("t1"), vec![], sym("hole")).expect("a step").with_premises(NonEmpty::one(sym("-2")));
    assert_eq!(premise.expect_err("an excluded premise").kind(), ErrorKind::Syntax);
    for keyword in ["rule", "premises", "args", "discharge"] {
        let attribute = Attribute::flag(Keyword::new(keyword).expect("keyword"));
        assert_eq!(Step::new(sym("t1"), vec![], sym("hole")).expect("a step").with_attribute(attribute).expect_err(keyword).kind(), ErrorKind::Construction);
    }
    let attribute = Attribute::flag(Keyword::new("args").expect("keyword"));
    assert_eq!(Anchor::new(sym("t1")).expect("an anchor").with_attribute(attribute).expect_err("args").kind(), ErrorKind::Construction);
    let two = smtlib::Term::Binder(sym("choice"), NonEmpty::new(vec![SortedVar::new(sym("x"), Sort::named("U").expect("U")), SortedVar::new(sym("y"), Sort::named("U").expect("U"))]).expect("vars"), Box::new(term("true")));
    assert_eq!(Assume::new(sym("a0"), two).expect_err("choice over two").kind(), ErrorKind::Syntax);
    let applied = term("(choice x)");
    assert_eq!(Assume::new(sym("a0"), applied).expect_err("choice applied").kind(), ErrorKind::Syntax);
    let mapped = ContextAssignment::Mapping(SortedVar::new(sym("f"), Sort::named("U").expect("U")), term("(lambda ((x Int)) x)"));
    assert_eq!(Anchor::new(sym("t1")).expect("an anchor").with_context(NonEmpty::one(mapped)).expect_err("lambda").kind(), ErrorKind::Unsupported);
}

/// The nesting limit of the reader: `smtlib`'s default.
fn limit() -> usize {
    alethe::dialect().max_depth()
}

/// Deep input is a typed error, never a stack overflow: the `smtlib`
/// reader rejects nesting beyond its limit, and this crate's checks of
/// terms use `smtlib`'s iterative folds.
#[test]
fn deep_input_is_an_error_not_a_crash() {
    assert_eq!(limit(), smtlib::Dialect::DEFAULT_MAX_DEPTH);
    let depth = 200_000;
    let text = format!("(assume a0 {}p{})", "(not ".repeat(depth), ")".repeat(depth));
    let e = err(&text);
    assert_eq!(e.kind(), ErrorKind::Depth, "{e}");
    assert!(e.position().is_some());
    let unclosed = "(".repeat(depth);
    assert!(Proof::parse(&unclosed).is_err());
    assert!(read_output(&unclosed).is_err());

    let readable = limit() - 1;
    let text = format!("(assume a0 {}p{})", "(not ".repeat(readable), ")".repeat(readable));
    assert_eq!(Proof::parse(&text).expect("within the limit").to_text(), format!("{text}\n"));

    let e = err(&format!("(assume a0 {}p{})", "(not ".repeat(readable + 1), ")".repeat(readable + 1)));
    assert_eq!(e.kind(), ErrorKind::Depth, "one level more");

    // A term built in code, far deeper than the reader admits, is checked
    // and dropped without recursion, and refused.
    let not = || smtlib::term::QualIdentifier::plain(smtlib::term::Identifier::simple(sym("not")));
    let mut deep = term("p");
    for _ in 0..1_000_000 {
        deep = Term::Application(not(), NonEmpty::one(deep));
    }
    assert_eq!(alethe::term::validate(&deep).expect_err("too deep").kind(), ErrorKind::Depth);
    drop(deep);
    // The depth counts every parenthesis the command prints: a term that
    // reads alone may be one level too deep inside a step's clause.
    let mut edge = term("p");
    for _ in 0..limit() - 1 {
        edge = Term::Application(not(), NonEmpty::one(edge));
    }
    alethe::term::validate(&edge).expect("alone, the term nests limit - 1 deep");
    Assume::new(sym("a0"), edge.clone()).expect("inside assume, at the limit");
    assert_eq!(Step::new(sym("t1"), vec![edge], sym("hole")).expect_err("inside (step (cl …)), one level more").kind(), ErrorKind::Depth);
}

#[test]
fn output_is_split_into_answers() {
    let output = "sat\n((define-fun x () Int 1))\nunsat\n(\n(assume a0 p)\n(step t0 (cl) :rule hole :premises (a0))\n)\n(error \"bad\")\nunknown\n";
    let answers: Vec<SolverResponse> = read_output(output).expect("answers").into_iter().map(|(_, a)| a).collect();
    assert_eq!(answers.len(), 6);
    assert!(matches!(&answers[1], SolverResponse::Other(_)), "a model is not a proof");
    assert!(matches!(&answers[3], SolverResponse::Proof(c) if c.len() == 2));
    assert_eq!(answers[4], SolverResponse::Error("bad".to_string()));
    assert_eq!(read_proofs(output).expect_err("the error").kind(), ErrorKind::Output);
    let proofs = read_proofs("unsat\n(\n(assume a0 p)\n)\nunsat\n(\n(assume a0 q)\n)").expect("two proofs");
    assert_eq!(proofs.len(), 2);
    assert_eq!(proofs[1][0].0.line(), 7, "commands keep their position in the output");
    assert_eq!(answers[0], SolverResponse::CheckSat(CheckSatResponse::Sat));
    assert_eq!(answers[5], SolverResponse::CheckSat(CheckSatResponse::Unknown));
    assert!(matches!(&read_output("success").expect("success")[0].1, SolverResponse::Atom(s) if s.as_str() == "success"));
}

/// Responses are not self-describing, and `read_output` classifies them by
/// shape (`output` module documentation): an answer to `get-value` or
/// `get-assertions` about user symbols named `assume` or `step` is taken
/// for a proof. This records exactly when it misreads.
#[test]
fn answers_about_symbols_named_like_proof_commands_are_misread() {
    // `(get-value (assume))` for a constant `assume`: read as a proof, which
    // then fails, at the position of the item.
    let e = read_output("sat\n((assume true))\n").expect_err("taken for a proof");
    assert_eq!(e.kind(), ErrorKind::Syntax);
    assert_eq!(e.position().map(|p| (p.line(), p.column())), Some((2, 2)));
    // `(get-assertions)` after `(assert (assume a0 p))` for a function
    // `assume`: read as a proof of one command.
    let answers = read_output("((assume a0 p))").expect("taken for a proof");
    assert!(matches!(&answers[0].1, SolverResponse::Proof(c) if c.len() == 1));
    // Other heads, or a define-fun alone, are not misread.
    assert!(matches!(&read_output("((anchor true))").expect("anchor alone")[0].1, SolverResponse::Other(_)));
    assert!(matches!(&read_output("((x 1) (assume true))").expect("mixed")[0].1, SolverResponse::Other(_)));
    assert!(matches!(&read_output("((define-fun x () Int 1))").expect("a model")[0].1, SolverResponse::Other(_)));
}

/// An error of the SMT-LIB layer is wrapped once: it keeps its position
/// and message, and the `smtlib` error with its own kind is the source.
#[test]
fn smtlib_errors_are_the_source() {
    let e = err("(assume a0 1abc)");
    let inner = e.smtlib().expect("an smtlib error");
    assert_eq!(inner.kind(), smtlib::ErrorKind::Lexical);
    assert_eq!(inner.position(), e.position());
    let source = std::error::Error::source(&e).expect("a source");
    assert_eq!(source.to_string(), inner.to_string());
    let own = err("(step t1 (or p) :rule hole)");
    assert!(own.smtlib().is_none() && std::error::Error::source(&own).is_none());
}

/// Reading at the depth limit stays within the 2 MiB stack of a spawned
/// thread, the smallest a library user is likely to read on, in the build
/// the tests run in.
#[test]
fn the_depth_limit_fits_a_2_mib_thread() {
    let readable = limit() - 1;
    let text = format!("(assume a0 {}p{})\n", "(not ".repeat(readable), ")".repeat(readable));
    let read = std::thread::Builder::new()
        .stack_size(2 << 20)
        .spawn(move || {
            let proof = Proof::parse(&text).expect("within the limit");
            assert_eq!(proof.to_text(), text);
            let output = format!("unsat\n(\n{text})\n");
            assert_eq!(read_proofs(&output).expect("within the limit").len(), 1);
        })
        .expect("a thread");
    read.join().expect("no stack overflow");
}
