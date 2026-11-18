//! Examples quoted from The SMT-LIB Standard, Version 2.7 (release
//! 2026-09-09), section by section. Each test cites the section and the
//! page (as printed in the page header) its text comes from. The examples
//! are transcribed from the typeset PDF: its text layer inserts spaces
//! inside some tokens (`# x0` for `#x0`, `: named` for `:named`,
//! `declare - sort - parameter` for `declare-sort-parameter`, `" out "`
//! for `"out"`), which are removed here; nothing else is changed unless a
//! test says so.
//!
//! The crate models the grammar, so each example is read, printed, and read
//! back to the same value; whether an example is well sorted or inside its
//! logic is not checked here (the reference's remarks on that are quoted
//! where a test reads an ill-sorted example, which the grammar admits).

use smtlib::command::Command;
use smtlib::lexicon::{Dialect, Reserved, SpecConstant, Symbol};
use smtlib::response::{GeneralResponse, ResponseKind, SpecificSuccessResponse};
use smtlib::sexpr::{read_all, Atom, SExpr, Spanned};
use smtlib::term::{Attribute, Identifier, Sort, Term};
use smtlib::{ErrorKind, Script};

/// The atoms of `text`, which holds only atoms.
fn kinds(text: &str) -> Vec<Atom> {
    read_all(text, &Dialect::strict()).unwrap().iter().map(|n| n.as_atom().cloned().unwrap_or_else(|| panic!("{text}: not an atom"))).collect()
}

fn round_trip_term(text: &str) -> Term {
    let term = Term::parse(text).unwrap_or_else(|e| panic!("{text}: {e}"));
    assert_eq!(Term::parse(&term.to_string()).unwrap(), term, "{text}");
    term
}

fn round_trip_script(text: &str) -> Script {
    let script = Script::parse(text).unwrap_or_else(|e| panic!("{text}: {e}"));
    assert_eq!(Script::parse(&script.to_string()).unwrap(), script, "{text}");
    script
}

/// Reads `text` as S-expressions and checks that their print reads back to
/// the same S-expressions.
fn round_trip_sexprs(text: &str) -> Vec<SExpr> {
    let exprs: Vec<SExpr> = read_all(text, &Dialect::strict()).unwrap_or_else(|e| panic!("{text}: {e}")).iter().map(Spanned::to_sexpr).collect();
    let printed: Vec<String> = exprs.iter().map(SExpr::to_string).collect();
    let again: Vec<SExpr> = read_all(&printed.join(" "), &Dialect::strict()).unwrap().iter().map(Spanned::to_sexpr).collect();
    assert_eq!(again, exprs, "{text}");
    exprs
}

// §3.1 Lexicon, page 23: "#x0 #xA04 #x01Ab #x61ff".
#[test]
fn s3_1_hexadecimals() {
    for text in ["#x0", "#xA04", "#x01Ab", "#x61ff"] {
        match kinds(text).as_slice() {
            [Atom::Constant(c @ SpecConstant::Hexadecimal(_))] => assert_eq!(c.to_string(), text),
            other => panic!("{text}: {other:?}"),
        }
    }
}

// §3.1, page 23: "#b0 #b1 #b001 #b101011".
#[test]
fn s3_1_binaries() {
    for text in ["#b0", "#b1", "#b001", "#b101011"] {
        match kinds(text).as_slice() {
            [Atom::Constant(c @ SpecConstant::Binary(_))] => assert_eq!(c.to_string(), text),
            other => panic!("{text}: {other:?}"),
        }
    }
}

// §3.1, pages 23–24: the four string literal examples, and the remark that
// "" is the only escape sequence.
#[test]
fn s3_1_string_literals() {
    let cases = [
        ("\"this is a string literal\"", "this is a string literal"),
        ("\"\"", ""),
        ("\"She said: \"\"Bye bye\"\" and left.\"", "She said: \"Bye bye\" and left."),
        ("\"this is a string literal\nwith a line break in it\"", "this is a string literal\nwith a line break in it"),
        ("\"\\n\"", "\\n"),
    ];
    for (text, content) in cases {
        match kinds(text).as_slice() {
            [Atom::Constant(c @ SpecConstant::String(s))] => {
                assert_eq!(s.as_str(), content);
                assert_eq!(c.to_string(), text);
            }
            other => panic!("{text}: {other:?}"),
        }
    }
}

// §3.1, page 24: the basic set of reserved words (2.7 adds `lambda`), and
// command names (2.7 adds `declare-sort-parameter` and `define-const`).
#[test]
fn s3_1_reserved_words() {
    let basic = "BINARY DECIMAL HEXADECIMAL NUMERAL STRING _ ! as lambda let exists forall match par set-logic set-option";
    for kind in kinds(basic) {
        assert!(matches!(kind, Atom::Reserved(_)), "{kind:?}");
    }
    assert_eq!(kinds("define-funs-rec"), vec![Atom::Reserved(Reserved::DefineFunsRec)]);
    assert_eq!(kinds("lambda"), vec![Atom::Reserved(Reserved::Lambda)]);
    assert_eq!(kinds("declare-sort-parameter"), vec![Atom::Reserved(Reserved::DeclareSortParameter)]);
    assert_eq!(kinds("define-const"), vec![Atom::Reserved(Reserved::DefineConst)]);
}

// §3.1, page 24: simple symbols "+ <= x plus ** $ <sas <adf>" and
// "abc77 *$s&6 .kkk .8 +34 -32".
#[test]
fn s3_1_simple_symbols() {
    let text = "+ <= x plus ** $ <sas <adf> abc77 *$s&6 .kkk .8 +34 -32";
    let expected: Vec<&str> = text.split(' ').collect();
    let found = kinds(text);
    assert_eq!(found.len(), expected.len());
    for (kind, name) in found.iter().zip(expected) {
        assert_eq!(kind, &Atom::Symbol(Symbol::new(name).unwrap()));
        assert_eq!(Symbol::new(name).unwrap().to_string(), name, "a simple symbol prints unquoted");
    }
}

// §3.1, page 24: quoted symbols.
#[test]
fn s3_1_quoted_symbols() {
    let cases = [
        ("|this is a quoted symbol|", "this is a quoted symbol"),
        ("|so is\n this one|", "so is\n this one"),
        ("||", ""),
        ("| \" can occur too|", " \" can occur too"),
        ("|af klj^*0asfe2(&*)&(#^$>>>?\"']]984|", "af klj^*0asfe2(&*)&(#^$>>>?\"']]984"),
    ];
    for (text, name) in cases {
        assert_eq!(kinds(text), vec![Atom::Symbol(Symbol::new(name).unwrap())], "{text}");
        assert_eq!(Symbol::new(name).unwrap().to_string(), text, "a non-simple symbol prints quoted");
    }
}

// §3.1, page 25: "abc and |abc| are the same symbol"; footnote 4: "|@abc|
// and |.abc| … are considered the same as @abc and .abc".
#[test]
fn s3_1_quoting_a_simple_symbol_gives_the_same_symbol() {
    assert_eq!(kinds("abc"), kinds("|abc|"));
    assert_eq!(kinds("@abc"), kinds("|@abc|"));
    assert_eq!(kinds(".abc"), kinds("|.abc|"));
    assert_eq!(Term::parse("|abc|").unwrap(), Term::parse("abc").unwrap());
    // A quoted reserved word is a symbol, printed quoted.
    assert_eq!(kinds("|as|"), vec![Atom::Symbol(Symbol::new("as").unwrap())]);
    assert_eq!(Symbol::new("as").unwrap().to_string(), "|as|");
}

// §3.1, page 25: keywords ":date :a2 :foo-bar :<= :56 :->".
#[test]
fn s3_1_keywords() {
    let names = ["date", "a2", "foo-bar", "<=", "56", "->"];
    let found = kinds(":date :a2 :foo-bar :<= :56 :->");
    for (kind, name) in found.iter().zip(names) {
        match kind {
            Atom::Keyword(k) => assert_eq!(k.name(), name),
            other => panic!("{other:?}"),
        }
    }
}

// §3.3, page 26: identifiers.
#[test]
fn s3_3_identifiers() {
    for text in ["plus", "+", "<=", "Real", "|John Brown|", "(_ vector-add 4 5)", "(_ BitVec 32)", "(_ move up)", "(_ move down)", "(_ move left)", "(_ move right)"] {
        let node = smtlib::sexpr::read(text, &Dialect::strict()).unwrap();
        let id = Identifier::from_spanned(&node).unwrap_or_else(|e| panic!("{text}: {e}"));
        assert_eq!(id.to_string(), text);
    }
}

// §3.4, page 27: attributes.
#[test]
fn s3_4_attributes() {
    let text = "(! true :left-assoc :status unsat :my_attribute (humpty dumpty) :authors \"Jack and Jill\")";
    let term = Term::parse(text).unwrap();
    let Term::Annotated(_, attributes) = &term else { panic!() };
    let shown: Vec<String> = attributes.iter().map(Attribute::to_string).collect();
    assert_eq!(shown, [":left-assoc", ":status unsat", ":my_attribute (humpty dumpty)", ":authors \"Jack and Jill\""]);
}

// §3.5, page 27: sorts, with the map sorts 2.7 adds.
#[test]
fn s3_5_sorts() {
    for text in ["Int", "Bool", "(_ BitVec 3)", "(List (Array Int Real))", "((_ FixedSizeList 4) Real)", "(Set (_ Bitvec 3))", "(-> Int Real)", "(-> Int (-> Int Real))"] {
        let sort = Sort::parse(text).unwrap_or_else(|e| panic!("{text}: {e}"));
        assert_eq!(sort.to_string(), text);
    }
    // -> is :right-assoc (§3.9), a rule of the theory, not of the grammar:
    // the two spellings are two sorts here.
    assert_ne!(Sort::parse("(-> Int Int Real)").unwrap(), Sort::parse("(-> Int (-> Int Real))").unwrap());
    // ⟨sort⟩ ::= ( ⟨identifier⟩ ⟨sort⟩+ ): no empty argument list.
    assert_eq!(Sort::parse("(List)").unwrap_err().kind(), ErrorKind::Syntax);
}

// §3.5, page 28: the numbered script on sort parameters. (Its logic
// QF_UFLIA is quantifier free, a rule of the logic, outside the grammar.)
const S3_5_SCRIPT: &str = "(set-logic QF_UFLIA)
(declare-sort-parameter X)
(declare-fun f (X) X)
(assert (forall ((x X)) (not (= (f x) x))))
(declare-sort A 0)
(assert (forall ((x X)) (not (= (f (f x)) x))))
(check-sat)
(declare-sort B 0)
(check-sat)";

#[test]
fn s3_5_sort_parameters() {
    let script = round_trip_script(S3_5_SCRIPT);
    assert_eq!(script.commands().len(), 9);
    assert!(matches!(&script.commands()[1], Command::DeclareSortParameter(x) if x.as_str() == "X"));
}

const LIST: &str = "(set-logic ALL) (declare-datatype List (par (E) ((nil) (cons (head E) (tail (List E))))))";

// §3.6, page 30: the append axiom.
#[test]
fn s3_6_terms() {
    let axiom = "(forall ((x (List Int)) (y (List Int)))
           (= (append x y)
              (ite (= x (as nil (List Int)))
                   y
                   (let ((h (head x)) (t (tail x)))
                     (insert h (append t y))))))";
    let term = round_trip_term(axiom);
    assert!(matches!(term, Term::Forall(ref vars, _) if vars.len() == 2));
    round_trip_script(&format!("{LIST} (declare-fun append ((List Int) (List Int)) (List Int)) (declare-fun insert (Int (List Int)) (List Int)) (assert {axiom})"));
}

// §3.6.1, page 31: let does not make its variables polymorphic. The first
// assert of the verbatim script closes `and` after one argument and so
// gives assert two arguments, which is not a command (a typo in the
// reference); with the parenthesis moved to make the `=` the second
// conjunct, the text is read. The last two asserts are ill sorted, as the
// reference says; the grammar admits them.
#[test]
fn s3_6_1_let_is_monomorphic() {
    let verbatim = "(declare-sort-parameter X)
(declare-const a (Array Int X))
(assert
  (and (> (select (as a (Array Int Int)) 3) 0))
       (= (select (as a (Array Int String)) 3) \"out\"))";
    let error = Script::parse(verbatim).unwrap_err();
    assert_eq!(error.kind(), ErrorKind::Syntax);
    assert_eq!(error.position().map(|p| p.line()), Some(3), "{error}");
    let fixed = verbatim.replace("3) 0))\n", "3) 0)\n").replace("\"out\"))", "\"out\")))");
    round_trip_script(&fixed);
    let third = "(assert
  ; ill sorted!
  (let ((b (as a (Array Int X))))
    (< (select (as b (Array Int Int)) 3) 0)))";
    let fourth = "(assert
  ; ill sorted!
  (let ((id (lambda ((x X)) x)))
    (= 1 (id 1))))";
    for ill in [third, fourth] {
        round_trip_script(ill);
    }
}

// §3.6.1, page 32: the match axioms for append (version 2 with the
// wildcard `_`) and length.
#[test]
fn s3_6_1_match() {
    let axioms = [
        "(forall ((l1 (List Int)) (l2 (List Int)))
           (= (append l1 l2)
              (match l1 (
                 (nil l2)
                 ((cons h t) (cons h (append t l2)))))))",
        "(forall ((l1 (List Int)) (l2 (List Int)))
           (= (append l1 l2)
              (match l1 (
                 ((cons h t) (cons h (append t l2)))
                 (_ l2)))))",
        "(forall ((l (List Int)))
           (= (length l)
              (match l (
                 (nil 0)
                 ((cons _ t) (+ 1 (length t)))))))",
    ];
    for axiom in axioms {
        round_trip_term(axiom);
    }
    // The wildcard is a pattern of its own and a variable of a constructor
    // pattern (2.7); patterns are not nested.
    let term = round_trip_term(axioms[2]);
    let Term::Forall(_, body) = &term else { panic!() };
    let Term::Application(_, args) = body.as_ref() else { panic!() };
    let Term::Match(_, cases) = &args[1] else { panic!() };
    assert_eq!(cases[1].pattern(), &smtlib::Pattern::Constructor(Symbol::new("cons").unwrap(), smtlib::NonEmpty::new(vec![None, Some(Symbol::new("t").unwrap())]).unwrap()));
    assert_eq!(Term::parse("(match l (((cons (cons x y) t) 0)))").unwrap_err().kind(), ErrorKind::Syntax);
    round_trip_term("(match l (((cons x nil) nil) (_ l)))");
}

// §3.6.3, page 35: ambiguous symbols. The ill-sorted terms and the
// well-sorted ones are all in the grammar.
#[test]
fn s3_6_3_ambiguous_symbols() {
    let ill = ["(cons \"abc\" nil)", "(cons b nil)", "(select a 0)", "(select (g 0.0) 1)"];
    let well = ["(cons \"abc\" (as nil (List String)))", "(cons (as b B) (as nil (List B)))", "(select (as a (Array Int B)) 0)", "(select ((as g (Array B Real)) 0.0) (as b B))"];
    for term in ill.iter().chain(&well) {
        round_trip_term(term);
    }
    round_trip_term("(= ((as cons (List Int)) 1 (as nil (List Int))) (as nil (List Int)))");
}

// §3.6, page 29, and §3.6.3, page 35: qualified identifiers.
#[test]
fn s3_6_4_qualified_identifiers() {
    round_trip_term("(cons \"abc\" (as nil (List String)))");
    round_trip_term("(= a ((as const-array (Array Int Real)) 0.0))");
    round_trip_term("(select (as @a1 (Array Int Int)) 3)");
}

// §3.6.5, pages 35–36: :named and :pattern.
#[test]
fn s3_6_5_term_attributes() {
    let named = "(=> (! (> x y) :named p1)
                     (! (= x z) :named p2))";
    round_trip_term(named);
    let script = round_trip_script(&format!("(set-logic QF_LIA) (declare-const x Int) (declare-const y Int) (declare-const z Int) (assert {named}) (check-sat-assuming (p1 (not p2)))"));
    assert!(matches!(&script.commands()[5], Command::CheckSatAssuming(terms) if terms.len() == 2));

    let pattern = "(forall ((x0 A) (x1 A) (x2 A))
                     (! (=> (and (r x0 x1) (r x1 x2)) (r x0 x2))
                        :pattern ((r x0 x1) (r x1 x2))
                        :pattern ((p x0 a))
                     ))";
    let term = round_trip_term(pattern);
    let Term::Forall(_, body) = &term else { panic!() };
    let Term::Annotated(_, attributes) = body.as_ref() else { panic!() };
    assert_eq!(attributes.iter().map(Attribute::to_string).collect::<Vec<_>>(), [":pattern ((r x0 x1) (r x1 x2))", ":pattern ((p x0 a))"]);
    // The constructor of :pattern values builds the same attribute.
    let terms = vec![Term::parse("(r x0 x1)").unwrap(), Term::parse("(r x1 x2)").unwrap()];
    assert_eq!(Attribute::pattern(terms), attributes[0]);
    assert_eq!(Attribute::pattern(Vec::new()).to_string(), ":pattern ()");
}

// §3.7, page 39: function symbol declarations with annotations, and the
// theory declarations of Figures 3.2–3.5. Theory and logic declarations
// (§3.7, §3.10) are not modelled as their own types; they are read and
// printed as S-expressions.
#[test]
fn s3_7_function_symbol_declarations() {
    for text in [
        "(+ Real Real Real :left-assoc)",
        "(and Bool Bool Bool :left-assoc)",
        "(par (X) (insert X (List X) (List X) :right-assoc))",
        "(< Real Real Bool :chainable)",
        "(equiv Elem Elem Bool :chainable)",
        "(par (X) (Disjoint (Set X) (Set X) Bool :pairwise))",
        "(par (X) (distinct X X Bool :pairwise))",
    ] {
        let exprs = round_trip_sexprs(text);
        assert_eq!(exprs[0].to_string(), text);
    }
}

const FIGURE_3_5: &str = r#"(theory Core

    :sorts ( (Bool 0) )

    :funs ( (true Bool) (false Bool) (not Bool Bool)
            (=> Bool Bool Bool :right-assoc) (and Bool Bool Bool :left-assoc)
            (or Bool Bool Bool :left-assoc) (xor Bool Bool Bool :left-assoc)
            (par (A) (= A A Bool :chainable))
            (par (A) (distinct A A Bool :pairwise))
            (par (A) (ite Bool A A A)) )

    :definition
    "For every expanded signature Sigma, the instance of Core with that signature
     is the theory consisting of all Sigma-models in which:
     - the sort Bool denotes the set {true, false} of Boolean values;
     - for all sorts s in Sigma,
       - (= s s Bool) denotes the function that
         returns true iff its two arguments are identical;
       - (distinct s s Bool) denotes the function that
         returns true iff its two arguments are not identical;
       - (ite Bool s s) denotes the function that
         returns its second argument or its third depending on whether
         its first argument is true or not;
     - the other function symbols of Core denote the standard Boolean operators
       as expected."

     :values "The set of values for the sort Bool is {true, false}."
)"#;

const FIGURE_3_2: &str = r#"(theory Ints
  :sorts ( (Int 0) )
  :funs ( (NUMERAL Int)
          (- Int Int)                 ; negation
          (- Int Int Int :left-assoc) ; subtraction
          (+ Int Int Int :left-assoc)
          (* Int Int Int :left-assoc)
          (<= Int Int Bool :chainable)
          (< Int Int Bool :chainable)
          (>= Int Int Bool :chainable)
          (> Int Int Bool :chainable) )
  :definition
  "For every expanded signature Sigma, the instance of Ints with that
   signature is the theory consisting of all Sigma-models that interpret
   - the sort Int as the set of all integers,
   - the function symbols of Ints as expected. "
  :values
  "The Int values are all the numerals and all the terms of the form (- n)
   where n is a non-zero numeral."
)"#;

// Figures 3.2 (page 41) and 3.5 (page 44): the theory declarations read as
// one S-expression each, headed by the symbol `theory`, with their
// attributes as keywords followed by their values.
#[test]
fn figures_3_2_and_3_5_theory_declarations() {
    for (text, name, keywords) in [(FIGURE_3_5, "Core", vec![":sorts", ":funs", ":definition", ":values"]), (FIGURE_3_2, "Ints", vec![":sorts", ":funs", ":definition", ":values"])] {
        let exprs = round_trip_sexprs(text);
        let [SExpr::List(items)] = exprs.as_slice() else { panic!("{name}") };
        assert_eq!(items[0].to_string(), "theory");
        assert_eq!(items[1].to_string(), name);
        let found: Vec<String> = items.iter().filter(|i| matches!(i, SExpr::Atom(Atom::Keyword(_)))).map(SExpr::to_string).collect();
        assert_eq!(found, keywords, "{name}");
    }
}

// §3.8, page 45: "(=> x y z) (and x y z) (= x y z) (distinct x y z)"
// abbreviate "(=> x (=> y z)) (and (and x y) z) (and (= x y) (= y z))
// (and (distinct x y) (distinct x z) (distinct y z))".
#[test]
fn s3_8_core_abbreviations() {
    let terms = [
        "(=> x y z)",
        "(and x y z)",
        "(= x y z)",
        "(distinct x y z)",
        "(=> x (=> y z))",
        "(and (and x y) z)",
        "(and (= x y) (= y z))",
        "(and (distinct x y) (distinct x z) (distinct y z))",
    ];
    for term in terms {
        round_trip_term(term);
    }
    // The abbreviation is a rule of the theory: the grammar keeps the n-ary
    // form as written.
    assert!(matches!(&round_trip_term("(and x y z)"), Term::Application(_, args) if args.len() == 3));
}

// §3.9, pages 45–47: HO-Core. The conversions between functions and maps,
// partial application, map application without @, Remark 10's
// extensionality formula, Remark 11's ill-sorted (k f), and Remark 12's
// polymorphic maps: all in the grammar, `->` as a sort symbol and `@` as a
// function symbol.
#[test]
fn s3_9_higher_order_core() {
    let head = "(set-logic ALL) (declare-fun f (Int) Real) (declare-const m (-> Int Real)) (declare-const g (-> Int Bool Real))";
    for command in [
        "(define-const c_f (-> Int Real) (lambda ((x Int)) (f x)))",
        "(define-fun f_c ((x Int)) Real (@ m x))",
        "(assert (= (@ g 1 true) (@ (@ g 1) true)))",
        "(define-const h (-> Bool Real) (@ g 1))",
        "(assert (= (m 1) (@ m 1)))",
        "(assert (= (g 1 true) 0.0))",
        "(assert (forall ((f (-> Int Real)) (g (-> Int Real))) (= (= f g) (forall ((x Int)) (= (@ f x) (@ g x))))))",
        "(declare-fun k ((-> Int Real)) Bool) (assert (k (lambda ((x Int)) (f x))))",
        "(declare-fun k ((-> Int Real)) Bool) (assert (k f))",
    ] {
        round_trip_script(&format!("{head} {command}"));
    }
    let remark_12 = "(set-logic ALL)
(declare-sort-parameter A)
(declare-sort-parameter B)
(declare-sort-parameter C)
(declare-const m (-> A B))
(define-const id (-> A A) (lambda ((a A)) a))
(define-const compose (-> (-> A B) (-> B C) (-> A C))
  (lambda ((f (-> A B)) (g (-> B C)))
    (lambda ((a A)) (@ g (@ f a)))))";
    let script = round_trip_script(remark_12);
    assert!(matches!(&script.commands()[6], Command::DefineConst(_, _, Term::Lambda(..))));
    round_trip_script(&format!("{remark_12} (declare-fun p (Int) Bool) (assert (@ (@ (@ (as compose (-> (-> Int Int) (-> Int Bool) (-> Int Bool))) (as id (-> Int Int))) (lambda ((x Int)) (p x))) 3))"));
}

// Figure 3.11 (page 54): the example script, left column then right column,
// with the responses given in its comments.
#[test]
fn figure_3_11_script() {
    let script = "(set-option :print-success true)
(set-info :smt-lib-version 2.7)
(set-logic QF_LIA)
(declare-const w Int)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (> x y))
(assert (> y z))
(push 1)
(assert (> z x))
(check-sat)
(get-info :all-statistics)
(pop 1)
(push 1)
(check-sat)
(exit)";
    let parsed = round_trip_script(script);
    let success = GeneralResponse::parse_kind("success", ResponseKind::General, &Dialect::strict()).unwrap();
    assert_eq!(success, GeneralResponse::Success);
    let unsat = GeneralResponse::parse(" unsat\n", &Command::CheckSat).unwrap();
    assert_eq!(unsat.to_string(), "unsat");
    assert!(matches!(&parsed.commands()[12], Command::GetInfo(_)));
    let statistics = GeneralResponse::parse("(:time 0.01 :memory 0.2)", &parsed.commands()[12]).unwrap();
    assert!(matches!(statistics, GeneralResponse::Specific(SpecificSuccessResponse::GetInfo(ref a)) if a.len() == 2));
}

// Figure 3.12 (page 54): an excerpt with get-value (it elides commands,
// "...", including the declaration of List); the responses in its comments
// are read as get-value responses.
#[test]
fn figure_3_12_script_and_responses() {
    let script = Script::parse(
        "(set-info :smt-lib-version 2.7)
(set-option :produce-models true)
(declare-const x Int)
(declare-const y Int)
(declare-fun f (Int) Int)
(assert (= (f x) (f y)))
(assert (not (= x y)))
(check-sat)
(get-value (x y))
(declare-const a (Array Int (List Int)))
(check-sat)
(get-value (a))
(get-value ((select @array1 2)))
(get-value ((first @list0) (rest @list0)))",
    )
    .unwrap();
    assert_eq!(script.commands().len(), 14);
    let get_value = &script.commands()[8];
    assert!(matches!(get_value, Command::GetValue(_)));
    let responses = [
        "((x 0)\n (y 1)\n )",
        "( (a (as @array1 (Array Int (List Int))))\n )",
        "(((select (as @array1 (Array Int (List Int))) 2)\n   (as @list0 (List Int))\n )\n )",
        "(((first (as @list0 (List Int))) 1)\n ((rest (as @list0 (List Int))) (as nil (List Int)))\n )",
    ];
    for text in responses {
        match GeneralResponse::parse(text, get_value).unwrap_or_else(|e| panic!("{text}: {e}")) {
            GeneralResponse::Specific(SpecificSuccessResponse::GetValue(pairs)) => assert!(!pairs.is_empty()),
            other => panic!("{other:?}"),
        }
    }
}

// §4.2.3, pages 67–68: the datatype declarations read and print.
#[test]
fn s4_2_3_datatype_declarations() {
    let examples = [
        "(declare-datatypes ( (Color 0) ) (
   ( (red) (green) (blue) ))
)",
        "(declare-datatypes ( (IntList 0) ) (
   ( (empty) (insert (head Int) (tail IntList) )))
)",
        "(declare-datatypes ( (List 1) ) (
   (par (T) ( (nil) (cons (car T) (cdr (List T)) )))))",
        "(declare-datatypes ( (Option 1) ) (
   (par (X) ( (none) (some (val X)) ))))",
        "(declare-datatypes ( (Pair 2) ) (
   (par (X Y) ( (pair (first X) (second Y)) ))))",
        "(declare-datatypes ( (Tree 1) (TreeList 1) ) (
   ; Tree
   (par (X) ( (node (value X) (children (TreeList X)) )))
   ; TreeList
   (par (Y) ( (empty)
      (insert (head (Tree Y)) (tail (TreeList Y))) ))))",
        "(declare-datatype Color ( (red) (green) (blue) ))",
        "(declare-datatype IntList
   ( (empty)
     (insert (head Int) (tail IntList) )))",
        "(declare-datatype List (par (E)
   ( (nil)
     (cons (car E) (cdr (List E)) ))))",
        "(declare-datatype Option (par (X)
   ( (none)
     (some (val X) ))))",
        "(declare-datatype Pair (par (X Y)
  ( (pair (first X) (second Y)) )))",
    ];
    for text in examples {
        let script = round_trip_script(text);
        assert!(matches!(script.commands(), [Command::DeclareDatatype(..) | Command::DeclareDatatypes(..)]), "{text}");
    }
    let script = round_trip_script(examples[5]);
    let Command::DeclareDatatypes(pairs) = &script.commands()[0] else { panic!() };
    assert_eq!(pairs.iter().map(|(s, d)| (s.symbol().as_str(), d.parameters().len(), d.constructors().len())).collect::<Vec<_>>(), [("Tree", 1, 1), ("TreeList", 1, 2)]);
    // The testers of §4.2.3 are indexed identifiers.
    round_trip_script("(declare-datatype Color ((red) (green) (blue))) (declare-const c Color) (assert ((_ is red) c))");
    // The grammar: ( par ( ⟨symbol⟩+ ) … ) and ( ⟨constructor_dec⟩+ ).
    for bad in ["(declare-datatype Box (par () ((box (content Int)))))", "(declare-datatype Box ())", "(declare-datatypes () ())", "(declare-datatypes ((A 0)) ())"] {
        assert_eq!(Script::parse(bad).unwrap_err().kind(), ErrorKind::Syntax, "{bad}");
    }
}

// §4.2.3, page 69: "(define-const f τ t) has the same effect as
// (define-fun f () τ t)": two commands of the grammar with the same parts.
#[test]
fn s4_2_3_define_const() {
    let a = round_trip_script("(define-const f Int (+ 1 2))");
    let b = round_trip_script("(define-fun f () Int (+ 1 2))");
    let (Command::DefineConst(name, sort, body), Command::DefineFun(def)) = (&a.commands()[0], &b.commands()[0]) else { panic!() };
    assert_eq!((name, sort, body), (def.name(), def.sort(), def.body()));
    assert!(def.parameters().is_empty());
}

// §4.2.4, page 70: an assertion over the polymorphic is-const, and
// Remark 13's cardinality formula.
#[test]
fn s4_2_4_polymorphic_assertions() {
    round_trip_script(
        "(set-logic ALL)
(declare-sort-parameter A)
(declare-sort-parameter B)
(declare-fun is-const ((Array A B)) Bool)
(assert (forall ((a (Array A B)))
  (= (is-const a)
     (forall ((i A) (j A)) (= (select a i) (select a j))))))
(check-sat)",
    );
    round_trip_script("(set-logic ALL) (declare-sort-parameter A) (assert (forall ((x A) (y A) (z A)) (or (= x y) (= x z))))");
}

// §4.2.3, footnote 5 (page 69): "(define-funs-rec ((f ((x Bool)) Bool))
// ((not (f x))))"; the two lists have the same length.
#[test]
fn s4_2_3_define_funs_rec() {
    let script = round_trip_script("(define-funs-rec ((f ((x Bool)) Bool)) ((not (f x))))");
    assert!(matches!(&script.commands()[0], Command::DefineFunsRec(pairs) if pairs.len() == 1));
    assert_eq!(Script::parse("(define-funs-rec ((f ((x Bool)) Bool)) ((not (f x)) x))").unwrap_err().kind(), ErrorKind::Syntax);
}

// §3.11.1, Figure 3.10 (page 53): general responses.
#[test]
fn s3_11_1_general_responses() {
    let push = Command::Push(1u64.into());
    assert_eq!(GeneralResponse::parse("success", &push).unwrap(), GeneralResponse::Success);
    assert_eq!(GeneralResponse::parse("unsupported", &push).unwrap(), GeneralResponse::Unsupported);
    assert!(matches!(GeneralResponse::parse("(error \"bad\")", &push).unwrap(), GeneralResponse::Error(s) if s.as_str() == "bad"));
    assert!(GeneralResponse::parse("sat", &push).is_err());
}

// §3.1: errors carry the line and column of the token where the rule broke.
#[test]
fn errors_have_positions() {
    for (text, kind, line, column) in [
        ("(assert (> x 0)", ErrorKind::Syntax, 1, 1),
        ("(check-sat)\n  (assert)", ErrorKind::Syntax, 2, 3),
        ("(check-sat)\r\n(assert |x)", ErrorKind::Lexical, 2, 9),
        ("(check-sat)\r(echo \"a)", ErrorKind::Lexical, 2, 7),
        ("(push x)", ErrorKind::Syntax, 1, 7),
        ("(set-logic QF_LIA))", ErrorKind::Syntax, 1, 19),
    ] {
        let error = Script::parse(text).unwrap_err();
        assert_eq!((error.kind(), error.position().map(|p| (p.line(), p.column()))), (kind, Some((line, column))), "{text:?}: {error}");
        assert!(error.to_string().starts_with(&format!("{line}:{column}: ")), "{error}");
    }
}
