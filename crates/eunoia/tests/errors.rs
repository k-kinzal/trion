//! Every kind of error, produced by a text or a value that causes it: the
//! kind is a typed value a caller can match on, the position points at the
//! offending token, and `Display` keeps a message for a person.

use eunoia::{parse_script, parse_term, Application, AstErrorKind, Found, Keyword, Literal, LiteralCategory, LiteralProblem, NonEmpty, ParseErrorKind, Position, StrLit, Symbol, SyntaxProblem, Term, UnsupportedConstruct};

/// Parses `text` as a script; it must fail with `kind` at line 1, `column`.
#[track_caller]
fn fails(text: &str, column: u32, kind: ParseErrorKind) {
    let e = parse_script(text).expect_err(text);
    assert_eq!(e.kind, kind, "{text}\n  gave: {e}");
    assert_eq!(e.position, Position::new(1, column), "{text}\n  gave: {e}");
    assert!(!e.to_string().is_empty());
}

fn kw(name: &str) -> Keyword {
    Keyword::new(name).unwrap()
}

#[test]
fn literal_problems() {
    let lit = ParseErrorKind::InvalidLiteral;
    fails("(define d () #b)", 14, lit(LiteralProblem::MissingDigits(LiteralCategory::Binary)));
    fails("(define d () #x)", 14, lit(LiteralProblem::MissingDigits(LiteralCategory::Hexadecimal)));
    fails("(define d () 1.)", 14, lit(LiteralProblem::MissingDigits(LiteralCategory::Decimal)));
    fails("(define d () 1/)", 14, lit(LiteralProblem::MissingDigits(LiteralCategory::Rational)));
    fails("(define d () #q)", 14, lit(LiteralProblem::UnknownRadix));
    fails("(define d () \"é\")", 14, lit(LiteralProblem::NonAsciiString));
    fails("(define d () 1/0)", 14, lit(LiteralProblem::ZeroDenominator));
    fails("(declare-sort S 01)", 17, lit(LiteralProblem::LeadingZero));
    fails("(declare-sort S 4294967296)", 17, lit(LiteralProblem::TooLarge));
}

#[test]
fn syntax_problems() {
    let syn = ParseErrorKind::Syntax;
    fails("(define d () [)", 14, syn(SyntaxProblem::UnexpectedCharacter('[')));
    fails("(declare-const a Bool : )", 23, syn(SyntaxProblem::EmptyKeyword));
    fails("(define d () ((f a) b))", 16, syn(SyntaxProblem::QualifierHead));
    fails("(define d () (lambda ((x)) x))", 25, syn(SyntaxProblem::VariablePair));
    fails("(define d () (let ((x)) x))", 22, syn(SyntaxProblem::BindingPair));
    fails("(define d () ())", 14, syn(SyntaxProblem::MissingHead));
    fails("(define d () (!))", 16, syn(SyntaxProblem::AnnotationWithoutTerm));
    fails("(define d () (! a))", 18, syn(SyntaxProblem::AnnotationWithoutAttribute));
    fails("(declare-datatype D (par () ((c))))", 26, syn(SyntaxProblem::EmptyParameterList));
    fails("(declare-datatype D ())", 22, syn(SyntaxProblem::DatatypeWithoutConstructor));
    fails("(declare-datatypes ((D 0)) ())", 30, syn(SyntaxProblem::DatatypeCount { sorts: 1, datatypes: 0 }));
    fails("(step @p a :premises ())", 12, syn(SyntaxProblem::StepWithoutRule));
    fails("(declare-rule r () :args () :premises ())", 29, syn(SyntaxProblem::RuleField(kw("premises"))));
    fails("(program p () :sig (Bool) Bool)", 15, syn(SyntaxProblem::ProgramWithoutSignature(kw("sig"))));
    fails("(program p () :signature () Bool)", 26, syn(SyntaxProblem::ProgramWithoutArgumentType));
    fails("(declare-consts <bits> Bool)", 17, syn(SyntaxProblem::UnknownLiteralCategory("<bits>".to_string())));
    fails("(define d () (f))", 14, syn(SyntaxProblem::Invalid(AstErrorKind::NoArguments)));
    fails("(define d () ((_ ((x Bool)) a) b))", 14, syn(SyntaxProblem::Invalid(AstErrorKind::ApplicationHead)));
}

#[test]
fn unsupported_constructs() {
    fails("(define d () |Bool|)", 14, ParseErrorKind::Unsupported(UnsupportedConstruct::QuotedBuiltinWord("Bool")));
    fails("(define d () -.5)", 14, ParseErrorKind::Unsupported(UnsupportedConstruct::LiteralWithoutLeadingDigits("-.5".to_string())));
}

#[test]
fn unexpected_tokens_say_what_was_found() {
    let found = |text: &str| match parse_script(text).unwrap_err().kind {
        ParseErrorKind::UnexpectedToken { found, .. } => found,
        other => panic!("{text}: {other:?}"),
    };
    assert_eq!(found("(assume 1 a)"), Found::Literal(LiteralCategory::Numeral, "1".to_string()));
    assert_eq!(found("(assume #b01 a)"), Found::Literal(LiteralCategory::Binary, "#b01".to_string()));
    assert_eq!(found("(assume :k a)"), Found::Keyword("k".to_string()));
    assert_eq!(found("(assume let a)"), Found::Reserved("let"));
    assert_eq!(found("(frobnicate)"), Found::Symbol("frobnicate".to_string()));
    assert_eq!(found("(assume (a) a)"), Found::LParen);
    assert!(matches!(parse_term("(f a))").unwrap_err().kind, ParseErrorKind::UnexpectedToken { found: Found::RParen, expected: "the end of the term" }));
    let e = parse_script("(assume 1 a)").unwrap_err();
    assert_eq!(e.to_string(), "1:9: expected a symbol, found literal `1`");
}

#[test]
fn values_the_abstract_syntax_refuses() {
    let kind = |r: Result<(), eunoia::AstError>| r.unwrap_err().kind();
    assert_eq!(kind(NonEmpty::<Term>::from_vec(Vec::new()).map(drop)), AstErrorKind::Empty);
    assert_eq!(kind(Symbol::new("a|b").map(drop)), AstErrorKind::SymbolWithBar);
    assert_eq!(kind(Symbol::new("let").map(drop)), AstErrorKind::ReservedWord("let"));
    assert_eq!(kind(Keyword::new("a b").map(drop)), AstErrorKind::NotAKeyword);
    assert_eq!(kind(Literal::new(LiteralCategory::Rational, "1/0").map(drop)), AstErrorKind::ZeroDenominator);
    assert_eq!(kind(Literal::new(LiteralCategory::Boolean, "true").map(drop)), AstErrorKind::BooleanLiteral);
    assert_eq!(kind(Literal::new(LiteralCategory::Numeral, "x").map(drop)), AstErrorKind::NotALiteral(LiteralCategory::Numeral));
    assert_eq!(kind(StrLit::new("é").map(drop)), AstErrorKind::NonAsciiString);
    let a = Term::symbol("a").unwrap();
    assert_eq!(kind(Application::new(Term::Literal(Literal::new(LiteralCategory::Numeral, "1").unwrap()), vec![a.clone()]).map(drop)), AstErrorKind::ApplicationHead);
    assert_eq!(kind(Application::new(a.clone(), Vec::new()).map(drop)), AstErrorKind::NoArguments);
    let f = Symbol::new("f").unwrap();
    assert_eq!(kind(Application::binder(f.clone(), Vec::new(), vec![a.clone()]).map(drop)), AstErrorKind::EmptyVariableList);
    assert_eq!(kind(Application::binder(f, vec![(Symbol::new("_").unwrap(), a.clone())], vec![a]).map(drop)), AstErrorKind::QualifierVariable);
}
