//! Round trips through the printer and the readers, over generated input:
//! terms in a theory with varied notations (infix, prefix, postfix,
//! right-associative, circumfix, binders, sequences, default application,
//! literals, constants with Unicode and keyword names), once under LF's
//! higher-order abstract syntax and once without a meta-theory (plain
//! OMA/OMBINDC), and documents of the structural syntax with every kind of
//! item, declaration and component, Unicode text and text next to the
//! delimiters. The printer checks each object it prints by reading it back;
//! these tests additionally check the read-back term against the generated
//! one.

mod common;

use std::sync::OnceLock;

use common::*;
use mmt::rules::{hoas_apply, hoas_lambda};
use mmt::syntax::{Component, ConstantItem, Decl, DeclText, DocItem, Document, ModuleText, ObjectText, TheoryItem, Word};
use mmt::term::{Integer, LitValue, VarDecl};
use mmt::uri::{LocalName, MPath};
use mmt::{Library, Term};
use proptest::prelude::*;

const NOTATIONS: &str = "
  plus # 1 + 2 prec 10❙
  times # 1 * 2 prec 20❙
  neg # - 1 prec 30❙
  fact # 1 ! prec 40❙
  imp # 1 %R⇒ 2 prec 5❙
  eq # 1 ≐ 2 prec 7❙
  all # ∀ V1,… . 2 prec 3❙
  tup # ⟨ 1 , 2 , 3 ⟩❙
  sum # Σ 1,…❙
  f❙ a❙ β❙ 名前❙ constant theory❙ constant include❙";

/// The constants that terms refer to by name.
const CONSTANTS: [&str; 5] = ["a", "β", "名前", "theory", "include"];

fn library() -> &'static (Library, MPath, MPath) {
    static LIB: OnceLock<(Library, MPath, MPath)> = OnceLock::new();
    LIB.get_or_init(make_library)
}

fn make_library() -> (Library, MPath, MPath) {
    let mut lib = mini_lf();
    let src = format!(
        "namespace http://test.org/p❚
import rules scala://mmt.kwarc.info❚
import m http://cds.omdoc.org/mmt❚
theory H : http://cds.omdoc.org/urtheories?LF =
  i : type❙ str : type❙ int : type❙
  rule rules/lf?Realize str rules/api/uom?StandardString❙
  rule rules/lf?Realize int rules/api/uom?StandardInt❙
  {NOTATIONS}
❚
theory P =
  include m?mmt❙
  {NOTATIONS}
❚"
    );
    let errors = add(&mut lib, &src);
    assert!(errors.is_empty(), "{}", show(&errors));
    (lib, mpath("http://test.org/p?H"), mpath("http://test.org/p?P"))
}

/// A generated term: built for a theory with or without higher-order abstract syntax.
#[derive(Clone, Debug)]
enum Gen {
    Const(usize),
    Var(usize),
    Int(u64),
    Str(String),
    Op(&'static str, Vec<Gen>),
    All(usize, Box<Gen>),
    Apply(Box<Gen>, Vec<Gen>),
}

const VAR_NAMES: [&str; 6] = ["x", "y", "z", "u", "v", "w"];

fn gen() -> impl Strategy<Value = Gen> {
    let leaf = prop_oneof![(0usize..CONSTANTS.len()).prop_map(Gen::Const), (0usize..6).prop_map(Gen::Var), any::<u64>().prop_map(Gen::Int), "[a-zα-ω名前 #:=❘@/%]{0,5}".prop_map(Gen::Str)];
    leaf.prop_recursive(5, 40, 3, |inner| {
        prop_oneof![
            (prop_oneof![Just("plus"), Just("times"), Just("imp"), Just("eq")], inner.clone(), inner.clone()).prop_map(|(o, x, y)| Gen::Op(o, vec![x, y])),
            (prop_oneof![Just("neg"), Just("fact")], inner.clone()).prop_map(|(o, x)| Gen::Op(o, vec![x])),
            (inner.clone(), inner.clone(), inner.clone()).prop_map(|(x, y, z)| Gen::Op("tup", vec![x, y, z])),
            prop::collection::vec(inner.clone(), 2..4).prop_map(|v| Gen::Op("sum", v)),
            (1usize..3, inner.clone()).prop_map(|(n, b)| Gen::All(n, Box::new(b))),
            (inner.clone(), prop::collection::vec(inner.clone(), 1..3)).prop_map(|(h, a)| Gen::Apply(Box::new(h), a)),
        ]
    })
}

/// Builds the term a parser builds for the generated structure; bound variables are named by depth.
fn build(g: &Gen, thy: &MPath, hoas: bool, bound: &[LocalName]) -> Term {
    let c = |n: &str| Term::Sym(thy.sym(n));
    let op = |name: &str, args: Vec<Term>| if hoas { Term::app(Term::Sym(hoas_apply()), std::iter::once(c(name)).chain(args).collect()) } else { Term::app(c(name), args) };
    match g {
        Gen::Const(i) => c(CONSTANTS[*i]),
        Gen::Var(i) => match bound.len() {
            0 => c(CONSTANTS[i % CONSTANTS.len()]),
            n => Term::Var(bound[i % n].clone()),
        },
        Gen::Int(n) if hoas => Term::lit(LitValue::Int(Integer::from(*n)), c("int")),
        Gen::Str(s) if hoas => Term::lit(LitValue::String(s.clone()), c("str")),
        Gen::Int(_) | Gen::Str(_) => c("a"),
        Gen::Op(o, args) => op(o, args.iter().map(|a| build(a, thy, hoas, bound)).collect()),
        Gen::All(n, body) => {
            let mut inner = bound.to_vec();
            let mut vars = Vec::new();
            for k in 0..*n {
                let name = LocalName::simple(format!("{}{}", VAR_NAMES[bound.len() % 6], ["", "a", "b"][k]));
                inner.push(name.clone());
                vars.push(VarDecl { name, tp: None, df: None });
            }
            let b = build(body, thy, hoas, &inner);
            if hoas {
                Term::app(Term::Sym(hoas_apply()), vec![c("all"), Term::Bind(Box::new(Term::Sym(hoas_lambda())), vars, vec![b])])
            } else {
                Term::Bind(Box::new(c("all")), vars, vec![b])
            }
        }
        Gen::Apply(h, args) => {
            let f = match &**h {
                Gen::Var(_) if !bound.is_empty() => build(h, thy, hoas, bound),
                _ => c("f"),
            };
            let args: Vec<Term> = args.iter().map(|a| build(a, thy, hoas, bound)).collect();
            if hoas {
                Term::app(Term::Sym(hoas_apply()), std::iter::once(f).chain(args).collect())
            } else {
                Term::app(f, args)
            }
        }
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(cases(256)))]

    #[test]
    fn terms_print_and_read_back_under_hoas(g in gen()) {
        let (lib, h, _) = library();
        let scope = lib.object_scope(h).unwrap();
        let t = build(&g, h, true, &[]);
        let text = scope.print_term(&t).map_err(|e| TestCaseError::fail(format!("{e}\n{t}")))?;
        let back = scope.parse(&text).map_err(|e| TestCaseError::fail(format!("{e}\n{text}")))?;
        prop_assert_eq!(back.term(), &t, "{}", text);
    }

    #[test]
    fn terms_print_and_read_back_without_meta_theory(g in gen()) {
        let (lib, _, p) = library();
        let scope = lib.object_scope(p).unwrap();
        let t = build(&g, p, false, &[]);
        let text = scope.print_term(&t).map_err(|e| TestCaseError::fail(format!("{e}\n{t}")))?;
        let back = scope.parse(&text).map_err(|e| TestCaseError::fail(format!("{e}\n{text}")))?;
        prop_assert_eq!(back.term(), &t, "{}", text);
    }
}

/// Names: ASCII, Unicode letters, and words that are keywords of the structure parser (written after `constant`).
fn name() -> impl Strategy<Value = String> {
    prop_oneof![
        3 => "[a-z][a-z0-9_]{0,6}",
        2 => "[α-ωА-я名前][α-ω0-9_名前]{0,4}",
        1 => prop::sample::select(vec!["constant", "include", "theory", "rule", "meta", "tag", "realize", "structure", "view", "role", "//", "/", "#", "##", "@_x", "a_"]).prop_map(str::to_string),
    ]
}

/// Text of any characters (delimiters and carriage returns are left out by the filters of the strategies below).
fn text() -> impl Strategy<Value = String> {
    prop_oneof![
        "[a-z0-9 ()+*⟶:=#@/%]{0,12}",
        "[ -~α-ω❘❙❚\u{1c}-\u{1f}\n\t\u{a0}]{0,10}",
    ]
}

fn object() -> impl Strategy<Value = ObjectText> {
    text().prop_filter_map("not an object text", |t| ObjectText::new(t).ok())
}

fn word() -> impl Strategy<Value = Word> {
    prop_oneof![name(), "[ -~α-ω]{1,8}", "http://[a-z]{1,5}\\.org(/[a-z]{1,3})?(\\?[A-Z][a-z]{0,3}){0,2}"].prop_filter_map("not a word", |w| Word::new(w).ok())
}

fn component() -> impl Strategy<Value = Component> {
    prop_oneof![
        object().prop_map(Component::Type),
        object().prop_map(Component::Definiens),
        object().prop_map(Component::Notation),
        object().prop_map(Component::PresentationNotation),
        object().prop_map(Component::Alias),
        object().prop_map(Component::Role),
        (word(), object()).prop_map(|(key, value)| Component::Meta { key, value }),
        word().prop_map(Component::Tag),
        object().prop_map(Component::Comment),
    ]
}

fn constant() -> impl Strategy<Value = Decl> {
    (name().prop_filter_map("not a word", |n| Word::new(n).ok()), prop::collection::vec(component(), 0..5)).prop_filter_map("a main component twice", |(name, components)| ConstantItem::new(name, components).ok().map(Decl::Constant))
}

fn decl() -> impl Strategy<Value = Decl> {
    prop_oneof![
        6 => constant(),
        1 => object().prop_map(Decl::Include),
        1 => object().prop_map(Decl::Rule),
        1 => (word(), object()).prop_map(|(key, value)| Decl::Meta { key, value }),
        1 => word().prop_map(Decl::Tag),
        1 => text().prop_filter_map("not a declaration text", |t| DeclText::new(t).ok()).prop_map(Decl::Comment),
        1 => text().prop_filter_map("not a declaration text", |t| DeclText::new(t).ok()).prop_map(Decl::Text),
    ]
}

fn theory(depth: u32) -> BoxedStrategy<TheoryItem> {
    let body = if depth == 0 { prop::collection::vec(decl(), 0..6).boxed() } else { prop::collection::vec(prop_oneof![5 => decl(), 1 => theory(depth - 1).prop_map(Decl::Theory)], 0..6).boxed() };
    (word(), prop::option::of(word()), body).prop_map(|(name, meta, body)| TheoryItem { name, meta, body }).boxed()
}

fn document() -> impl Strategy<Value = Document> {
    let module_text = || text().prop_filter_map("not a module text", |t| ModuleText::new(t).ok());
    prop::collection::vec(
        prop_oneof![
            1 => word().prop_map(DocItem::Namespace),
            1 => (word(), word()).prop_map(|(prefix, uri)| DocItem::Import { prefix, uri }),
            1 => word().prop_map(DocItem::FixMeta),
            1 => word().prop_map(DocItem::Rule),
            1 => module_text().prop_map(DocItem::Comment),
            1 => module_text().prop_map(DocItem::Text),
            4 => theory(2).prop_map(DocItem::Theory),
        ],
        0..6,
    )
    .prop_map(|items| Document { items })
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(cases(512)))]

    #[test]
    fn documents_print_and_read_back(d in document()) {
        let text = d.to_string();
        let back = Document::parse(&text).map_err(|e| TestCaseError::fail(format!("{e}\n{text}")))?;
        prop_assert_eq!(back, d, "{}", text);
    }
}
