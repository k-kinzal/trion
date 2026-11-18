//! The concrete proofs of the specification, quoted verbatim (page breaks
//! and running heads removed), each read and printed back to an equal
//! proof. Examples that are not well-formed text as typeset are rejected at
//! the position of the defect, and read once repaired.
//!
//! *The Alethe Proof Format: An Evolving Specification and Reference*,
//! typeset 2025-11-19, "Version not known". Page numbers are those of the
//! PDF.

use alethe::{Command, ErrorKind, Proof};

fn round_trip(text: &str) -> Proof {
    let proof = Proof::parse(text).unwrap_or_else(|e| panic!("{e}\n{text}"));
    let printed = proof.to_text();
    assert_eq!(Proof::parse(&printed).expect("the printed proof reads back"), proof, "{printed}");
    proof
}


/// Figure 1 (p. 8): veriT output "with light edits for readability". The
/// figure elides commands with `...`, so it is read in its three fragments.
#[test]
fn figure_1() {
    let figure = r#"(assume h1 (not (p a)))
(assume h2 (forall ((z1 U)) (forall ((z2 U)) (p z2))))
...
(anchor :step t9 :args ((vr4 U) (:= (z2 U) vr4)))
(step t9.t1 (cl (= z2 vr4)) :rule refl)
(step t9.t2 (cl (= (p z2) (p vr4)))
         :rule cong :premises (t9.t1))
(step t9 (cl (= (forall ((z2 U)) (p z2))
                (forall ((vr4 U)) (p vr4))))
         :rule bind)
...
(step t14 (cl (forall ((vr5 U)) (p vr5)))
          :rule th_resolution :premises (t11 t12 t13))
(step t15 (cl (or (not (forall ((vr5 U)) (p vr5)))
                  (p a)))
          :rule forall_inst :args (a))
(step t16 (cl (not (forall ((vr5 U)) (p vr5))) (p a))
          :rule or :premises (t15))
(step t17 (cl) :rule resolution :premises (t16 h1 t14))"#;
    let error = Proof::parse(figure).expect_err("the elision ... is not a command");
    assert_eq!(error.kind(), ErrorKind::Syntax);
    assert_eq!(error.position().map(|p| (p.line(), p.column())), Some((3, 1)));
    let fragments: Vec<&str> = figure.split("...\n").collect();
    assert_eq!(fragments.len(), 3);
    let commands: usize = fragments.iter().map(|f| round_trip(f).commands().len()).sum();
    assert_eq!(commands, 10);
}

/// Example 4 (p. 11): the proof of Example 3 in the concrete syntax.
#[test]
fn example_4() {
    let text = r#"(assume h1 (forall ((x S)) (P x)))
(assume h2 (not (forall ((y S)) (P y))))
(anchor :step t5 :args ((y S) (:= (x S) y)))
(step t3 (cl (= x y)) :rule refl)
(step t4 (cl (= (P x) (P y))) :rule cong :premises (t3))
(step t5 (cl (= (forall ((x S)) (P x)) (forall ((y S)) (P y))))
                              :rule bind)
(step t6 (cl (not (= (forall ((x S)) (P x)) (forall ((y S)) (P y))))
             (not (forall ((x S)) (P x)))
             (forall ((y S)) (P y))) :rule equiv_pos2)
(step t7 (cl) :rule resolution :premises (h1 h2 t5 t6))"#;
    let proof = round_trip(text);
    let Command::Anchor(anchor) = &proof.commands()[2] else { panic!("an anchor") };
    assert_eq!(anchor.step().as_str(), "t5");
    assert_eq!(anchor.context().len(), 2);
    let Command::Step(last) = &proof.commands()[7] else { panic!("a step") };
    assert!(last.clause().is_empty());
    assert_eq!(last.premises().iter().map(|s| s.as_str()).collect::<Vec<_>>(), ["h1", "h2", "t5", "t6"]);
}

/// Example 5 (p. 14): the first-innermost subproof of Example 4, a proof of
/// its own.
#[test]
fn example_5() {
    let text = r#"(anchor :step t5 :args ((y S) (:= (x S) y)))
(step t3 (cl (= x y)) :rule refl)
(step t4 (cl (= (P x) (P y))) :rule cong :premises (t3))
(step t5 (cl (= (forall ((x S)) (P x)) (forall ((y S)) (P y))))
                              :rule bind)"#;
    assert_eq!(round_trip(text).commands().len(), 4);
}

/// Example 7 (p. 15): Example 4 after eliminating its subproof. As typeset,
/// step t6 has one closing parenthesis too many (the step ends before
/// `:rule`, on line 7), so it is a syntax error; with that parenthesis
/// removed it reads.
#[test]
fn example_7() {
    let text = r#"(assume h1 (forall ((x S)) (P x)))
(assume h2 (not (forall ((y S)) (P y))))
(step t5 (cl (= (forall ((x S)) (P x)) (forall ((y S)) (P y))))
                                      :rule hole)
(step t6 (cl (= (forall ((x S)) (P x)) (forall ((y S)) (P y)))
             (not (forall ((x S)) (P x)))
             (forall ((y S)) (P y)))) :rule equiv_pos2)
(step t7 (cl) :rule resolution :premises (h1 h2 t5 t6))"#;
    let error = Proof::parse(text).expect_err("the extra parenthesis");
    assert_eq!(error.kind(), ErrorKind::Syntax);
    assert_eq!(error.position().map(|p| p.line()), Some(7), "{error}");
    let repaired = text.replace("(P y)))) :rule equiv_pos2)", "(P y))) :rule equiv_pos2)");
    assert_eq!(round_trip(&repaired).commands().len(), 5);
}

/// Example 11.1 (p. 32): `la_generic` in LRA with decimal coefficients.
#[test]
fn example_11_1() {
    let text = r#"(step t10 (cl (not (> (f a) (f b))) (not (= (f a) (f b))))
    :rule la_generic :args (1.0 -1.0))"#;
    let proof = round_trip(text);
    let Command::Step(step) = &proof.commands()[0] else { panic!("a step") };
    assert_eq!(step.args().iter().map(alethe::term::to_text).collect::<Vec<_>>(), ["1.0", "-1.0"]);
}

/// Example 11.2 (p. 32): `la_generic` in QF_UFLIA with a rational
/// coefficient.
#[test]
fn example_11_2() {
    let text = r#"(step t11 (cl (not (<= f3 0)) (<= (+ 1 (* 4 f3)) 1))
    :rule la_generic :args (1.0 1/4))"#;
    let proof = round_trip(text);
    let Command::Step(step) = &proof.commands()[0] else { panic!("a step") };
    assert_eq!(step.args().iter().map(alethe::term::to_text).collect::<Vec<_>>(), ["1.0", "1/4"]);
}

/// Example 21.1 (p. 34): `forall_inst`. As typeset, the clause and the step
/// are not closed; with the parentheses added it reads.
#[test]
fn example_21_1() {
    let text = r#"(step t16 (cl (or (not (forall ((x S) (y T)) (P y x    )))
                                             (P b (f a))
      :rule forall_inst :args ((f a) b)"#;
    let error = Proof::parse(text).expect_err("unclosed parentheses");
    assert_eq!(error.kind(), ErrorKind::Syntax);
    let repaired = format!("{})", text.replace("(P b (f a))\n", "(P b (f a))))\n"));
    let proof = round_trip(&repaired);
    let Command::Step(step) = &proof.commands()[0] else { panic!("a step") };
    assert_eq!(step.args().iter().map(alethe::term::to_text).collect::<Vec<_>>(), ["(f a)", "b"]);
}

/// Example 32.1 (p. 36): `la_disequality` and `or`.
#[test]
fn example_32_1() {
    let text = r#"(step t15 (cl (or (= a b) (not (<= a b)) (not (<= b a))))
    :rule la_disequality)
(step t16 (cl     (= a b) (not (<= a b)) (not (<= b a)))
     :rule or :premises (t15))"#;
    assert_eq!(round_trip(text).commands().len(), 2);
}

/// Example 81.1 (pp. 43–44): `onepoint` concluding a subproof with a
/// context.
#[test]
fn example_81_1() {
    let text = r#"(anchor :step t3 :args ((x S) (:= (y S) x)))
(step t3.t1 (cl (= x y)) :rule refl)
(step t3.t2 (cl (= (= x y) (= x x)))
    :rule cong :premises (t3.t1))
(step t3.t3 (cl (= x y)) :rule refl)
(step t3.t4 (cl (= (f y) (f x)))
    :rule cong :premises (t3.t3))
(step t3.t5 (cl (= (and (f x) (f y)) (and (f x) (f x))))
    :rule cong :premises (t3.t4))
(step t3.t6 (cl (= (=> (= x y) (and (f x) (f y)))
                    (=> (= x x) (and (f x) (f x)))))
    :rule cong :premises (t3.t2 t3.t5))
(step t3 (cl (=
        (forall ((x S) (y S)) (=> (= x y) (and (f x) (f y))))
        (forall ((x S))        (=> (= x x) (and (f x) (f x))))))
    :rule onepoint)"#;
    assert_eq!(round_trip(text).commands().len(), 8);
}

/// Example 92.1 (p. 47): `bind_let`, from Carcara's elaborator. (Step t2.t1
/// uses `eq_symmetric` under a context, which Rule 103 does not allow; that
/// is a matter of the rule list, not of the syntax, and is not checked
/// here.)
#[test]
fn example_92_1() {
    let text = r#"(step t1 (cl (= (= 0 1) (= 1 0))) :rule eq_symmetric)
(anchor :step t2 :args ((p Bool) (:= (p Bool) p)))
(step t2.t1 (cl (= (= p false) (= false p))) :rule eq_symmetric)
(step t2 (cl (= (let ((p (= 0 1))) (= p false))
                (let ((p (= 1 0))) (= false p))))
         :rule bind_let :premises (t1))"#;
    let proof = round_trip(text);
    let Command::Step(step) = &proof.commands()[3] else { panic!("a step") };
    assert_eq!((step.rule().as_str(), step.premises().len()), ("bind_let", 1));
}
