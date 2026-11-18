(set-logic LIA)
(declare-const c Int)
(assert (forall ((x Int)) (> x c)))
(check-sat)
