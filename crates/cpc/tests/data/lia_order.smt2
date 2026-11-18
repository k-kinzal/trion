; QF_LIA: x > y + 1 and x < y.
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x (+ y 1)))
(assert (< x y))
(check-sat)
