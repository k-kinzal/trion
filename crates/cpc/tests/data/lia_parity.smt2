; QF_LIA: 2x = 2y + 1 has no integer solution.
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (* 2 x) (+ (* 2 y) 1)))
(check-sat)
