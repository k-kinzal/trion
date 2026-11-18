; QF_UF: a = b but f(a) /= f(b).
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-fun a () U)
(declare-fun b () U)
(assert (= a b))
(assert (not (= (f a) (f b))))
(check-sat)
