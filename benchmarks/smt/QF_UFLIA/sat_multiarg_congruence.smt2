; Test SAT: g(a,0) = g(b,0) when a = b
(set-logic QF_UFLIA)
(declare-fun g (Int Int) Int)
(declare-const a Int)
(declare-const b Int)
(assert (= a b))
(assert (= (g a 0) (g b 0)))
(check-sat)
; Expected: sat
