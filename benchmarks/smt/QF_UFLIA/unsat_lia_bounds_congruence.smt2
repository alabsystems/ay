; Test UNSAT: LIA bounds determine equality which causes congruence conflict
; a >= 3, a <= 3, b = 3, so a = b = 3
; f(a) = 10, f(b) = 20 conflicts with a = b
(set-logic QF_UFLIA)
(declare-const a Int)
(declare-const b Int)
(declare-fun f (Int) Int)
(assert (>= a 3))
(assert (<= a 3))
(assert (= b 3))
(assert (= (f a) 10))
(assert (= (f b) 20))
(check-sat)
; Expected: unsat
