; Test UNSAT: implied equality from arithmetic constraints
; Regression for #237: false SAT from missing implied-equality propagation
;
; a + 1 = b + 1 implies a = b
; b + 2 = c + 2 implies b = c
; Therefore a = b = c and f(a) = f(b) = f(c)
; But f(a) = 10 and f(b) != 10 is contradictory
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (= (+ a 1) (+ b 1)))
(assert (= (+ b 2) (+ c 2)))
(assert (= (f a) 10))
(assert (= (f c) 10))
(assert (not (= (f b) 10)))
(check-sat)
; Expected: unsat
