; Test UNSAT: implied equality from multiple constraints
; Regression for #238: false SAT from missing model-based assume_eqs
;
; a + b = c and b = 0 implies a = c
; Therefore f(a) = f(c), contradicting f(a) != f(c)
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(assert (= (+ a b) c))
(assert (= b 0))
(assert (= (f a) 10))
(assert (not (= (f c) 10)))
(check-sat)
; Expected: unsat
