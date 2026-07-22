; Test UNSAT: x = y but f(x) ≠ f(y) violates congruence
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= x y))
(assert (not (= (f x) (f y))))
(check-sat)
; Expected: unsat (x = y implies f(x) = f(y))
