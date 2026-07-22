; Test SAT: f(x) = f(y) when x = y
; Issue #222 Example 1
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= x y))
(assert (= (f x) 100))
(assert (= (f y) 100))
(check-sat)
; Expected: sat
