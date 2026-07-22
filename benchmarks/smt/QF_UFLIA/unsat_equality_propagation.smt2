; Test UNSAT: x=5, y=5 => f(x)=f(y) but 10≠20
; Issue #222 Example 2
(set-logic QF_UFLIA)
(declare-const x Int)
(declare-const y Int)
(declare-fun f (Int) Int)
(assert (>= x 5))
(assert (<= x 5))
(assert (= y 5))
(assert (= (f x) 10))
(assert (= (f y) 20))
(check-sat)
; Expected: unsat (x=5=y, so f(x)=f(y), but 10≠20)
