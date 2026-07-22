; Test case for LRA strict bounds - the bug fixed in #158
; x > 100 should have x = 101 as a solution (not exactly 100)
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (= y (+ x 1.0)))
(assert (> x 0.0))
(assert (> y 100.0))
(check-sat)
