; Test non-unit coefficients
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (= (* 3.0 x) (* 2.0 y)))
(assert (> x 0.0))
(assert (> y 0.0))
(assert (< x 10.0))
(check-sat)
