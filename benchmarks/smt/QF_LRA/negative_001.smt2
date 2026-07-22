; Negative values
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (< x 0.0))
(assert (> y 0.0))
(assert (= (+ x y) 0.0))
(check-sat)
