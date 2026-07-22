; Test strict lower bound
(set-logic QF_LRA)
(declare-const x Real)
(assert (> x 5.0))
(assert (< x 6.0))
(check-sat)
