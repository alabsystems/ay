; Test strict upper bound
(set-logic QF_LRA)
(declare-const x Real)
(assert (>= x 5.0))
(assert (< x 5.1))
(check-sat)
