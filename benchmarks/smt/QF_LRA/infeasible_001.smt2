; Infeasible linear system
(set-logic QF_LRA)
(declare-const x Real)
(assert (>= x 10.0))
(assert (<= x 5.0))
(check-sat)
