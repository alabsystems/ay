(set-info :status unsat)
(set-logic QF_LRA)
; No real number satisfies x > 1 and x < 1 simultaneously
(declare-const x Real)
(assert (> x 1.0))
(assert (< x 1.0))
(check-sat)
(exit)
