; expected: unsat
; QF_LIA — contradictory bounds on an integer.
(set-logic QF_LIA)
(set-info :status unsat)
(declare-const x Int)
(assert (> x 5))
(assert (< x 2))
(check-sat)
