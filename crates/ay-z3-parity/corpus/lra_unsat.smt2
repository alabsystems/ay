; expected: unsat
; QF_LRA — strict inequality cycle has no real solution.
(set-logic QF_LRA)
(set-info :status unsat)
(declare-const a Real)
(declare-const b Real)
(assert (< a b))
(assert (< b a))
(check-sat)
