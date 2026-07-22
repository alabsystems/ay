; expected: sat
; QF_LRA — satisfiable linear-real system.
(set-logic QF_LRA)
(set-info :status sat)
(declare-const a Real)
(declare-const b Real)
(assert (< a b))
(assert (< b (+ a 1.0)))
(assert (> a 0.0))
(check-sat)
