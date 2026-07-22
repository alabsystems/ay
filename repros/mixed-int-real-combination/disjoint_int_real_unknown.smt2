; Mixed Int+Real theory-combination gap (verdict INCOMPLETE, not wrong).
; Two INDEPENDENT arithmetic sub-problems — a constraint over an Int variable and
; a disjoint constraint over a Real variable — that share no atom. Each alone is
; trivially sat. z3: sat. ay: unknown (:reason-unknown incomplete).
; AY cannot combine two disjoint linear-arithmetic components (LIA + LRA).
(set-info :status sat)
(set-logic ALL)
(declare-fun x () Int)
(declare-fun p () Real)
(assert (> x 5))
(assert (> p 5.0))
(check-sat)
