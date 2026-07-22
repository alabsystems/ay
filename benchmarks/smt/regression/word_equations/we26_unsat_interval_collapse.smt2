; Stage 3b regression (A3): interval length bounds couple into the Nielsen
; length abstraction. x·ab = ab·x forces x ∈ (ab)* (even length), but the
; two inequalities collapse the window to |x| = 1.
; before: unknown   after: unsat   z3 4.16.0: unsat
(set-logic QF_SLIA)
(declare-const x String)
(assert (= (str.++ x "ab") (str.++ "ab" x)))
(assert (>= (str.len x) 1))
(assert (<= (str.len x) 1))
(check-sat)
