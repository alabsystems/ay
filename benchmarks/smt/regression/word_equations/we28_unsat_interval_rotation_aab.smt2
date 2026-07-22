; Stage 3b regression (A3): x·aab = aab·x forces σ(x) ∈ (aab)*, so |x| is a
; multiple of 3 — impossible inside the faithful window 1 ≤ |x| ≤ 2.
; before: unknown   after: unsat   z3 4.16.0: unsat
(set-logic QF_SLIA)
(declare-const x String)
(assert (= (str.++ x "aab") (str.++ "aab" x)))
(assert (>= (str.len x) 1))
(assert (<= (str.len x) 2))
(check-sat)
