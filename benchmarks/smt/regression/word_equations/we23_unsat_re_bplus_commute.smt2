; Stage 2 regression (A3): x commutes with "ab" (x ∈ (ab)*) but x ∈ b+ —
; the b-derivative of every reachable residual is empty.
; before: unknown   after: unsat   z3 4.16.0: unsat
(set-logic QF_S)
(declare-const x String)
(assert (= (str.++ x "ab") (str.++ "ab" x)))
(assert (str.in_re x (re.+ (str.to_re "b"))))
(check-sat)
