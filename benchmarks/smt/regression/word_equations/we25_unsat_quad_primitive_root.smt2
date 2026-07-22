; Stage 2 regression (A3, BONUS): quadratic rotation x·a·x·b = b·x·a·x —
; σ(x·a·x) must be a power of "b" (Lyndon–Schützenberger) yet contains 'a'.
; before: unknown   after: unsat   z3 4.16.0: TIMEOUT at 10s (ay decides
; via the primitive-root refutation; verified by hand, see word_eq.rs
; commutation_conflict docs).
(set-logic QF_S)
(declare-const x String)
(assert (= (str.++ x "a" x "b") (str.++ "b" x "a" x)))
(check-sat)
