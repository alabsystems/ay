; QF_LRA incremental scoping regression test
; Part of #1432 - tests "reused Boolean subterm across scopes" soundness
;
; Tests the Tseitin caching soundness invariant with LRA theory:
; A shared Boolean subterm (and (>= x 0.0) (< x 1.0)) is introduced in scope 1,
; then reused with an additional constraint that makes it UNSAT.
;
; Expected: sat then unsat
; Unsound behavior: sat then sat (cached var unconstrained after pop)

(set-logic QF_LRA)
(declare-const x Real)

(push 1)
(assert (and (>= x 0.0) (< x 1.0)))  ; 0 <= x < 1, introduces Tseitin var
(check-sat)                          ; expected: sat (e.g., x = 0.5)
(pop 1)

(push 1)
; Reuses (and (>= x 0.0) (< x 1.0)) and adds (< x 0.0) which contradicts (>= x 0.0)
(assert (and (and (>= x 0.0) (< x 1.0)) (< x 0.0)))
(check-sat)                          ; expected: unsat
(pop 1)

(exit)
