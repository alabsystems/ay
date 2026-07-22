; QF_LIA incremental scoping regression test
; Part of #1432 - tests "reused Boolean subterm across scopes" soundness
;
; Tests the Tseitin caching soundness invariant with LIA theory:
; A shared Boolean subterm (and (>= x 0) (< x 1)) is introduced in scope 1,
; then reused with an additional constraint that makes it UNSAT.
;
; Expected: sat then unsat
; Unsound behavior: sat then sat (cached var unconstrained after pop)

(set-logic QF_LIA)
(declare-const x Int)

(push 1)
(assert (and (>= x 0) (< x 1)))  ; x = 0 is the only solution, introduces Tseitin var
(check-sat)                      ; expected: sat (x = 0)
(pop 1)

(push 1)
; Reuses (and (>= x 0) (< x 1)) and adds (< x 0) which contradicts (>= x 0)
(assert (and (and (>= x 0) (< x 1)) (< x 0)))
(check-sat)                      ; expected: unsat
(pop 1)

(exit)
