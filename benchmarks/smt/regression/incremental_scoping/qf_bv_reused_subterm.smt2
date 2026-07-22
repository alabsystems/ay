; QF_BV incremental scoping regression test
; Part of #1432 - tests "reused Boolean subterm across scopes" soundness
;
; Tests the Tseitin/BV caching soundness invariant:
; A shared Boolean subterm (and (= x #x00) (distinct x #x01)) is introduced in scope 1,
; then reused with an additional constraint that makes it UNSAT.
;
; Expected: sat then unsat
; Unsound behavior: sat then sat (cached var unconstrained after pop)

(set-logic QF_BV)
(declare-const x (_ BitVec 8))

(push 1)
(assert (and (= x #x00) (distinct x #x01)))  ; x = 0, introduces Tseitin var
(check-sat)                                   ; expected: sat (x = #x00)
(pop 1)

(push 1)
; Reuses (and (= x #x00) (distinct x #x01)) and adds (distinct x #x00)
; which contradicts (= x #x00)
(assert (and (and (= x #x00) (distinct x #x01)) (distinct x #x00)))
(check-sat)                                   ; expected: unsat
(pop 1)

(exit)
