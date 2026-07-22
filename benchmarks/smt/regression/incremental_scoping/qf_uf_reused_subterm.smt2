; QF_UF incremental scoping regression test
; Part of #1432 - tests "reused Boolean subterm across scopes" soundness
;
; This tests the Tseitin caching soundness invariant:
; If a popped assertion introduced a shared Boolean subterm (and a b),
; later assertions reusing that subterm must not see spurious SAT.
;
; Expected: sat then unsat
; Unsound behavior: sat then sat (cached var unconstrained after pop)

(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)

(push 1)
(assert (and a b))         ; introduces Tseitin var v_and plus definition clauses
(check-sat)                ; expected: sat
(pop 1)                    ; disables clauses guarded by selector for (and a b)

(push 1)
(assert (and (and a b) (not a))) ; UNSAT in SMT semantics
(check-sat)                ; expected: unsat (but spurious sat if v_and unconstrained)
(pop 1)

(exit)
