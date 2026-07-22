; QF_BV incremental scoping regression test for internal BV subterms
; Part of #1454 - tests "cached BV internal term across pop" soundness
;
; This test exercises BV arithmetic operations (bvadd) that generate their
; own bitblasting circuits, as opposed to simple Boolean predicates.
;
; The concern: When the BV solver caches bitblasted subterms in term_to_bits
; and those are reused across push/pop with changing var_offset, the cached
; bits may reference stale/incorrect SAT variables.
;
; Tests the BV caching soundness invariant:
; An internal BV subterm (bvadd x #x01) is introduced in scope 1,
; then reused in scope 2 with a contradiction.
;
; Expected: sat then unsat
; Unsound behavior: sat then sat (cached bits unconstrained after pop)

(set-logic QF_BV)
(declare-const x (_ BitVec 8))

(push 1)
; Introduces (bvadd x #x01) which generates adder circuit
(assert (= (bvadd x #x01) #x02))    ; x + 1 = 2, so x = 1
(check-sat)                         ; expected: sat (x = #x01)
(pop 1)

(push 1)
; Reuses (bvadd x #x01) and adds a contradiction:
; (bvadd x #x01) = #x02 AND (bvadd x #x01) != #x02
(assert (and (= (bvadd x #x01) #x02) (distinct (bvadd x #x01) #x02)))
(check-sat)                         ; expected: unsat
(pop 1)

(exit)
