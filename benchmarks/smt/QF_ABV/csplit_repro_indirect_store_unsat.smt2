; csplit-like benchmark: indirect store through variable alias.
; Pattern: b is defined as store(a, i, v), but select is done via b (not store term directly)
; This tests that congruence axioms connect select(b, i) with v.
(set-logic QF_ABV)

(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun idx () (_ BitVec 32))
(declare-fun val () (_ BitVec 8))

; b = store(a, idx, val)
(assert (= b (store a idx val)))

; But select(b, idx) != val -- this is UNSAT
(assert (not (= (select b idx) val)))

(check-sat)
