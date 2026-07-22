; storeinv sf size=2: cross-swap at 2 indices, flattened form
; Expected: unsat
(set-logic QF_AUFLIA)
(set-info :status unsat)
(declare-fun a1 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
; Step 1: cross-swap at i1
(declare-fun v0 () (Array Int Int))
(declare-fun v1 () (Array Int Int))
(assert (= v0 (store a2 i1 (select a1 i1))))
(assert (= v1 (store a1 i1 (select a2 i1))))
; Step 2: cross-swap at i2
(declare-fun lhs () (Array Int Int))
(declare-fun rhs () (Array Int Int))
(assert (= lhs (store v1 i2 (select v0 i2))))
(assert (= rhs (store v0 i2 (select v1 i2))))
; Assert results equal
(assert (= lhs rhs))
; Assert a1 != a2
(assert (not (= a1 a2)))
(check-sat)
(exit)
