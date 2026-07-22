; storeinv sf size=5: cross-swap at 5 indices, flattened form
; Expected: unsat
(set-logic QF_AUFLIA)
(set-info :status unsat)
(declare-fun a1 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun i3 () Int)
(declare-fun i4 () Int)
(declare-fun i5 () Int)
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
; Step 1: cross-swap at i1
(declare-fun v0 () (Array Int Int))
(declare-fun v1 () (Array Int Int))
(assert (= v0 (store a2 i1 (select a1 i1))))
(assert (= v1 (store a1 i1 (select a2 i1))))
; Step 2: cross-swap at i2
(declare-fun v2 () (Array Int Int))
(declare-fun v3 () (Array Int Int))
(assert (= v2 (store v0 i2 (select v1 i2))))
(assert (= v3 (store v1 i2 (select v0 i2))))
; Step 3: cross-swap at i3
(declare-fun v4 () (Array Int Int))
(declare-fun v5 () (Array Int Int))
(assert (= v4 (store v2 i3 (select v3 i3))))
(assert (= v5 (store v3 i3 (select v2 i3))))
; Step 4: cross-swap at i4
(declare-fun v6 () (Array Int Int))
(declare-fun v7 () (Array Int Int))
(assert (= v6 (store v4 i4 (select v5 i4))))
(assert (= v7 (store v5 i4 (select v4 i4))))
; Step 5: assert equality of final results
(assert (= (store v7 i5 (select v6 i5))
           (store v6 i5 (select v7 i5))))
; Assert a1 != a2 via Skolem
(assert (let ((?v_0 (sk a1 a2))) (not (= (select a1 ?v_0) (select a2 ?v_0)))))
(check-sat)
(exit)
