; storeinv sf size=7: cross-swap at 7 indices, flattened form
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
(declare-fun i6 () Int)
(declare-fun i7 () Int)
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
; Step 1
(declare-fun v0 () (Array Int Int))
(declare-fun v1 () (Array Int Int))
(assert (= v0 (store a2 i1 (select a1 i1))))
(assert (= v1 (store a1 i1 (select a2 i1))))
; Step 2
(declare-fun v2 () (Array Int Int))
(declare-fun v3 () (Array Int Int))
(assert (= v2 (store v0 i2 (select v1 i2))))
(assert (= v3 (store v1 i2 (select v0 i2))))
; Step 3
(declare-fun v4 () (Array Int Int))
(declare-fun v5 () (Array Int Int))
(assert (= v4 (store v2 i3 (select v3 i3))))
(assert (= v5 (store v3 i3 (select v2 i3))))
; Step 4
(declare-fun v6 () (Array Int Int))
(declare-fun v7 () (Array Int Int))
(assert (= v6 (store v4 i4 (select v5 i4))))
(assert (= v7 (store v5 i4 (select v4 i4))))
; Step 5
(declare-fun v8 () (Array Int Int))
(declare-fun v9 () (Array Int Int))
(assert (= v8 (store v6 i5 (select v7 i5))))
(assert (= v9 (store v7 i5 (select v6 i5))))
; Step 6
(declare-fun v10 () (Array Int Int))
(declare-fun v11 () (Array Int Int))
(assert (= v10 (store v8 i6 (select v9 i6))))
(assert (= v11 (store v9 i6 (select v8 i6))))
; Step 7
(assert (= (store v11 i7 (select v10 i7))
           (store v10 i7 (select v11 i7))))
; Assert a1 != a2
(assert (let ((?v_0 (sk a1 a2))) (not (= (select a1 ?v_0) (select a2 ?v_0)))))
(check-sat)
(exit)
