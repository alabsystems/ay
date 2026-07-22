; storeinv sf size=3: cross-swap at 3 indices, flattened form
; Expected: unsat
(set-logic QF_AUFLIA)
(set-info :status unsat)
(declare-fun a1 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun i3 () Int)
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
; Step 3: assert equality of final results
(assert (= (store v3 i3 (select v2 i3))
           (store v2 i3 (select v3 i3))))
; Assert a1 != a2 via Skolem
(assert (let ((?v_0 (sk a1 a2))) (not (= (select a1 ?v_0) (select a2 ?v_0)))))
(check-sat)
(exit)
