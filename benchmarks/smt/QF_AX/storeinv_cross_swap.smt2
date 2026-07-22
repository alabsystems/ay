; Cross-swap store inverse: swap values between a1 and a2 at i1 and i2
; Then assert the results are equal + a1 != a2 => UNSAT
; Simplified version of storeinv_t1_np_nf_ai_00002_001
(set-logic QF_AX)
(set-info :status unsat)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a1 () (Array Index Element))
(declare-fun a2 () (Array Index Element))
(declare-fun i1 () Index)
(declare-fun i2 () Index)
; v0 = a2 with a1[i1] at position i1
(declare-fun v0 () (Array Index Element))
(assert (= v0 (store a2 i1 (select a1 i1))))
; v1 = a1 with a2[i1] at position i1
(declare-fun v1 () (Array Index Element))
(assert (= v1 (store a1 i1 (select a2 i1))))
; Cross-swap at i2
(declare-fun lhs () (Array Index Element))
(assert (= lhs (store v1 i2 (select v0 i2))))
(declare-fun rhs () (Array Index Element))
(assert (= rhs (store v0 i2 (select v1 i2))))
; Assert they're equal
(assert (= lhs rhs))
; Assert a1 != a2 => should be UNSAT
(assert (not (= a1 a2)))
(check-sat)
(exit)
