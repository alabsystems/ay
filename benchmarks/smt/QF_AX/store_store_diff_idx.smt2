; Two stores at different indices preserve each other
; b = store(store(a, i, v1), j, v2) with i != j
; select(b, i) should be v1 (store at j doesn't affect index i)
; Expected: unsat
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun i () Index)
(declare-fun j () Index)
(declare-fun v1 () Element)
(declare-fun v2 () Element)
(assert (not (= i j)))
(assert (not (= (select (store (store a i v1) j v2) i) v1)))
(check-sat)
(exit)
