; Store overwrite: store(store(a, i, v1), i, v2) at index i gives v2
; Expected: unsat
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun i () Index)
(declare-fun v1 () Element)
(declare-fun v2 () Element)
(assert (not (= (select (store (store a i v1) i v2) i) v2)))
(check-sat)
(exit)
