; Store is idempotent: store(store(a, i, v), i, v) = store(a, i, v)
; select at any index j should be the same
; Expected: unsat
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun i () Index)
(declare-fun j () Index)
(declare-fun v () Element)
(assert (not (= (select (store (store a i v) i v) j) (select (store a i v) j))))
(check-sat)
(exit)
