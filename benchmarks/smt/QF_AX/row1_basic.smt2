; ROW1 basic: select(store(a, i, v), i) = v
; Expected: unsat
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun i () Index)
(declare-fun v () Element)
(assert (not (= (select (store a i v) i) v)))
(check-sat)
(exit)
