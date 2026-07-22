; Store transitivity via equality: b = store(a, i, e) implies select(b, i) = e
; Expected: unsat
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun b () (Array Index Element))
(declare-fun i () Index)
(declare-fun e () Element)
(assert (= b (store a i e)))
(assert (not (= (select b i) e)))
(check-sat)
(exit)
