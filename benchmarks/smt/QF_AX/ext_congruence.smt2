; Extensionality + congruence: store(a, i, v) = store(b, i, v) when a = b
; Expected: unsat
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun b () (Array Index Element))
(declare-fun i () Index)
(declare-fun v () Element)
(assert (= a b))
(assert (not (= (store a i v) (store b i v))))
(check-sat)
(exit)
