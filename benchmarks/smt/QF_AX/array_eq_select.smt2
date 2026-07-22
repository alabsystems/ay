; Array equality implies select equality
; a = b -> select(a, i) = select(b, i)
; Expected: unsat
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun b () (Array Index Element))
(declare-fun i () Index)
(assert (= a b))
(assert (not (= (select a i) (select b i))))
(check-sat)
(exit)
