; Store inverse: store(a, i, select(a, i)) = a
; Writing back the same value should produce the same array
; Expected: unsat
(set-logic QF_AX)
(set-info :status unsat)
(declare-sort Index 0)
(declare-sort Elem 0)
(declare-fun a () (Array Index Elem))
(declare-fun i () Index)
; store(a, i, select(a, i)) != a should be UNSAT
(assert (not (= (store a i (select a i)) a)))
(check-sat)
(exit)
