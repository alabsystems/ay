; Write-back identity: store(a, i, select(a, i)) = a
; This requires extensionality: arrays that agree everywhere must be equal
; Expected: unsat
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun i () Index)
(assert (not (= (store a i (select a i)) a)))
(check-sat)
(exit)
