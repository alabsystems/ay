; Store inverse: store(a, i, select(a, i)) = a
; Using nested let in QF_AUFLIA
; Expected: unsat
(set-logic QF_AUFLIA)
(set-info :status unsat)
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(assert (not (= (store a i (select a i)) a)))
(check-sat)
(exit)
