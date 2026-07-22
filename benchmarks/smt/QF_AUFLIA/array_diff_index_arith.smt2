(set-logic QF_AUFLIA)
; Different index arithmetic leads to unsat
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(assert (= (select (store a i 42) (+ i 0)) 43))
(check-sat)
; Expected: unsat (i+0 = i, so select gives 42, not 43)
(exit)
