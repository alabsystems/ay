(set-logic QF_AUFLIA)
; Initialize array then read back — common program pattern
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (= b (store (store (store a 0 1) 1 2) 2 3)))
(assert (= (select b 0) 1))
(assert (= (select b 1) 2))
(assert (= (select b 2) 3))
(check-sat)
; Expected: sat
(exit)
