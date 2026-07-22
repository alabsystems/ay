(set-logic QF_AUFLIA)
; Array with bounded integer values — sat check
(declare-fun a () (Array Int Int))
(declare-fun x () Int)
(assert (>= x 0))
(assert (<= x 10))
(assert (= (select a x) (+ x 5)))
(assert (= (select a 3) 8))
(assert (= x 3))
(check-sat)
; Expected: sat
(exit)
