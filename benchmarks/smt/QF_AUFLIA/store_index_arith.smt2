(set-logic QF_AUFLIA)
; Array store with arithmetic index constraints
; store(a, i+1, v) then select(a, i+1) should equal v
(declare-fun a () (Array Int Int))
(declare-fun i () Int)
(declare-fun v () Int)
(assert (= (select (store a (+ i 1) v) (+ i 1)) v))
(assert (not (= (select (store a (+ i 1) v) (+ i 1)) v)))
(check-sat)
; Expected: unsat
(exit)
