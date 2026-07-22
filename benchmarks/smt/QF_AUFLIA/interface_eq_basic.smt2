; Interface equality regression test (#8531)
;
; Two arrays a, b of the same sort. Uninterpreted function f applied to both.
; Constraint: f(a) = f(b) AND select(a, 0) != select(b, 0)
; Expected: sat (the model needs a != b from extensionality, and f can map
; different arrays to the same value)
;
; Without interface equalities, the solver may not explore the a = b vs a != b
; case split, potentially returning unknown instead of sat.
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(declare-fun f ((Array Int Int)) Int)

(assert (= (f a) (f b)))
(assert (not (= (select a 0) (select b 0))))

(check-sat)
(exit)
