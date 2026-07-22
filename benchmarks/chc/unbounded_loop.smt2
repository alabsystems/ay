; unbounded_loop.smt2 - canonical global guidance benchmark (#656, #1858)
; Author: Andrew Yates <andrewyates.name@gmail.com>
;
; Expected: sat (safe) with invariant x >= 0.
; Source: the development design notes

(set-logic HORN)
(declare-fun Inv (Int) Bool)

; init: x = 0 => Inv(x)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))

; trans: Inv(x) => Inv(x+1)
(assert (forall ((x Int)) (=> (Inv x) (Inv (+ x 1)))))

; query: Inv(x) /\ x < 0 => false
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))

(check-sat)
