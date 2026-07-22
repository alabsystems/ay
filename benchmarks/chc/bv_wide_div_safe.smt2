; CHC with wide BV division — exercises delayed internalization for bvudiv
; Expected: sat (safe)
;
; Models halving: x starts at 100, halved each step via bvudiv.
;   init: x = 100
;   trans: x' = bvudiv(x, 2)
;   bad: x > 200 (unreachable: halving never exceeds initial value)

(set-logic HORN)

(declare-fun Inv ((_ BitVec 16)) Bool)

; Init: x = 100
(assert (forall ((x (_ BitVec 16)))
  (=> (= x #x0064) (Inv x))))

; Trans: x' = x / 2 (wide division, triggers delayed internalization)
(assert (forall ((x (_ BitVec 16)) (xp (_ BitVec 16)))
  (=> (and (Inv x) (= xp (bvudiv x #x0002))) (Inv xp))))

; Bad: x > 200 (unreachable from 100 by halving)
(assert (forall ((x (_ BitVec 16)))
  (=> (and (Inv x) (bvugt x #x00C8)) false)))

(check-sat)
