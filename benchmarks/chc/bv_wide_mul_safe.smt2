; CHC with wide BV multiplication — exercises delayed internalization in CHC/PDR path
; Expected: sat (safe)
;
; Models a counter that doubles each step via 16-bit multiplication:
;   init: x = 1
;   trans: x' = bvmul(x, 2)  (wide mul: 16-bit, 2 args triggers delayed internalization)
;   bad: x = 0 AND x != 1  (unreachable: doubling 1 never reaches 0 within BV range)
;
; The invariant is: x != 0 (or more precisely, x is a power of 2)
; PDR must reason about BV multiplication through the delayed internalization loop.

(set-logic HORN)

(declare-fun Inv ((_ BitVec 16)) Bool)

; Init: x = 1
(assert (forall ((x (_ BitVec 16)))
  (=> (= x #x0001) (Inv x))))

; Trans: x' = x * 2 (wide multiplication, triggers delayed internalization)
(assert (forall ((x (_ BitVec 16)) (xp (_ BitVec 16)))
  (=> (and (Inv x) (= xp (bvmul x #x0002))) (Inv xp))))

; Bad: Inv(x) and x = 0 and x was not the initial value
; Actually simpler: Inv(x) and x = 3 (odd number != 1, unreachable by doubling)
(assert (forall ((x (_ BitVec 16)))
  (=> (and (Inv x) (= x #x0003)) false)))

(check-sat)
