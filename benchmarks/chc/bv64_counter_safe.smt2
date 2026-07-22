; Simple BV64 counter benchmark for #7975 validation.
; Models a 64-bit counter incrementing from 1, property: counter != 0.
; Expected: sat (safe)
;
; Init: x = 1
; Trans: x' = bvadd(x, 1), guard bvult(x, 10)
; Bad: x = 0 (unreachable since counter starts at 1 and guard limits it)

(set-logic HORN)

(declare-fun Inv ((_ BitVec 64)) Bool)

; Init: x = 1
(assert (forall ((x (_ BitVec 64)))
  (=> (= x #x0000000000000001) (Inv x))))

; Trans: x' = x + 1, guarded by x < 10
(assert (forall ((x (_ BitVec 64)) (xp (_ BitVec 64)))
  (=> (and (Inv x)
           (bvult x #x000000000000000A)
           (= xp (bvadd x #x0000000000000001)))
      (Inv xp))))

; Bad: Inv(x) and x = 0 (unreachable)
(assert (forall ((x (_ BitVec 64)))
  (=> (and (Inv x) (= x #x0000000000000000)) false)))

(check-sat)
