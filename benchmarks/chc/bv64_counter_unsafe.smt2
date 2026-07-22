; Simple BV64 counter benchmark (UNSAFE) for #7975 validation.
; Models a 64-bit counter incrementing from 0, property: counter < 5.
; Expected: unsat (unsafe) - counter reaches 5 after 5 steps.
;
; Init: x = 0
; Trans: x' = bvadd(x, 1)
; Bad: x >= 5

(set-logic HORN)

(declare-fun Inv ((_ BitVec 64)) Bool)

; Init: x = 0
(assert (forall ((x (_ BitVec 64)))
  (=> (= x #x0000000000000000) (Inv x))))

; Trans: x' = x + 1 (unbounded)
(assert (forall ((x (_ BitVec 64)) (xp (_ BitVec 64)))
  (=> (and (Inv x)
           (= xp (bvadd x #x0000000000000001)))
      (Inv xp))))

; Bad: Inv(x) and x = 5 (reachable after 5 steps)
(assert (forall ((x (_ BitVec 64)))
  (=> (and (Inv x) (= x #x0000000000000005)) false)))

(check-sat)
