; Minimal BV64 CHC benchmark mimicking a model-checker-consumer harness.
; Tests: BV64 constant handling in BvToInt, Array(BV64, BV8) memory model.
;
; Models: simple loop writing to memory at incrementing BV64 addresses.
; Init: mem[0] = 0xFF, counter = 1
; Trans: mem[counter] = 0x42, counter++
; Property: mem[0] = 0xFF (never overwritten since counter starts at 1)
;
; Expected: sat (safe)
(set-logic HORN)

(declare-fun |inv| (
  (Array (_ BitVec 64) (_ BitVec 8))
  (_ BitVec 64)
) Bool)

; Init: write 0xFF at address 0, counter = 1
(assert
  (forall (
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 64))
  )
    (=>
      (and
        (= m (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)
              #x0000000000000000 #xFF))
        (= cnt #x0000000000000001)
      )
      (inv m cnt)
    )
  )
)

; Trans: write 0x42 at address=counter, then counter++
; Since counter >= 1, never overwrites address 0.
(assert
  (forall (
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 64))
    (m2 (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt2 (_ BitVec 64))
  )
    (=>
      (and
        (inv m cnt)
        (bvult cnt #x000000000000000A)
        (= m2  (store m cnt #x42))
        (= cnt2 (bvadd cnt #x0000000000000001))
      )
      (inv m2 cnt2)
    )
  )
)

; Bad: mem[0] != 0xFF
(assert
  (forall (
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 64))
  )
    (=>
      (and
        (inv m cnt)
        (not (= (select m #x0000000000000000) #xFF))
      )
      false
    )
  )
)

(check-sat)
(exit)
