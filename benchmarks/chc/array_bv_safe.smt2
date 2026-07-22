; CHC with BV-indexed Array predicate parameters (model-checker-consumer-like pattern)
; Expected: sat (safe)
;
; P(obj_valid, mem) where:
;   obj_valid: (Array (_ BitVec 32) Bool) — object validity map
;   mem: (Array (_ BitVec 64) (_ BitVec 8)) — byte-level memory
;
; Invariant: obj_valid[0] = true /\ mem[0] = #x2a

(set-logic HORN)

(declare-fun Inv ((Array (_ BitVec 32) Bool) (Array (_ BitVec 64) (_ BitVec 8))) Bool)

; Init: obj_valid[0] = true, mem[0] = 0x2a
(assert (forall ((ov (Array (_ BitVec 32) Bool)) (m (Array (_ BitVec 64) (_ BitVec 8))))
  (=> (and (select ov #x00000000) (= (select m #x0000000000000000) #x2a))
      (Inv ov m))))

; Trans: identity (no change)
(assert (forall ((ov (Array (_ BitVec 32) Bool)) (m (Array (_ BitVec 64) (_ BitVec 8))))
  (=> (Inv ov m) (Inv ov m))))

; Bad: Inv holds but obj_valid[0] = false
(assert (forall ((ov (Array (_ BitVec 32) Bool)) (m (Array (_ BitVec 64) (_ BitVec 8))))
  (=> (and (Inv ov m) (not (select ov #x00000000))) false)))

(check-sat)
