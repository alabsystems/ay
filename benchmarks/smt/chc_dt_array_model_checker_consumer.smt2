; model-checker-consumer-style CHC with datatypes + Array-sorted predicate parameters.
; Models: struct allocation in heap (stored via BV64 memory array),
; field read-back, and property assertion.
;
; Pattern: allocate Pair(42, true) at address 0, read back fields, assert unchanged.
;
; Expected: sat (safe)
(set-logic HORN)

; Struct type: Pair with two fields
(declare-datatype Pair ((Pair_mk (fld_0 (_ BitVec 32)) (fld_1 Bool))))

; Predicate: inv(obj_valid, mem, alloc_count)
(declare-fun |inv| (
  (Array (_ BitVec 32) Bool)
  (Array (_ BitVec 64) (_ BitVec 8))
  (_ BitVec 32)
) Bool)

; Init: allocate object 0 with valid=true, write 0x2A (42) to mem[0]
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (= ov (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000000 true))
        (= m  (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00) #x0000000000000000 #x2A))
        (= cnt #x00000001)
      )
      (inv ov m cnt)
    )
  )
)

; Trans: identity (no modification — struct is read-only after allocation)
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=> (inv ov m cnt) (inv ov m cnt))
  )
)

; Bad: obj_valid[0] AND mem[0] != 0x2A (42)
; This should be safe: init writes 0x2A to mem[0] and it's never overwritten.
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (inv ov m cnt)
        (select ov #x00000000)
        (not (= (select m #x0000000000000000) #x2A))
      )
      false
    )
  )
)

(check-sat)
(exit)
