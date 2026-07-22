; Multi-predicate CHC with arrays: models a function call chain.
; init -> allocate -> read_field -> check_property
;
; Two predicates: |allocate| and |read_field|
;
; Expected: sat (safe)
(set-logic HORN)

(declare-fun |allocate| (
  (Array (_ BitVec 32) Bool)
  (Array (_ BitVec 64) (_ BitVec 8))
  (_ BitVec 32)
  (_ BitVec 64)
) Bool)

(declare-fun |read_field| (
  (Array (_ BitVec 32) Bool)
  (Array (_ BitVec 64) (_ BitVec 8))
  (_ BitVec 32)
  (_ BitVec 64)
  (_ BitVec 8)
) Bool)

; Init: empty state, allocate object 0
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
    (addr (_ BitVec 64))
  )
    (=>
      (and
        (= ov (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000000 true))
        (= m  (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00) #x0000000000000000 #x2A))
        (= cnt #x00000001)
        (= addr #x0000000000000000)
      )
      (allocate ov m cnt addr)
    )
  )
)

; allocate -> read_field: read the value at address
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))(m (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))(addr (_ BitVec 64))
    (val (_ BitVec 8))
  )
    (=>
      (and
        (allocate ov m cnt addr)
        (= val (select m addr))
      )
      (read_field ov m cnt addr val)
    )
  )
)

; Bad: read_field and val != 0x2A
; This should be safe: we wrote 0x2A at address 0 in init.
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))(m (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))(addr (_ BitVec 64))
    (val (_ BitVec 8))
  )
    (=>
      (and
        (read_field ov m cnt addr val)
        (= addr #x0000000000000000)
        (not (= val #x2A))
      )
      false
    )
  )
)

(check-sat)
(exit)
