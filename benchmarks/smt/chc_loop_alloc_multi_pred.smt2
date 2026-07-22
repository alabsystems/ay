; Loop allocation with multi-predicate CHC (model-checker-consumer-like pattern).
; Models: init -> loop body -> allocate(n) -> write_field(n) -> property check
;
; 3 predicates: |loop_inv|, |post_alloc|, |post_write|
; 3 array params: obj_valid (BV32->Bool), obj_size (BV32->BV32), mem (BV64->BV8)
; 1 scalar: count (BV32)
;
; Property: after loop, obj 0 is valid with size >= 1 and mem[0] = 0x42
;
; Expected: sat (safe)
(set-logic HORN)

(declare-fun |loop_inv| (
  (Array (_ BitVec 32) Bool)
  (Array (_ BitVec 32) (_ BitVec 32))
  (Array (_ BitVec 64) (_ BitVec 8))
  (_ BitVec 32)
) Bool)

(declare-fun |post_alloc| (
  (Array (_ BitVec 32) Bool)
  (Array (_ BitVec 32) (_ BitVec 32))
  (Array (_ BitVec 64) (_ BitVec 8))
  (_ BitVec 32)
  (_ BitVec 32)
) Bool)

(declare-fun |post_write| (
  (Array (_ BitVec 32) Bool)
  (Array (_ BitVec 32) (_ BitVec 32))
  (Array (_ BitVec 64) (_ BitVec 8))
  (_ BitVec 32)
) Bool)

; Init: allocate object 0, set size=4, write 0x42 at mem[0]
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (= ov (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000000 true))
        (= os (store ((as const (Array (_ BitVec 32) (_ BitVec 32))) #x00000000) #x00000000 #x00000004))
        (= m  (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00) #x0000000000000000 #x42))
        (= cnt #x00000001)
      )
      (loop_inv ov os m cnt)
    )
  )
)

; Loop body: allocate next object (cnt), then write its field
; loop_inv -> post_alloc: mark obj cnt as valid, set size
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
    (new_cnt (_ BitVec 32))
  )
    (=>
      (and
        (loop_inv ov os m cnt)
        (bvult cnt #x00000004)  ; loop bound: allocate up to 4 objects
        (= new_cnt (bvadd cnt #x00000001))
      )
      (post_alloc
        (store ov cnt true)
        (store os cnt #x00000002)
        m
        cnt
        new_cnt)
    )
  )
)

; post_alloc -> post_write: write a byte to memory at address = zext(cnt)*8
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
    (new_cnt (_ BitVec 32))
  )
    (=>
      (post_alloc ov os m cnt new_cnt)
      (post_write
        ov os
        (store m (bvmul ((_ zero_extend 32) cnt) #x0000000000000008) #xAA)
        new_cnt)
    )
  )
)

; post_write -> loop_inv: continue loop
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=>
      (post_write ov os m cnt)
      (loop_inv ov os m cnt)
    )
  )
)

; Property: object 0 is always valid with size >= 1, and mem[0] = 0x42
; This is safe because init sets these and the loop never modifies obj 0's fields
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (loop_inv ov os m cnt)
        (or
          (not (select ov #x00000000))
          (= (select os #x00000000) #x00000000)
          (not (= (select m #x0000000000000000) #x42))
        )
      )
      false
    )
  )
)

(check-sat)
(exit)
