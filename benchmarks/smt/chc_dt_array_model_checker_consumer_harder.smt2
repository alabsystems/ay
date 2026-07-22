; Harder model-checker-consumer-style CHC: struct allocation with field mutation via memory writes.
;
; Models a function that:
; 1. Allocates Pair(42, true) at BV64 address 0
; 2. Reads and writes struct fields through memory (byte-level)
; 3. Transition: allocates another object at address=8*count
; 4. Property: obj_valid[0] AND mem[0] = 0x2A after any number of transitions
;
; This tests: BV64 array keys, symbolic store indices, cross-array invariant,
; BV arithmetic on addresses (8*count = count << 3).
;
; Expected: sat (safe)
(set-logic HORN)

(declare-fun |inv| (
  (Array (_ BitVec 32) Bool)
  (Array (_ BitVec 32) (_ BitVec 32))
  (Array (_ BitVec 64) (_ BitVec 8))
  (_ BitVec 32)
) Bool)

; Init: obj 0 valid, size 4, mem[0] = 0x2A, count = 1
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
        (= m  (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00) #x0000000000000000 #x2A))
        (= cnt #x00000001)
      )
      (inv ov os m cnt)
    )
  )
)

; Trans: allocate another object at symbolic index.
; Memory written at address = zext(count) * 8 (object 0 is at address 0).
; Since count starts at 1, writes go to address >= 8, never touching address 0.
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
    (ov2 (Array (_ BitVec 32) Bool))
    (os2 (Array (_ BitVec 32) (_ BitVec 32)))
    (m2  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt2 (_ BitVec 32))
  )
    (=>
      (and
        (inv ov os m cnt)
        (bvult cnt #x0000000A)
        (= ov2 (store ov cnt true))
        (= os2 (store os cnt #x00000008))
        ; Write 0xFF at address zext(cnt)*8 — never touches address 0 (cnt >= 1)
        (= m2  (store m (bvmul ((_ zero_extend 32) cnt) #x0000000000000008) #xFF))
        (= cnt2 (bvadd cnt #x00000001))
      )
      (inv ov2 os2 m2 cnt2)
    )
  )
)

; Bad: obj_valid[0] AND mem[0] != 0x2A
; Safe because: init sets mem[0]=0x2A, transitions only write at 8*cnt (cnt >= 1),
; so address 0 is never touched.
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool))
    (os (Array (_ BitVec 32) (_ BitVec 32)))
    (m  (Array (_ BitVec 64) (_ BitVec 8)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (inv ov os m cnt)
        (select ov #x00000000)
        (not (= (select m #x0000000000000000) #x2A))
      )
      false
    )
  )
)

(check-sat)
(exit)
