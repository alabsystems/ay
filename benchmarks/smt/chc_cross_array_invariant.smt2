; Cross-array invariant: for all allocated objects, valid[i] => size[i] > 0
; This requires a universally quantified invariant over array indices.
;
; Pattern from model-checker-consumer: allocate sets both valid[cnt]=true and size[cnt]=N (N>0).
; Property: valid[0] => size[0] > 0
;
; Expected: sat (safe)
(set-logic HORN)

(declare-fun |inv| (
  (Array (_ BitVec 32) Bool)
  (Array (_ BitVec 32) (_ BitVec 32))
  (_ BitVec 32)
) Bool)

; Init: valid[0]=true, size[0]=4, cnt=1
(assert
  (forall (
    (valid (Array (_ BitVec 32) Bool))
    (sz (Array (_ BitVec 32) (_ BitVec 32)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (= valid (store ((as const (Array (_ BitVec 32) Bool)) false) #x00000000 true))
        (= sz (store ((as const (Array (_ BitVec 32) (_ BitVec 32))) #x00000000) #x00000000 #x00000004))
        (= cnt #x00000001)
      )
      (inv valid sz cnt)
    )
  )
)

; Transition: allocate object cnt with size = cnt+1 (always > 0)
(assert
  (forall (
    (valid (Array (_ BitVec 32) Bool))
    (sz (Array (_ BitVec 32) (_ BitVec 32)))
    (cnt (_ BitVec 32))
    (valid2 (Array (_ BitVec 32) Bool))
    (sz2 (Array (_ BitVec 32) (_ BitVec 32)))
    (cnt2 (_ BitVec 32))
  )
    (=>
      (and
        (inv valid sz cnt)
        (bvult cnt #x00000008)
        (= valid2 (store valid cnt true))
        (= sz2 (store sz cnt (bvadd cnt #x00000001)))
        (= cnt2 (bvadd cnt #x00000001))
      )
      (inv valid2 sz2 cnt2)
    )
  )
)

; Property: valid[0] => size[0] > 0
; Negated: valid[0] AND size[0] = 0 => false
(assert
  (forall (
    (valid (Array (_ BitVec 32) Bool))
    (sz (Array (_ BitVec 32) (_ BitVec 32)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (inv valid sz cnt)
        (select valid #x00000000)
        (= (select sz #x00000000) #x00000000)
      )
      false
    )
  )
)

(check-sat)
(exit)
