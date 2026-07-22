; Array non-interference: writes at different indices preserve properties.
; This is the key pattern in model-checker-consumer harnesses where:
; - Object 0's fields are set in init
; - Loop allocates objects 1..N at different indices
; - Property checks object 0's fields are preserved
;
; The invariant must express: select(arr, 0) is preserved across stores at i != 0
; This requires array theory reasoning (ROW2 axioms).
;
; Expected: sat (safe)
(set-logic HORN)

(declare-fun |inv| (
  (Array (_ BitVec 32) (_ BitVec 32))
  (_ BitVec 32)
) Bool)

; Init: arr[0] = 42, cnt = 1
(assert
  (forall (
    (arr (Array (_ BitVec 32) (_ BitVec 32)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (= arr (store ((as const (Array (_ BitVec 32) (_ BitVec 32))) #x00000000) #x00000000 #x0000002A))
        (= cnt #x00000001)
      )
      (inv arr cnt)
    )
  )
)

; Transition: write value cnt at index cnt, increment cnt
; This never writes at index 0 because cnt >= 1
(assert
  (forall (
    (arr (Array (_ BitVec 32) (_ BitVec 32)))
    (cnt (_ BitVec 32))
    (arr2 (Array (_ BitVec 32) (_ BitVec 32)))
    (cnt2 (_ BitVec 32))
  )
    (=>
      (and
        (inv arr cnt)
        (bvult cnt #x00000010)
        (= arr2 (store arr cnt cnt))
        (= cnt2 (bvadd cnt #x00000001))
      )
      (inv arr2 cnt2)
    )
  )
)

; Property: arr[0] is always 42
(assert
  (forall (
    (arr (Array (_ BitVec 32) (_ BitVec 32)))
    (cnt (_ BitVec 32))
  )
    (=>
      (and
        (inv arr cnt)
        (not (= (select arr #x00000000) #x0000002A))
      )
      false
    )
  )
)

(check-sat)
(exit)
