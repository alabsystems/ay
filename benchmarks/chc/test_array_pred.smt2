; Simple CHC benchmark with Array-sorted predicate parameters
; Mimics model-checker-consumer's --ay-chc-track=mem pattern with array state
(set-logic HORN)

; Predicate with array-sorted parameter
(declare-fun inv ((Array (_ BitVec 32) (_ BitVec 32)) (_ BitVec 32)) Bool)

; Initial state: arr[0] = 42, i = 0
(assert (forall ((arr (Array (_ BitVec 32) (_ BitVec 32))) (i (_ BitVec 32)))
  (=> (and (= (select arr (_ bv0 32)) (_ bv42 32)) (= i (_ bv0 32)))
      (inv arr i))))

; Transition: arr' = store(arr, i, select(arr, i) + 1), i' = i + 1
(assert (forall ((arr (Array (_ BitVec 32) (_ BitVec 32))) (i (_ BitVec 32))
                 (arr2 (Array (_ BitVec 32) (_ BitVec 32))) (i2 (_ BitVec 32)))
  (=> (and (inv arr i)
           (bvult i (_ bv10 32))
           (= arr2 (store arr i (bvadd (select arr i) (_ bv1 32))))
           (= i2 (bvadd i (_ bv1 32))))
      (inv arr2 i2))))

; Safety: arr[0] >= 42 always holds
(assert (forall ((arr (Array (_ BitVec 32) (_ BitVec 32))) (i (_ BitVec 32)))
  (=> (inv arr i)
      (not (bvult (select arr (_ bv0 32)) (_ bv42 32))))))

(check-sat)
