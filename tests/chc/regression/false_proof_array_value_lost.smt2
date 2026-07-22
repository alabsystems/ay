; Regression test for #8675: false PROOF when array value gets lost
; through store/select chain in PDR generalization.
;
; This encodes a pattern where:
; 1. Init stores value 64 into arr[id]
; 2. A loop modifies a DIFFERENT array element (arr[1]) each iteration
; 3. Error checks arr[id] != 32 (should be reachable since arr[0]=64)
;
; The key: the transition modifies the array (via store to index 1),
; so the PDR generalizer might drop the constraint about arr[0]=64
; thinking the array constraint is not needed for inductiveness.
; With >=2 array params AND self-loops that modify arrays,
; the ArraySelectIndexGeneralizer can be too aggressive.

(set-logic HORN)

(declare-fun Inv ((Array Int Int) (Array Int Int) Int Int) Bool)

; Fact: obj_size[0]=64, obj_flags[0]=1, id=0, ctr=0
(assert (forall ((obj_size (Array Int Int)) (obj_flags (Array Int Int)) (id Int) (ctr Int))
  (=> (and (= id 0)
           (= ctr 0)
           (= obj_size (store ((as const (Array Int Int)) 0) 0 64))
           (= obj_flags (store ((as const (Array Int Int)) 0) 0 1)))
      (Inv obj_size obj_flags id ctr))))

; Transition: Inv(obj_size, obj_flags, id, ctr) /\ ctr < 3
;   => Inv(store(obj_size, 1, ctr), obj_flags, id, ctr+1)
; Modifies obj_size[1] (NOT obj_size[0]!) each iteration.
; obj_size[0] should remain 64 throughout.
(assert (forall ((obj_size (Array Int Int)) (obj_flags (Array Int Int))
                 (id Int) (ctr Int)
                 (obj_size2 (Array Int Int)) (ctr2 Int))
  (=> (and (Inv obj_size obj_flags id ctr)
           (< ctr 3)
           (= ctr2 (+ ctr 1))
           (= obj_size2 (store obj_size 1 ctr)))
      (Inv obj_size2 obj_flags id ctr2))))

; Error: Inv(obj_size, obj_flags, id, ctr) /\ ctr >= 2
;        /\ select(obj_size, id) != 32 => false
; Since id=0, obj_size[0]=64, and 64 != 32, this IS reachable -> UNSAFE
(assert (forall ((obj_size (Array Int Int)) (obj_flags (Array Int Int))
                 (id Int) (ctr Int))
  (=> (and (Inv obj_size obj_flags id ctr)
           (>= ctr 2)
           (not (= (select obj_size id) 32)))
      false)))

(check-sat)
