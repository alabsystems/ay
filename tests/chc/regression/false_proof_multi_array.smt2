; Regression test for #8675: false PROOF with multiple array parameters
; The error IS reachable (expected: unsat / Unsafe).
;
; Uses 2 array params (obj_size, obj_type) to trigger the aggressive
; array generalization (max_array_params >= 2 path in PDR).
; Stores obj_size[0]=64 and obj_type[0]=1 at init.
; The error checks select(obj_size, 0) != 32 (64 != 32, reachable).

(set-logic HORN)

(declare-fun Inv ((Array Int Int) (Array Int Int) Int) Bool)

; Fact: obj_size[0]=64, obj_type[0]=1, id=0
(assert (forall ((obj_size (Array Int Int)) (obj_type (Array Int Int)) (id Int))
  (=> (and (= id 0)
           (= obj_size (store ((as const (Array Int Int)) 0) 0 64))
           (= obj_type (store ((as const (Array Int Int)) 0) 0 1)))
      (Inv obj_size obj_type id))))

; Transition: Inv(obj_size, obj_type, id) => Inv(obj_size, obj_type, id)
; Identity transition (arrays pass through unchanged).
; The self-loop keeps the same state, exercising the PDR invariant synthesis.
(assert (forall ((obj_size (Array Int Int)) (obj_type (Array Int Int)) (id Int))
  (=> (Inv obj_size obj_type id)
      (Inv obj_size obj_type id))))

; Error: Inv(obj_size, obj_type, id) /\ select(obj_size, id) != 32 => false
; Since obj_size[0] = 64 and 64 != 32, this IS reachable -> UNSAFE
(assert (forall ((obj_size (Array Int Int)) (obj_type (Array Int Int)) (id Int))
  (=> (and (Inv obj_size obj_type id)
           (not (= (select obj_size id) 32)))
      false)))

(check-sat)
