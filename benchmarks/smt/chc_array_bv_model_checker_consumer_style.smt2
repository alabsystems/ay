; model-checker-consumer-style CHC with Array-sorted predicate parameters using BV keys.
; Simulates the `--ay-chc-track=mem` pattern: predicates have
; obj_valid: (Array (_ BitVec 32) Bool), obj_size: (Array (_ BitVec 32) (_ BitVec 32))
;
; Invariant: obj_valid[0] = true, obj_size[0] >= 1
; Expected: sat
(set-logic HORN)

(declare-fun Inv ((_ BitVec 32) (Array (_ BitVec 32) Bool) (Array (_ BitVec 32) (_ BitVec 32))) Bool)

; Init: i = 0, obj_valid[0] = true, obj_size[0] = bv1
(assert
  (forall ((v (Array (_ BitVec 32) Bool)) (s (Array (_ BitVec 32) (_ BitVec 32))))
    (=> (and (select (store v (_ bv0 32) true) (_ bv0 32))
             (= (select (store s (_ bv0 32) (_ bv1 32)) (_ bv0 32)) (_ bv1 32)))
        (Inv (_ bv0 32) (store v (_ bv0 32) true) (store s (_ bv0 32) (_ bv1 32))))))

; Trans: i' = i + 1, obj_valid and obj_size preserved
(assert
  (forall ((i (_ BitVec 32)) (v (Array (_ BitVec 32) Bool)) (s (Array (_ BitVec 32) (_ BitVec 32))))
    (=> (Inv i v s)
        (Inv (bvadd i (_ bv1 32)) v s))))

; Query: Inv => obj_valid[0] = true
(assert
  (forall ((i (_ BitVec 32)) (v (Array (_ BitVec 32) Bool)) (s (Array (_ BitVec 32) (_ BitVec 32))))
    (=> (and (Inv i v s) (not (select v (_ bv0 32))))
        false)))

(check-sat)
(exit)
