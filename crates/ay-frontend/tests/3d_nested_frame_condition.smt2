; Edge case: Double nested arrays - heap of heap of values
; Tests 3D nested array frame condition (Issue #85)
(set-logic QF_AUFLIA)

; Level 2 arrays: field_id -> value
; Level 1 arrays: obj_id -> (field_id -> value)
; Level 0 (Heap): heap_id -> (obj_id -> (field_id -> value))

(declare-fun Heap () (Array Int (Array Int (Array Int Int))))
(declare-const obj1 Int)
(declare-const field1 Int)
(declare-const field2 Int)

; Fields are distinct
(assert (not (= field1 field2)))

; Pre-state
(declare-const pre_val Int)
(assert (= pre_val (select (select (select Heap 0) obj1) field2)))

; Update: Heap[0][obj1][field1] = 99
(declare-fun Heap_post () (Array Int (Array Int (Array Int Int))))
(assert (= Heap_post
  (store Heap 0
    (store (select Heap 0) obj1
      (store (select (select Heap 0) obj1) field1 99)))))

; Read field2 from post-state
(declare-const post_val Int)
(assert (= post_val (select (select (select Heap_post 0) obj1) field2)))

; Assert they differ - should be UNSAT if frame condition holds
(assert (not (= pre_val post_val)))

(check-sat)
