; model-checker-consumer-style Vec::pop CHC benchmark.
; Models: A vector as (Array Int Int) with length tracking.
; The loop pushes values, then pops one and checks the field.
;
; State: (arr: Array Int Int, len: Int, val: Int, phase: Int)
; Phase 0: push values [10, 20, 30]
; Phase 1: pop last value
; Phase 2: check popped value = 30
;
; Expected: sat (safe) - Z3 Spacer proves this
(set-logic HORN)

(declare-fun Inv (
  (Array Int Int)  ; backing array
  Int              ; length
  Int              ; popped value
  Int              ; phase counter
) Bool)

; Init: empty array, length 0, phase 0
(assert (forall ((arr (Array Int Int)) (len Int) (val Int) (phase Int))
  (=> (and (= len 0) (= val 0) (= phase 0))
      (Inv arr len val phase))))

; Push 10 at index 0 (phase 0 -> 1)
(assert (forall ((arr (Array Int Int)) (len Int) (val Int) (phase Int)
                 (arr1 (Array Int Int)) (len1 Int) (val1 Int) (phase1 Int))
  (=> (and (Inv arr len val phase)
           (= phase 0)
           (= arr1 (store arr 0 10))
           (= len1 1)
           (= val1 val)
           (= phase1 1))
      (Inv arr1 len1 val1 phase1))))

; Push 20 at index 1 (phase 1 -> 2)
(assert (forall ((arr (Array Int Int)) (len Int) (val Int) (phase Int)
                 (arr1 (Array Int Int)) (len1 Int) (val1 Int) (phase1 Int))
  (=> (and (Inv arr len val phase)
           (= phase 1)
           (= arr1 (store arr 1 20))
           (= len1 2)
           (= val1 val)
           (= phase1 2))
      (Inv arr1 len1 val1 phase1))))

; Push 30 at index 2 (phase 2 -> 3)
(assert (forall ((arr (Array Int Int)) (len Int) (val Int) (phase Int)
                 (arr1 (Array Int Int)) (len1 Int) (val1 Int) (phase1 Int))
  (=> (and (Inv arr len val phase)
           (= phase 2)
           (= arr1 (store arr 2 30))
           (= len1 3)
           (= val1 val)
           (= phase1 3))
      (Inv arr1 len1 val1 phase1))))

; Pop: read arr[len-1], decrease length (phase 3 -> 4)
(assert (forall ((arr (Array Int Int)) (len Int) (val Int) (phase Int)
                 (arr1 (Array Int Int)) (len1 Int) (val1 Int) (phase1 Int))
  (=> (and (Inv arr len val phase)
           (= phase 3)
           (> len 0)
           (= val1 (select arr (- len 1)))
           (= len1 (- len 1))
           (= arr1 arr)
           (= phase1 4))
      (Inv arr1 len1 val1 phase1))))

; Safety: after pop (phase 4), popped value should be 30
(assert (forall ((arr (Array Int Int)) (len Int) (val Int) (phase Int))
  (=> (and (Inv arr len val phase)
           (= phase 4)
           (not (= val 30)))
      false)))

(check-sat)
(exit)
