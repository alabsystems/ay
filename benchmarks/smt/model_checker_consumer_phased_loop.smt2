; model-checker-consumer-style phased loop CHC benchmark (no arrays).
; Models: A program that goes through phases 0->1->2->3, accumulating a value.
; Phase 0: x = 10
; Phase 1: y = x + 5
; Phase 2: z = y * 2
; Safety: at phase 2, z = 30
;
; Expected: sat (safe) - Z3 Spacer proves this
(set-logic HORN)

(declare-fun Inv (Int Int Int Int) Bool)

; Init: phase=0, x=10, y=0, z=0
(assert (forall ((phase Int) (x Int) (y Int) (z Int))
  (=> (and (= phase 0) (= x 10) (= y 0) (= z 0))
      (Inv phase x y z))))

; Phase 0 -> 1: set y = x + 5
(assert (forall ((phase Int) (x Int) (y Int) (z Int)
                 (phase1 Int) (x1 Int) (y1 Int) (z1 Int))
  (=> (and (Inv phase x y z)
           (= phase 0)
           (= phase1 1)
           (= x1 x)
           (= y1 (+ x 5))
           (= z1 z))
      (Inv phase1 x1 y1 z1))))

; Phase 1 -> 2: set z = y * 2
(assert (forall ((phase Int) (x Int) (y Int) (z Int)
                 (phase1 Int) (x1 Int) (y1 Int) (z1 Int))
  (=> (and (Inv phase x y z)
           (= phase 1)
           (= phase1 2)
           (= x1 x)
           (= y1 y)
           (= z1 (* y 2)))
      (Inv phase1 x1 y1 z1))))

; Safety: at phase 2, z should be 30
(assert (forall ((phase Int) (x Int) (y Int) (z Int))
  (=> (and (Inv phase x y z)
           (= phase 2)
           (not (= z 30)))
      false)))

(check-sat)
(exit)
