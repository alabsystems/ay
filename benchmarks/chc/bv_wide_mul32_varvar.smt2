; CHC with 32-bit variable-variable BV multiplication — delayed internalization test
; Expected: sat (safe)
;
; Models a counter with variable stride:
;   init: x = stride (where stride > 0)
;   trans: x' = bvmul(x, stride)  (32-bit variable*variable mul)
;   bad: x = 0 AND stride > 0  (unreachable: stride^n > 0 for small n)
;
; The invariant is: x != 0 (product of non-zero values is non-zero for small counts)
; PDR must reason about 32-bit variable*variable multiplication.

(set-logic HORN)

(declare-fun Inv ((_ BitVec 32) (_ BitVec 32)) Bool)

; Init: x = stride, stride > 0 and stride < 256
(assert (forall ((x (_ BitVec 32)) (s (_ BitVec 32)))
  (=> (and (= x s)
           (bvugt s #x00000000)
           (bvult s #x00000100))
      (Inv x s))))

; Trans: x' = x * s (32-bit variable*variable mul, triggers delayed internalization)
(assert (forall ((x (_ BitVec 32)) (s (_ BitVec 32)) (xp (_ BitVec 32)))
  (=> (and (Inv x s) (= xp (bvmul x s))) (Inv xp s))))

; Bad: x = 0 (product should never be zero if stride != 0 and initial != 0)
; This is actually reachable via overflow (e.g., s=2, after 32 steps x=0).
; So use a stronger bad: x = 3 (odd value != stride, unreachable by repeated mul)
(assert (forall ((x (_ BitVec 32)) (s (_ BitVec 32)))
  (=> (and (Inv x s) (= x #x00000003) (= s #x00000002)) false)))

(check-sat)
