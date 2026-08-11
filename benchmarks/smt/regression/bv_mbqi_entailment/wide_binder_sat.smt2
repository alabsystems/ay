; A width-32 binder: 4,294,967,296 values. Exhaustive enumeration is capped at
; width 8 (256 values), so ONLY the symbolic entailment check can discharge this.
; `bvand x a` clears bits outside `a`, so it is unsigned-<= `a` for every x.
(set-logic BV)
(declare-fun a () (_ BitVec 32))
(assert (bvugt a #x00000005))
(assert (forall ((x (_ BitVec 32))) (bvule (bvand x a) a)))
(check-sat)
