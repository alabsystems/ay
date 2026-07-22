; Part of #8660 Phase 2: array invariant synthesis.
; mem[0]=42 initially, increments by 1 in lockstep with counter i.
; Transition gated by i<10, so mem[0] stays bounded <= 52 <= 100.
; Safety query: (<= (select mem 0) 100).
;
; Requires the algebraic synthesizer to propose both a lower bound
; (>= (select mem 0) 42) AND the same-delta cross-product invariant
; (= (select mem 0) (+ i 42)) combining the array cell with the scalar
; counter. Plain fact-clause conjunct lifting (Phase 1) is insufficient
; because the raw equality is not self-inductive and the weakened >= bound
; alone cannot close the upper-bound query.
;
; Baseline before the fix: z3 "sat" (instant) vs ay "unknown" (timeout).
(set-logic HORN)

(declare-fun inv ((Array Int Int) (Array Int Int) Int) Bool)

(assert (forall ((mem (Array Int Int)) (valid (Array Int Int)) (i Int))
  (=> (and (= (select mem 0) 42) (= (select valid 0) 1) (= i 0))
      (inv mem valid i))))

(assert (forall ((mem (Array Int Int)) (valid (Array Int Int)) (i Int)
                 (mem2 (Array Int Int)) (valid2 (Array Int Int)) (i2 Int))
  (=> (and (inv mem valid i)
           (< i 10)
           (= mem2 (store mem 0 (+ (select mem 0) 1)))
           (= valid2 valid)
           (= i2 (+ i 1)))
      (inv mem2 valid2 i2))))

(assert (forall ((mem (Array Int Int)) (valid (Array Int Int)) (i Int))
  (=> (inv mem valid i)
      (<= (select mem 0) 100))))

(check-sat)
