; Authored source-derived BMC kernel, not a captured MODEL_CHECKER_CONSUMER compiler export.
; MODEL_CHECKER_CONSUMER d85cd869b254d8b848853b64787e24f82c35ff1c:
; tests/trust-lane/float-intrinsics/relation_arithmetic.rs,
; arith_sym_sum_is_x_holds. Ground min(+0,-0) keeps its fresh Bool choice
; (statement/intrinsics/math.rs); arithmetic uses float_arithmetic.rs's
; BV sign/exponent/significand -> FP -> fp.add RNE -> fp.to_ieee_bv route.
; Expected UNSAT by source reasoning: adding either zero is exact for every
; finite nonzero x, including subnormals, and preserves every bit under RNE.
; This is exact BMC FP arithmetic, not the CHC uninterpreted float table.
(set-logic ALL)
(set-info :status unsat)
(declare-const x (_ BitVec 32))
(declare-const minmax_equal_choice Bool)
(define-fun m () (_ BitVec 32)
  (ite minmax_equal_choice #x00000000 #x80000000))
; Preserve kani::assume(x.is_finite() && x != 0.0), excluding BOTH zeros.
(assert (and
  (not (= ((_ extract 30 23) x) #xff))
  (not (= (bvand x #x7fffffff) #x00000000))))
(define-fun x_fp () (_ FloatingPoint 8 24)
  (fp ((_ extract 31 31) x) ((_ extract 30 23) x) ((_ extract 22 0) x)))
(define-fun m_fp () (_ FloatingPoint 8 24)
  (fp ((_ extract 31 31) m) ((_ extract 30 23) m) ((_ extract 22 0) m)))
(define-fun sum_bits () (_ BitVec 32)
  (fp.to_ieee_bv (fp.add RNE x_fp m_fp)))
; Negate assert!((x + m).to_bits() == x.to_bits()).
(assert (not (= sum_bits x)))
(check-sat)
(exit)
