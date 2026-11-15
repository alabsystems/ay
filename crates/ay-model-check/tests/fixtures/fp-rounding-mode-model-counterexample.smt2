; A free mode with model value RTP rounds 2.5 to 3, never to 2.
; Expected outputs, in order: unsat, sat.
(set-logic QF_FP)
(declare-const mode RoundingMode)
(define-fun input () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RNE (/ 5 2)))
(assert (= mode RTP))
(push 1)
(assert (= (fp.roundToIntegral mode input) ((_ to_fp 8 24) RNE 2)))
(check-sat)
(pop 1)
(assert (= (fp.roundToIntegral mode input) ((_ to_fp 8 24) RNE 3)))
(check-sat)
