(set-logic QF_FP)
(set-info :status unsat)
; One abstract NaN, despite different sign and stored payload fields.
(assert (distinct
  (fp #b0 (_ bv9223372036854775807 63) (_ bv1 128))
  (fp #b1 (_ bv9223372036854775807 63) (_ bv2 128))))
(check-sat)
