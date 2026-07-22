(set-logic QF_FP)
(assert (fp.isInfinite ((_ to_fp 3 5) RTN (fp #b1 #b00000 #b0010000))))
(check-sat)
