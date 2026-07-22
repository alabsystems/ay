(set-logic QF_FP)
(assert (fp.isNormal ((_ to_fp 4 4) RTN (fp #b0 #b01000110 #b10100000111101000011111))))
(check-sat)
