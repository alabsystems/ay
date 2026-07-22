(set-logic QF_FP)
(assert (fp.isNegative
  (fp.rem (fp #b1 #b11110 #b1111100110)
          (fp #b1 #b00000 #b1001101111))))
(check-sat)
