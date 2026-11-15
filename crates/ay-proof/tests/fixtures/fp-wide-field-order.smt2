; Classification and ordering need no exponent-sized rational reconstruction.
(set-logic QF_FP)
(assert (not (and
  (fp.isNaN (_ NaN 15 113))
  (fp.lt (fp #b0 #b111111111111111111111111111111111111111111111111111111111111110 #b00) (_ +oo 63 3))
  (fp.lt (fp #b1 #b111111111111111111111111111111111111111111111111111111111111110 #b01) (fp #b1 #b111111111111111111111111111111111111111111111111111111111111110 #b00))
  (= (fp.neg (_ +zero 63 3)) (_ -zero 63 3))
)))
(check-sat)
