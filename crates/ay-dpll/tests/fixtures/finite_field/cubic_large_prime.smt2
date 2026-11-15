(set-logic QF_FF)
(declare-const x (_ FiniteField 65537))
(assert (= (ff.mul x x x) #f27m65537))
(check-sat)
