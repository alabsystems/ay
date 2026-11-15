(set-logic QF_FF)
(declare-const x (_ FiniteField 7))
(assert (= (ff.mul x x) #f2m7))
(check-sat)
