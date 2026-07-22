(set-logic QF_S)
(declare-const x String)
(assert (= (str.++ x "ab" x) (str.++ x "ba" x)))
(check-sat)
