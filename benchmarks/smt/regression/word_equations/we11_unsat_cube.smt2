(set-logic QF_S)
(declare-const x String)
(assert (= (str.++ x x x) "ab"))
(check-sat)
