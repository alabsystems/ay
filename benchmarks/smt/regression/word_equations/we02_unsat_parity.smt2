(set-logic QF_S)
(declare-const x String)
(assert (= (str.++ x x) "aba"))
(check-sat)
