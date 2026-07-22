(set-logic QF_S)
(declare-const x String)
(assert (str.contains "ab" (str.++ x "c")))
(check-sat)
