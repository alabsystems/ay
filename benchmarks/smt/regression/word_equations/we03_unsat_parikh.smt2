(set-logic QF_S)
(declare-const x String)
(assert (= (str.++ "a" x) (str.++ x "b")))
(check-sat)
