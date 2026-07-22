(set-logic QF_S)
(declare-const x String)
(assert (str.suffixof "c" (str.++ x "b")))
(check-sat)
