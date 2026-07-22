(set-logic QF_SLIA)
(declare-const n Int)
(assert (>= (str.indexof "a" "ca" n) 0))
(check-sat)
