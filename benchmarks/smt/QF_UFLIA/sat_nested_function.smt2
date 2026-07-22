; Test SAT: h(h(c)) = h(c) is satisfiable
(set-logic QF_UFLIA)
(declare-fun h (Int) Int)
(declare-const c Int)
(assert (= (h (h c)) (h c)))
(check-sat)
; Expected: sat
