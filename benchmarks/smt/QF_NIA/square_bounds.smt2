; QF_NIA benchmark: square bounds
; x^2 = 9 with -5 <= x <= 5
; Expected: SAT (x = 3 or x = -3)
(set-logic QF_NIA)
(declare-fun x () Int)
(assert (>= x (- 5)))
(assert (<= x 5))
(assert (= (* x x) 9))
(check-sat)
(exit)
