; Simple QF_NIA benchmark: satisfiable product
; x * y = 6 with x > 0 and y > 0
; Expected: SAT (e.g., x=2, y=3)
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x 0))
(assert (> y 0))
(assert (= (* x y) 6))
(check-sat)
(exit)
