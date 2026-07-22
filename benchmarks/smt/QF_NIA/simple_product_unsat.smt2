; Simple QF_NIA benchmark: unsatisfiable product
; x * y = 7 with x, y in [1, 2]
; Expected: UNSAT (7 is prime, no factorization with factors <= 2)
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= x 1))
(assert (<= x 2))
(assert (>= y 1))
(assert (<= y 2))
(assert (= (* x y) 7))
(check-sat)
(exit)
