; Linear system with unique solution
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (= (+ x y z) 6.0))
(assert (= (+ (* 2.0 x) (- y) z) 1.0))
(assert (= (- x (* 2.0 y) z) (- 3.0)))
(check-sat)
