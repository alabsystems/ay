; Simple linear constraints
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (= (+ x y) 10.0))
(assert (= (- x y) 2.0))
(check-sat)
