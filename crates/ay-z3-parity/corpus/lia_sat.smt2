; expected: sat
; QF_LIA — a small satisfiable linear-integer system.
(set-logic QF_LIA)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y) 10))
(assert (> x 3))
(assert (< y 4))
(check-sat)
