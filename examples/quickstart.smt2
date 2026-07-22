(set-info :status sat)
(set-logic QF_LIA)

(declare-const x Int)
(declare-const y Int)

(assert (= (+ x y) 7))
(assert (> x 2))
(assert (< y 4))

(check-sat)
(get-model)
