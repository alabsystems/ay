; expected: sat
; QF_IDL — a satisfiable chain of integer differences.
(set-logic QF_IDL)
(set-info :status sat)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (<= (- x y) 2))
(assert (<= (- y z) 3))
(assert (>= (- x z) 1))
(check-sat)
