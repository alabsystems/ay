; Regression test for #6207: QF_LIA false UNSAT with step-2 increment.
; Expected: sat (model: i=1, n=2, i_prime=3)
(set-logic QF_LIA)
(declare-const i Int)
(declare-const n Int)
(declare-const i_prime Int)
(assert (>= n 2))
(assert (>= i 0))
(assert (<= i n))
(assert (< i n))
(assert (= i_prime (+ i 2)))
(assert (not (and (>= i_prime 0) (<= i_prime n))))
(check-sat)
; expected: sat
