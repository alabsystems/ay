; Regression test for #6206: QF_LIA false UNSAT on implication-encoded formulas.
; Same root cause as #6205: atom_slack reuse without constant compensation.
; Expected: sat (model: i=0, n=0, i_prime=1)
(set-logic QF_LIA)
(declare-const i Int)
(declare-const n Int)
(declare-const i_prime Int)
(assert (>= i 0))
(assert (<= i n))
(assert (or (not (> n 0)) (< i n)))
(assert (= i_prime (+ i 1)))
(assert (not (and (>= i_prime 0) (<= i_prime n))))
(check-sat)
; expected: sat
