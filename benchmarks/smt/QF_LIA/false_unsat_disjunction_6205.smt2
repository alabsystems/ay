; Regression test for #6205: QF_LIA false UNSAT on disjunctive formulas.
; Root cause: atom_slack cache reuse after push/pop skipped constant compensation
; when the slack was created by a different atom via expr_to_slack cache.
; Expected: sat (model: i=0, n=0, k=1, i_prime=1)
(set-logic QF_LIA)
(declare-const i Int)
(declare-const n Int)
(declare-const k Int)
(declare-const i_prime Int)
(assert (>= i 0))
(assert (<= i n))
(assert (or (< i n) (> k 0)))
(assert (= i_prime (+ i 1)))
(assert (not (and (>= i_prime 0) (<= i_prime n))))
(check-sat)
; expected: sat
