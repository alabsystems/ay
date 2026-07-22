; Reproducer for Z3 issue #4323 — QF_NIA: slow on (a*b) % 10 == 0.
; Source: https://github.com/Z3Prover/z3/issues/4323
; Symptom: Z3 is extremely slow deciding satisfiability of modular products of
; small nonlinear integer terms. Minimized here to a pair of bounded variables
; whose product must be a multiple of 10.
; Expected: sat (e.g., a=2, b=5).
; Theory: QF_NIA (nonlinear integer arithmetic).
;
; Author: Andrew Yates <andrewyates.name@gmail.com>
(set-logic QF_NIA)
(declare-const a Int)
(declare-const b Int)
(assert (>= a 1))
(assert (<= a 1000))
(assert (>= b 1))
(assert (<= b 1000))
(assert (= (mod (* a b) 10) 0))
(assert (not (= a 10)))
(assert (not (= b 10)))
(assert (not (= a 5)))
(assert (not (= b 5)))
(assert (not (= a 2)))
(assert (not (= b 2)))
(check-sat)
