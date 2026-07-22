; Regression test for #297
; QF_LIA with ITE in arithmetic expression - should be SAT
; Bug: missing lift_arithmetic_ite_all caused unknown
(set-logic QF_LIA)
(declare-const D Int)
(declare-const E Int)
(declare-const F Int)
(assert (< E F))
(assert (> (ite (>= E 0) (* 2 D) D) 1))
(check-sat)
; Expected: sat (E=0, F=1, D=1 is a solution)
