; Reproducer for Z3 issue #7431 — invalid model on to_fp from Real.
; Source: https://github.com/Z3Prover/z3/issues/7431
; Expected: sat (the equation is solvable with v ≈ 2^-5 under RTZ).
(set-logic ALL)
(declare-fun v () Real)
(assert (= ((_ to_fp 2 6) RTZ v) (fp (_ bv1 1) (_ bv0 2) (_ bv0 5))))
(check-sat)
