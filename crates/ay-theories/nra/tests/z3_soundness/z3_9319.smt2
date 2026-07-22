; Reproducer for Z3 issue #9319 — invalid model on (^ (* x 2.0) (/ 1.0 x)) with x=0.
; Source: https://github.com/Z3Prover/z3/issues/9319
; Expected: sat (the constraint after substituting x=0 yields an undefined `^`
; expression under SMT-LIB's partial-function semantics, so the disequality is
; satisfiable). Alternatively, unsat under a total-function reading. Either way
; Z3's inconsistent model is wrong.
(set-logic QF_NRA)
(declare-const x Real)
(assert (= x 0.0))
(assert (not (= (^ (* x 2.0) (/ 1.0 x))
                (^ (* 0.0 (/ 1.0 x))
                   (* x (/ 1.0 2.0))))))
(check-sat)
