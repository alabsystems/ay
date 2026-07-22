; Reproducer for Z3 issue #8185 — invalid model with strings + FP + proofs.
; Source: https://github.com/Z3Prover/z3/issues/8185
; Expected: sat (the constraints are jointly satisfiable).
(set-logic ALL)
(set-option :produce-proofs true)
(declare-const x8 Int)
(declare-const x Bool)
(declare-fun s (Real) Real)
(assert (> (+ (s 0.0)
              (ite (fp.isNormal
                   (fp.fma RNE
                       (fp (_ bv0 1) (_ bv0 8) (_ bv0 23))
                       ((_ to_fp 8 24) RNE (to_real x8))
                       ((_ to_fp 8 24) RNE 0.5)))
                   x8 1))
           0.0))
(assert (and x (= (str.from_int 0) "0")))
(check-sat)
