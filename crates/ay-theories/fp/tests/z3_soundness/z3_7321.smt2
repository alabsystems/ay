; Reproducer for Z3 issue #7321 — FP-to-Real transitivity failure.
; Source: https://github.com/Z3Prover/z3/issues/7321
; Expected: unsat. Original Z3 reported sat with an invalid model.
(set-logic ALL)
(declare-fun s0 () (_ FloatingPoint 4 4))
(define-fun s1 () (_ FloatingPoint 4 4) (fp #b0 #b0000 #b001))
(define-fun s2 () Bool (fp.eq s0 s1))
(define-fun s8 () Real (fp.to_real s0))
(define-fun s10 () Real (/ 1.0 512.0))
(define-fun s11 () Bool (= s8 s10))
(define-fun s13 () Bool (and s2 (not s11)))
(assert s13)
(check-sat)
