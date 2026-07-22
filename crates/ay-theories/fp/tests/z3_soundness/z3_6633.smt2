; Reproducer for Z3 issue #6633 — fpToReal returns unknown on trivial FP constraint.
; Source: https://github.com/Z3Prover/z3/issues/6633
; Expected: sat. Original Z3 returned unknown.
(set-logic ALL)
(declare-const x (_ FloatingPoint 8 24))
(declare-const y Real)
(assert (= y (fp.to_real x)))
(assert (= y 99.2))
(check-sat)
