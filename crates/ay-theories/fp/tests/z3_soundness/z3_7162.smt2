; Reproducer for Z3 issue #7162 — invalid model on FP fma chain.
; Source: https://github.com/Z3Prover/z3/issues/7162
; Expected: sat (with a model whose fma evaluation is bit-exact).
(set-logic ALL)
(declare-const a0 (_ FloatingPoint 11 53))
(declare-const a1 (_ FloatingPoint 11 53))
(declare-const a3 (_ FloatingPoint 11 53))
(declare-const a4 (_ FloatingPoint 11 53))
(assert (= (fp #b0 #b00000000000 #b0000000000000000000000000000000000000000000000000000)
           (fp.sub RNA a4 (fp.fma RTN a3 a1 a0))))
(check-sat)
