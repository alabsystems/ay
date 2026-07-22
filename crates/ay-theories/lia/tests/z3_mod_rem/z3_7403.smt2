; Reproducer for Z3 issue #7403 — non-termination with mod0/div0 + quantifiers.
; Source: https://github.com/Z3Prover/z3/issues/7403
; This reproducer depends on quantifier support; tracked under AY #8340.
; Without full quantifier reasoning, ay is expected to return `unknown`.
; Quantifier-free core retained for when quant support lands.
(set-logic LIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (= (f x) (mod x 0))))
(assert (distinct (f 1) (f 2)))
(check-sat)
