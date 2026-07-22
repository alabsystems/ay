; Reproducer for Z3 issue #7464 — infinite loop on mod with variable divisor.
; Source: https://github.com/Z3Prover/z3/issues/7464
; Minimized core: `nn mod m = 0` with a non-zero divisor constraint.
; Expected: sat (e.g., nn = 0, m = 1). Original Z3 hung on the full Liquid
; Haskell-generated input.
(set-logic QF_LIA)
(declare-const nn Int)
(declare-const m Int)
(assert (> m 0))
(assert (= (mod nn m) 0))
(check-sat)
