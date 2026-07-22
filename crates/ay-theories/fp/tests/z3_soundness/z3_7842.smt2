; Reproducer for Z3 issue #7842 — NaN distinctness violated with datatype wrapper.
; Source: https://github.com/Z3Prover/z3/issues/7842
; Expected: unsat. Original Z3 reported sat with model x = Flt(NaN).
(set-logic ALL)
(declare-datatype Expr ((Flt (getFlt_1 (_ FloatingPoint 8 24)))))
(declare-fun x () Expr)
(assert (distinct x (Flt (_ NaN 8 24))))
(assert (fp.isNaN (getFlt_1 x)))
(check-sat)
