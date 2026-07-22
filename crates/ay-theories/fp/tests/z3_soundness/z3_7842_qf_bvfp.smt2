; Companion to z3_7842.smt2 — explicit (set-logic QF_BVFP) variant.
; Pins the DT+FP soundness contract (#8728) for the BV+FP case: explicit
; QF_BVFP + (declare-datatype) must not drop the FP theory and return a
; spurious `sat` on the NaN-distinctness reproducer.
(set-logic QF_BVFP)
(declare-datatype Expr ((Flt (getFlt_1 (_ FloatingPoint 8 24)))))
(declare-fun x () Expr)
(assert (distinct x (Flt (_ NaN 8 24))))
(assert (fp.isNaN (getFlt_1 x)))
(check-sat)
