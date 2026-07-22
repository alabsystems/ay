; Companion to z3_7842.smt2 — explicit (set-logic QF_FP) variant.
; Pins the DT+FP soundness contract (#8728) against regressions in the
; *explicit* logic-selection path: ALL-auto is handled in logic_detect.rs,
; but `with_datatypes()` + `Other` dispatch must also hold for explicit
; QF_FP + (declare-datatype). Expected: must not be `sat`.
(set-logic QF_FP)
(declare-datatype Expr ((Flt (getFlt_1 (_ FloatingPoint 8 24)))))
(declare-fun x () Expr)
(assert (distinct x (Flt (_ NaN 8 24))))
(assert (fp.isNaN (getFlt_1 x)))
(check-sat)
