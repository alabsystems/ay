; z3 5.1.0: sat
; Same LNH defect without datatypes: domain {(f a0) .. (f a4)} of compound UF terms.
; SAT: e = (f a1) = d1, a0 = b, (f b) = c, c /= e.
(set-logic QF_UF)
(set-info :status sat)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const e U) (declare-const c U) (declare-const b U) (declare-const b2 U)
(declare-const a0 U) (declare-const a1 U) (declare-const a2 U) (declare-const a3 U) (declare-const a4 U)
(assert (or (= e (f a0)) (= e (f a1)) (= e (f a2)) (= e (f a3)) (= e (f a4))))
(assert (or (= a0 b) (= a0 b2)))
(assert (= (f b) c))
(assert (= (f b2) c))
(assert (not (= e c)))
(check-sat)
