(set-logic QF_BV)
(declare-const x (_ BitVec 5))
(assert (not (= (bvsdiv x (_ bv1 5)) x)))
(check-sat)
