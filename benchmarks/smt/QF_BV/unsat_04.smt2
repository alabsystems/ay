; QF_BV benchmark: unsat_04
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(assert (= x #xaccc))
(assert (not (= x #xc21c)))
(assert (= x #x8e77))
(check-sat)
(exit)
