; QF_BV benchmark: unsat_07
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(assert (= x #xb32e))
(assert (not (= x #x72cd)))
(assert (= x #x2321))
(check-sat)
(exit)
