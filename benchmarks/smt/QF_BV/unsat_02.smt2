; QF_BV benchmark: unsat_02
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(assert (= x #x8533))
(assert (not (= x #xc219)))
(assert (= x #xa79a))
(check-sat)
(exit)
