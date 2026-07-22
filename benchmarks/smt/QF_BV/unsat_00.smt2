; QF_BV benchmark: unsat_00
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(assert (= x #x2afb))
(assert (not (= x #xdb73)))
(assert (= x #x457a))
(check-sat)
(exit)
