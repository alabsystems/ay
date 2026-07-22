; QF_BV benchmark: unsat_03
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(assert (= x #x6c5e))
(assert (not (= x #xe8ce)))
(assert (= x #xa758))
(check-sat)
(exit)
