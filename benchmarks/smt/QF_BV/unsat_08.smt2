; QF_BV benchmark: unsat_08
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(assert (= x #x149c))
(assert (not (= x #x0fe3)))
(assert (= x #x7e9b))
(check-sat)
(exit)
