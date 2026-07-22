; QF_BV benchmark: unsat_09
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(assert (= x #x6612))
(assert (not (= x #x0a6f)))
(assert (= x #x4e05))
(check-sat)
(exit)
