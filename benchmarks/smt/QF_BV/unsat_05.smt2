; QF_BV benchmark: unsat_05
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(assert (= x #xd7d7))
(assert (not (= x #x8129)))
(assert (= x #x29ef))
(check-sat)
(exit)
