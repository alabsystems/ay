; QF_BV benchmark: unsat_01
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(assert (= x #xec63))
(assert (not (= x #x5d0b)))
(assert (= x #x19be))
(check-sat)
(exit)
