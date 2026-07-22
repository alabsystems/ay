; QF_BV benchmark: unsat_06
(set-logic QF_BV)
(declare-fun x () (_ BitVec 16))
(assert (= x #xf0cc))
(assert (not (= x #x09ec)))
(assert (= x #x1aaa))
(check-sat)
(exit)
