; QF_BV benchmark: simple_sat_04
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x0000d806))
(assert (bvugt x #x00000010))
(check-sat)
(exit)
