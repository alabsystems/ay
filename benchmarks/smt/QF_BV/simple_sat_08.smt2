; QF_BV benchmark: simple_sat_08
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x0000d6cb))
(assert (bvugt x #x00000070))
(check-sat)
(exit)
