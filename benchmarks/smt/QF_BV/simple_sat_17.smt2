; QF_BV benchmark: simple_sat_17
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x0000876f))
(assert (bvugt x #x00000016))
(check-sat)
(exit)
