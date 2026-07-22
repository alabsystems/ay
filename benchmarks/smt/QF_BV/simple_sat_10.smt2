; QF_BV benchmark: simple_sat_10
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x00000353))
(assert (bvugt x #x00000051))
(check-sat)
(exit)
