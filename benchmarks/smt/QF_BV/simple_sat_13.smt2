; QF_BV benchmark: simple_sat_13
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x00006e3d))
(assert (bvugt x #x000000ac))
(check-sat)
(exit)
