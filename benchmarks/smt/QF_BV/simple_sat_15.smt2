; QF_BV benchmark: simple_sat_15
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x0000c285))
(assert (bvugt x #x00000031))
(check-sat)
(exit)
