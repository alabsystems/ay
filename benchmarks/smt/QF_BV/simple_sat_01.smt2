; QF_BV benchmark: simple_sat_01
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x00008cd0))
(assert (bvugt x #x0000007d))
(check-sat)
(exit)
