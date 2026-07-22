; QF_BV benchmark: simple_sat_03
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x0000347a))
(assert (bvugt x #x0000002c))
(check-sat)
(exit)
