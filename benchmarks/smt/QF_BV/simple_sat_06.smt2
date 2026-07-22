; QF_BV benchmark: simple_sat_06
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x00006ff1))
(assert (bvugt x #x00000077))
(check-sat)
(exit)
