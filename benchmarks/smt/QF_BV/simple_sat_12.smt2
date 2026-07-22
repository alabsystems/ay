; QF_BV benchmark: simple_sat_12
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x00008e45))
(assert (bvugt x #x0000004f))
(check-sat)
(exit)
