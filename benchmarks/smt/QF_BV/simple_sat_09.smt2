; QF_BV benchmark: simple_sat_09
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x0000e5fe))
(assert (bvugt x #x0000008e))
(check-sat)
(exit)
