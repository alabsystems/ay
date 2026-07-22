; QF_BV benchmark: simple_sat_18
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x0000eb39))
(assert (bvugt x #x0000003f))
(check-sat)
(exit)
