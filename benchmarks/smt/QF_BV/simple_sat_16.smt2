; QF_BV benchmark: simple_sat_16
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x0000b7cc))
(assert (bvugt x #x000000b0))
(check-sat)
(exit)
