; QF_BV benchmark: simple_sat_11
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x0000d860))
(assert (bvugt x #x000000ae))
(check-sat)
(exit)
