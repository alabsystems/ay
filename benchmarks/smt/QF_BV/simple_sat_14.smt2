; QF_BV benchmark: simple_sat_14
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x00003454))
(assert (bvugt x #x0000002f))
(check-sat)
(exit)
