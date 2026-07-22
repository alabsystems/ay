; QF_BV benchmark: simple_sat_00
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x00003900))
(assert (bvugt x #x0000000c))
(check-sat)
(exit)
