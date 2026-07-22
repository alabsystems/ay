; QF_BV benchmark: simple_sat_02
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x00007248))
(assert (bvugt x #x00000047))
(check-sat)
(exit)
