; QF_BV benchmark: simple_sat_19
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x0000c1cf))
(assert (bvugt x #x00000028))
(check-sat)
(exit)
