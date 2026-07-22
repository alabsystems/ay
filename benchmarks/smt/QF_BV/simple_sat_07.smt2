; QF_BV benchmark: simple_sat_07
(set-logic QF_BV)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert (= (bvadd x y) #x00000d96))
(assert (bvugt x #x00000065))
(check-sat)
(exit)
