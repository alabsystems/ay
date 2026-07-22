; QF_BV benchmark: puzzle_05
(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 32))
(declare-fun v1 () (_ BitVec 32))
(assert (= (bvand v0 v1) #x5496f63c))
(assert (= (bvxor v0 v1) #x7900f7f9))
(assert (= (bvand v1 v0) #x1825bc54))
(check-sat)
(exit)
