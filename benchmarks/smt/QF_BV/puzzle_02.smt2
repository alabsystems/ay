; QF_BV benchmark: puzzle_02
(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 8))
(declare-fun v1 () (_ BitVec 8))
(assert (= (bvxor v0 v1) #x20))
(assert (= (bvxor v1 v0) #x80))
(assert (= (bvor v0 v1) #xae))
(check-sat)
(exit)
