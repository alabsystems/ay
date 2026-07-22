; QF_BV benchmark: puzzle_15
(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 32))
(declare-fun v1 () (_ BitVec 32))
(assert (= (bvadd v1 v0) #xc04a96c4))
(assert (= (bvand v1 v0) #x25b8fd4b))
(assert (= (bvxor v0 v1) #xc4bbb7a9))
(check-sat)
(exit)
