; QF_ABV: mixed mul/div/rem on 32-bit — tests all delayed op types
; This exercises the full delayed internalization pipeline
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 32)))
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))

; y != 0
(assert (not (= y #x00000000)))

; Three delayed operations
(declare-fun m () (_ BitVec 32))
(declare-fun d () (_ BitVec 32))
(declare-fun r () (_ BitVec 32))
(assert (= m (bvmul x y)))
(assert (= d (bvudiv x y)))
(assert (= r (bvurem x y)))

; Fundamental identity: x = d*y + r
(assert (= x (bvadd (bvmul d y) r)))

; Store all in array
(assert (= (select (store a #x00 m) #x00) m))
(assert (= (select (store a #x01 d) #x01) d))
(assert (= (select (store a #x02 r) #x02) r))

; Non-trivial values
(assert (bvugt x #x00001000))
(assert (bvugt y #x00000010))
(assert (bvult y x))

(check-sat)
(exit)
