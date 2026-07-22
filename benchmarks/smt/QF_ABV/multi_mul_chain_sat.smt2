; QF_ABV: chain of 32-bit multiplications — SAT
; Multiple delayed ops that cheap axioms should handle
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 32)))
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(declare-fun z () (_ BitVec 32))

; Three variable-variable multiplications
(assert (= (select (store a #x00 (bvmul x y)) #x00) (bvmul x y)))
(assert (= (select (store a #x01 (bvmul y z)) #x01) (bvmul y z)))
(assert (= (select (store a #x02 (bvmul x z)) #x02) (bvmul x z)))

; Constraints
(assert (= x #x00000003))
(assert (= y #x00000005))
(assert (= z #x00000007))

; Products stored and retrievable
(assert (= (bvmul x y) #x0000000F))
(assert (= (bvmul y z) #x00000023))
(assert (= (bvmul x z) #x00000015))

(check-sat)
(exit)
