; QF_ABV: wide multiplication with array store/select — SAT
; Exercises delayed internalization for 32-bit variable*variable mul
; Z3 delays this, AY should too with #7015
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 32)))
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(declare-fun idx () (_ BitVec 8))

; Store x*y into array at idx
(assert (= (select (store a idx (bvmul x y)) idx) (bvmul x y)))

; Constrain x and y to make mul non-trivial
(assert (bvugt x #x00000010))
(assert (bvugt y #x00000010))
(assert (bvult x #x0000FFFF))
(assert (bvult y #x0000FFFF))

; Product must be within range
(assert (bvugt (bvmul x y) #x00000100))

(check-sat)
(exit)
