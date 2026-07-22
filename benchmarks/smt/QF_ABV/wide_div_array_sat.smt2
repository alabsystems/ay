; QF_ABV: wide unsigned division with array — SAT
; Exercises delayed internalization for 32-bit udiv
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 32)))
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))

; Store x/y into array
(assert (= (select (store a #x01 (bvudiv x y)) #x01) (bvudiv x y)))

; y != 0
(assert (not (= y #x00000000)))

; x > y (so quotient >= 1)
(assert (bvugt x y))
(assert (bvugt x #x00010000))
(assert (bvugt y #x00000100))

; Quotient constraint
(assert (bvult (bvudiv x y) #x00001000))

(check-sat)
(exit)
