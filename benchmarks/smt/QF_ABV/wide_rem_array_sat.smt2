; QF_ABV: wide remainder with array — SAT
; Exercises delayed internalization for 32-bit urem
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 32)))
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))

; y > 0
(assert (not (= y #x00000000)))

; Store remainder into array
(assert (= (select (store a #x00 (bvurem x y)) #x00) (bvurem x y)))

; Remainder is less than divisor
(assert (bvult (bvurem x y) y))

; Non-trivial values
(assert (bvugt x #x00001000))
(assert (bvugt y #x00000010))

(check-sat)
(exit)
