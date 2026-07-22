; QF_ABV: wide multiplication with zero — UNSAT
; Cheap axiom: mul_zero should catch: if product != 0 but one operand = 0
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 32)))
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))

; x = 0
(assert (= x #x00000000))

; Store x*y into array, read back must be > 0
(assert (bvugt (select (store a #x00 (bvmul x y)) #x00) #x00000000))

; This is UNSAT: 0*y = 0, but we require result > 0
(check-sat)
(exit)
