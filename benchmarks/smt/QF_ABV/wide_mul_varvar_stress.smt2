; QF_ABV: stress test for delayed internalization — 32-bit variable*variable
; This is the core pattern: both operands are variables, width > 12
; Without delayed internalization: ~32K gates per mul = ~96K total
; With delayed internalization: solved by cheap axioms alone if constant values work
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 16) (_ BitVec 32)))
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(declare-fun z () (_ BitVec 32))
(declare-fun w () (_ BitVec 32))

; x*y = z*w (two variable-variable muls)
(declare-fun prod1 () (_ BitVec 32))
(declare-fun prod2 () (_ BitVec 32))
(assert (= prod1 (bvmul x y)))
(assert (= prod2 (bvmul z w)))
(assert (= prod1 prod2))

; Constrain to non-trivial region
(assert (bvugt x #x00000002))
(assert (bvugt y #x00000002))
(assert (bvugt z #x00000002))
(assert (bvugt w #x00000002))
(assert (bvult x #x000000FF))
(assert (bvult y #x000000FF))
(assert (bvult z #x000000FF))
(assert (bvult w #x000000FF))

; Products must match and be > 100
(assert (bvugt prod1 #x00000064))

; Array interactions
(assert (= (select (store a #x0000 prod1) #x0000) prod1))

(check-sat)
(exit)
