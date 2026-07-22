; QF_ABV: 64-bit variable*variable multiplication — hard stress test
; Without delayed internalization: ~128K gates
; With delayed internalization: cheap axioms may suffice
(set-logic QF_ABV)
(declare-fun a () (Array (_ BitVec 8) (_ BitVec 64)))
(declare-fun x () (_ BitVec 64))
(declare-fun y () (_ BitVec 64))

; 64-bit variable * variable — this is the killer for eager blasting
(declare-fun prod () (_ BitVec 64))
(assert (= prod (bvmul x y)))

; Store in array
(assert (= (select (store a #x00 prod) #x00) prod))

; Constrain to small region so SAT is easy with right axioms
(assert (bvugt x #x0000000000000010))
(assert (bvult x #x00000000000000FF))
(assert (bvugt y #x0000000000000010))
(assert (bvult y #x00000000000000FF))
(assert (bvugt prod #x0000000000000100))

(check-sat)
(exit)
