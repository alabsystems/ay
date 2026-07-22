; EXTERNAL_CODEGEN-style memory aliasing: proving two pointers access different memory
; Tests: UNSAT from conflicting store/select at same address
(set-info :status unsat)
(set-logic QF_ABV)
(declare-const mem (Array (_ BitVec 64) (_ BitVec 8)))

; Write 0xAA to address 0x100
(define-fun mem1 () (Array (_ BitVec 64) (_ BitVec 8))
  (store mem #x0000000000000100 #xAA))

; Assert reading address 0x100 from mem1 gives a different value
(assert (not (= (select mem1 #x0000000000000100) #xAA)))

(check-sat)
(exit)
