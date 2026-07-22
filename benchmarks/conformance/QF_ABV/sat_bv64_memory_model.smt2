; EXTERNAL_CODEGEN-style byte-addressed memory model with BV64 indices
; Tests: Array (_ BitVec 64) (_ BitVec 8) with store chains
(set-info :status sat)
(set-logic QF_ABV)
(declare-const mem (Array (_ BitVec 64) (_ BitVec 8)))
(declare-const ptr (_ BitVec 64))

; Store 4 bytes at ptr, ptr+1, ptr+2, ptr+3
(define-fun mem1 () (Array (_ BitVec 64) (_ BitVec 8))
  (store mem ptr #xDE))
(define-fun mem2 () (Array (_ BitVec 64) (_ BitVec 8))
  (store mem1 (bvadd ptr #x0000000000000001) #xAD))
(define-fun mem3 () (Array (_ BitVec 64) (_ BitVec 8))
  (store mem2 (bvadd ptr #x0000000000000002) #xBE))
(define-fun mem4 () (Array (_ BitVec 64) (_ BitVec 8))
  (store mem3 (bvadd ptr #x0000000000000003) #xEF))

; Read back and verify
(assert (= (select mem4 ptr) #xDE))
(assert (= (select mem4 (bvadd ptr #x0000000000000001)) #xAD))
(assert (= (select mem4 (bvadd ptr #x0000000000000002)) #xBE))
(assert (= (select mem4 (bvadd ptr #x0000000000000003)) #xEF))

(check-sat)
(exit)
