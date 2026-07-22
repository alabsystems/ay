; EXTERNAL_CODEGEN-style GPU kernel: two threads writing to non-overlapping addresses
; Tests: parallel store operations with distinct index reasoning
(set-info :status sat)
(set-logic QF_ABV)
(declare-const mem (Array (_ BitVec 64) (_ BitVec 8)))
(declare-const tid (_ BitVec 64))  ; thread ID

; Thread tid writes to address tid*4
(define-fun addr_t0 () (_ BitVec 64) (bvmul tid #x0000000000000004))
(define-fun addr_t1 () (_ BitVec 64) (bvmul (bvadd tid #x0000000000000001) #x0000000000000004))

; Two writes to non-overlapping addresses
(define-fun mem1 () (Array (_ BitVec 64) (_ BitVec 8))
  (store mem addr_t0 #xFF))
(define-fun mem2 () (Array (_ BitVec 64) (_ BitVec 8))
  (store mem1 addr_t1 #xAA))

; Read back thread 0's value - should still be #xFF
(assert (= (select mem2 addr_t0) #xFF))
; Read back thread 1's value - should be #xAA
(assert (= (select mem2 addr_t1) #xAA))
; Threads are different
(assert (not (= tid (bvadd tid #x0000000000000001))))

(check-sat)
(exit)
