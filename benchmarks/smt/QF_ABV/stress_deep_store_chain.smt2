; QF_ABV: deep store chain with 32 writes, symbolic indices
; Exercises the expand_select_store ITE budget and array axiom fixpoint
(set-logic QF_ABV)
(declare-fun mem () (Array (_ BitVec 16) (_ BitVec 8)))
(declare-fun base () (_ BitVec 16))
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))

; 32-deep store chain at base+offset
(define-fun m1 () (Array (_ BitVec 16) (_ BitVec 8))
  (store (store (store (store (store (store (store (store mem
    (bvadd base #x0000) x)
    (bvadd base #x0001) (bvadd x #x01))
    (bvadd base #x0002) (bvadd x #x02))
    (bvadd base #x0003) (bvadd x #x03))
    (bvadd base #x0004) (bvadd x #x04))
    (bvadd base #x0005) (bvadd x #x05))
    (bvadd base #x0006) (bvadd x #x06))
    (bvadd base #x0007) (bvadd x #x07)))

(define-fun m2 () (Array (_ BitVec 16) (_ BitVec 8))
  (store (store (store (store (store (store (store (store m1
    (bvadd base #x0008) y)
    (bvadd base #x0009) (bvadd y #x01))
    (bvadd base #x000a) (bvadd y #x02))
    (bvadd base #x000b) (bvadd y #x03))
    (bvadd base #x000c) (bvadd y #x04))
    (bvadd base #x000d) (bvadd y #x05))
    (bvadd base #x000e) (bvadd y #x06))
    (bvadd base #x000f) (bvadd y #x07)))

; Read-back constraints
(assert (= (select m2 (bvadd base #x0000)) x))
(assert (= (select m2 (bvadd base #x0004)) (bvadd x #x04)))
(assert (= (select m2 (bvadd base #x0008)) y))
(assert (= (select m2 (bvadd base #x000c)) (bvadd y #x04)))

; Cross-read: unchanged location
(assert (= (select m2 (bvadd base #x0010))
           (select mem (bvadd base #x0010))))

; Constrain x and y
(assert (bvugt x #x10))
(assert (bvult y #xf0))

(check-sat)
(exit)
