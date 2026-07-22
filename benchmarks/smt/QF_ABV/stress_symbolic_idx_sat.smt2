; QF_ABV stress test: many symbolic-index selects on store chain
; Mimics software verification byte-level memory patterns
; 16 stores with symbolic indices, 8 selects at various offsets
(set-logic QF_ABV)
(declare-fun mem () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun p0 () (_ BitVec 32))
(declare-fun p1 () (_ BitVec 32))
(declare-fun p2 () (_ BitVec 32))
(declare-fun p3 () (_ BitVec 32))

; Build a store chain with 16 writes at symbolic offsets
(define-fun mem1 () (Array (_ BitVec 32) (_ BitVec 8))
  (store (store (store (store mem
    (bvadd p0 #x00000000) #x41)
    (bvadd p0 #x00000001) #x42)
    (bvadd p0 #x00000002) #x43)
    (bvadd p0 #x00000003) #x44))

(define-fun mem2 () (Array (_ BitVec 32) (_ BitVec 8))
  (store (store (store (store mem1
    (bvadd p1 #x00000000) #x51)
    (bvadd p1 #x00000001) #x52)
    (bvadd p1 #x00000002) #x53)
    (bvadd p1 #x00000003) #x54))

(define-fun mem3 () (Array (_ BitVec 32) (_ BitVec 8))
  (store (store (store (store mem2
    (bvadd p2 #x00000000) #x61)
    (bvadd p2 #x00000001) #x62)
    (bvadd p2 #x00000002) #x63)
    (bvadd p2 #x00000003) #x64))

(define-fun mem4 () (Array (_ BitVec 32) (_ BitVec 8))
  (store (store (store (store mem3
    (bvadd p3 #x00000000) #x71)
    (bvadd p3 #x00000001) #x72)
    (bvadd p3 #x00000002) #x73)
    (bvadd p3 #x00000003) #x74))

; Pointers don't alias
(assert (bvugt (bvsub p1 p0) #x00000010))
(assert (bvugt (bvsub p2 p1) #x00000010))
(assert (bvugt (bvsub p3 p2) #x00000010))

; Read back some values
(assert (= (select mem4 (bvadd p0 #x00000000)) #x41))
(assert (= (select mem4 (bvadd p1 #x00000002)) #x53))
(assert (= (select mem4 (bvadd p2 #x00000001)) #x62))
(assert (= (select mem4 (bvadd p3 #x00000003)) #x74))

; Verify some unchanged locations
(assert (= (select mem4 (bvadd p0 #x00000010))
           (select mem (bvadd p0 #x00000010))))

(check-sat)
(exit)
