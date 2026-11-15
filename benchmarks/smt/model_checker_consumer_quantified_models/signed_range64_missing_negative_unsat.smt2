; A concrete all-seven model with one bad negative-index override.
; Expected unsat. Checking only the low unsigned portion is insufficient.
(set-logic ALL)
(define-fun a () (Array (_ BitVec 64) (_ BitVec 8))
  (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x07)
         #xffffffffffffffff #x00))
(assert (forall ((i (_ BitVec 64)))
  (=> (and (bvsge i #xfffffffffffffffe) (bvslt i #x0000000000000002))
      (= (select a i) #x07))))
(check-sat)
