; The only satisfying element in signed [-2, 2) is at canonical BV64 -1.
; Expected sat. The model must preserve the high unsigned bit-pattern.
(set-logic ALL)
(define-fun a () (Array (_ BitVec 64) (_ BitVec 8))
  (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) #x00)
         #xffffffffffffffff #x07))
(assert (exists ((i (_ BitVec 64)))
  (and (bvsge i #xfffffffffffffffe) (bvslt i #x0000000000000002)
       (= (select a i) #x07))))
(check-sat)
