; A complete, well-typed but incompatible saved interpretation must refuse.
; An unpinned solve could choose f=0; same-assignment replay cannot.
(set-logic BV)
(set-info :status unsat)
(define-fun f ((x (_ BitVec 2))) (_ BitVec 2) (_ bv1 2))
(assert (forall ((i (_ BitVec 2))) (= (f i) (_ bv0 2))))
(check-sat)
