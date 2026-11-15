; Complete saved function interpretation satisfies the original forall.
(set-logic BV)
(set-info :status sat)
(define-fun f ((x (_ BitVec 2))) (_ BitVec 2) (_ bv0 2))
(assert (forall ((i (_ BitVec 2))) (= (f i) (_ bv0 2))))
(check-sat)
