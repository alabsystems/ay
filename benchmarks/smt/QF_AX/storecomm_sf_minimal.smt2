; Store commutativity with store-forwarding reads (_sf_ pattern)
; Builds two store chains with different orderings, then reads from both
; and asserts the reads differ. Should be UNSAT.
; Expected: unsat
(set-logic QF_AX)
(set-info :status unsat)
(declare-sort Index 0)
(declare-sort Elem 0)
(declare-fun a () (Array Index Elem))
(declare-fun i1 () Index)
(declare-fun i2 () Index)
(declare-fun v1 () Elem)
(declare-fun v2 () Elem)
(declare-fun k () Index)
(assert (not (= i1 i2)))
; Two orderings of the same stores
(define-fun lhs () (Array Index Elem) (store (store a i1 v1) i2 v2))
(define-fun rhs () (Array Index Elem) (store (store a i2 v2) i1 v1))
; Read at position k from both -- should always be equal
(assert (not (= (select lhs k) (select rhs k))))
(check-sat)
(exit)
