; Store commutativity with store-forwarding and 3 indices
; After reordering stores, check that reads from BOTH arrays at ALL positions match
; Expected: unsat
(set-logic QF_AX)
(set-info :status unsat)
(declare-sort Index 0)
(declare-sort Elem 0)
(declare-fun a () (Array Index Elem))
(declare-fun i1 () Index)
(declare-fun i2 () Index)
(declare-fun i3 () Index)
(declare-fun v1 () Elem)
(declare-fun v2 () Elem)
(declare-fun v3 () Elem)
(declare-fun k () Index)
; All indices distinct
(assert (not (= i1 i2)))
(assert (not (= i1 i3)))
(assert (not (= i2 i3)))
; Two orderings: 1-2-3 vs 3-2-1
(define-fun lhs () (Array Index Elem) (store (store (store a i1 v1) i2 v2) i3 v3))
(define-fun rhs () (Array Index Elem) (store (store (store a i3 v3) i2 v2) i1 v1))
; Select from both at arbitrary position k -- must be equal
(assert (not (= (select lhs k) (select rhs k))))
(check-sat)
(exit)
