; Store commutativity with 3 indices (more complex extensionality needed)
; store(store(store(a,i1,v1),i2,v2),i3,v3) = store(store(store(a,i3,v3),i2,v2),i1,v1)
; when i1, i2, i3 are all distinct
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
; All indices distinct
(assert (not (= i1 i2)))
(assert (not (= i1 i3)))
(assert (not (= i2 i3)))
; Two orderings: 1-2-3 vs 3-2-1
(define-fun lhs () (Array Index Elem) (store (store (store a i1 v1) i2 v2) i3 v3))
(define-fun rhs () (Array Index Elem) (store (store (store a i3 v3) i2 v2) i1 v1))
; They should be equal
(assert (not (= lhs rhs)))
(check-sat)
(exit)
