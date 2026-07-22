; Store commutativity: store(store(a,i,v),j,w) = store(store(a,j,w),i,v) when i != j
; This is UNSAT because the two sides are equivalent by ROW1/ROW2
; Expected: unsat
(set-logic QF_AX)
(set-info :status unsat)
(declare-sort Index 0)
(declare-sort Elem 0)
(declare-fun a () (Array Index Elem))
(declare-fun i () Index)
(declare-fun j () Index)
(declare-fun v () Elem)
(declare-fun w () Elem)
(assert (not (= i j)))
; store(store(a, i, v), j, w) != store(store(a, j, w), i, v) should be UNSAT
(assert (not (= (store (store a i v) j w) (store (store a j w) i v))))
(check-sat)
(exit)
