; LNH least-index symmetry breaking over a domain of COMPOUND terms (top l_i).
; Swapping the TERMS (top l0)<->(top li) leaves the assertion set invariant, but no model
; symmetry swaps their values: l0 is pinned to top A by a constraint that does not mention (top l0).
; SAT: e = B, l0 = (cons A nil), l1 = (cons B nil).
(set-logic QF_DT)
(set-info :status sat)
(declare-datatypes ((E 0) (L 0)) (((A) (B) (C) (D) (E5) (F)) ((cons (hd E) (tl L)) (nil))))
(declare-const e E)
(declare-const l0 L) (declare-const l1 L) (declare-const l2 L) (declare-const l3 L) (declare-const l4 L)
(assert (or (= e (hd l0)) (= e (hd l1)) (= e (hd l2)) (= e (hd l3)) (= e (hd l4))))
(assert (or (= l0 (cons A nil)) (= l0 (cons A (cons A nil)))))
(assert (not (= e A)))
(check-sat)
