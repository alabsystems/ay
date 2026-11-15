; LNH least-index over a domain of compound LIST terms (tl l0) .. (tl l4).
; LNH adds x = (tl l0); l0's tail is a cons, x is asserted nil. SAT: l1 = (cons A nil), x = nil.
(set-logic QF_DT)
(set-info :status sat)
(declare-datatypes ((E 0) (L 0)) (((A) (B) (C)) ((cons (hd E) (tl L)) (nil))))
(declare-const x L)
(declare-const l0 L) (declare-const l1 L) (declare-const l2 L) (declare-const l3 L) (declare-const l4 L)
(assert (or (= x (tl l0)) (= x (tl l1)) (= x (tl l2)) (= x (tl l3)) (= x (tl l4))))
(assert (or (= l0 (cons A (cons B nil))) (= l0 (cons B (cons C nil)))))
(assert ((_ is nil) x))
(check-sat)
