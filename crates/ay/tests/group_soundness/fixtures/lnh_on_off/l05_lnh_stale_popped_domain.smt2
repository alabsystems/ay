; z3 5.1.0: sat sat
; The LNH domain comes from ANY or-node in the term store, here one asserted only inside a popped scope.
; The live query never mentions (tl l_i), so the swap check passes vacuously, and the lex-leader
; then constrains l0/l1 of the live query. Second check-sat: SAT (l0 has a cons tail, l1 a nil tail).
(set-logic QF_DT)
(declare-datatypes ((E 0) (L 0)) (((A) (B) (C)) ((cons (hd E) (tl L)) (nil))))
(declare-const x L)
(declare-const l0 L) (declare-const l1 L) (declare-const l2 L) (declare-const l3 L) (declare-const l4 L) (declare-const l5 L)
(push 1)
(assert (not (or (= x (tl l0)) (= x (tl l1)) (= x (tl l2)) (= x (tl l3)) (= x (tl l4)) (= x (tl l5)))))
(check-sat)
(pop 1)
(assert (or (= l0 (cons A (cons B nil))) (= l0 (cons B (cons B nil)))))
(assert (or (= l1 (cons A nil)) (= l1 (cons B nil))))
(assert (or ((_ is cons) x) ((_ is nil) x)))
(check-sat)
