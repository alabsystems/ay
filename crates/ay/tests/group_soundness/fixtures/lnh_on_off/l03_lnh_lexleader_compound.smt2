; z3 5.1.0: sat
; LNH lex-leader (n = 6, list testers as unary predicates) over a domain of compound list terms (tl l_i).
; The totality-shaped or is not top-level, so least-index adds nothing and the lex-leader fires:
; it forces is-cons(tl l0) => is-cons(tl l1), but l0 has a cons tail and l1 a nil tail.
; SAT: l0 = (cons A (cons B nil)), l1 = (cons A nil).
(set-logic QF_DT)
(set-info :status sat)
(declare-datatypes ((E 0) (L 0)) (((A) (B) (C)) ((cons (hd E) (tl L)) (nil))))
(declare-const x L) (declare-const c Bool)
(declare-const l0 L) (declare-const l1 L) (declare-const l2 L) (declare-const l3 L) (declare-const l4 L) (declare-const l5 L)
(assert (= c (or (= x (tl l0)) (= x (tl l1)) (= x (tl l2)) (= x (tl l3)) (= x (tl l4)) (= x (tl l5)))))
(assert (or (= l0 (cons A (cons B nil))) (= l0 (cons B (cons B nil)))))
(assert (or (= l1 (cons A nil)) (= l1 (cons B nil))))
(assert (or ((_ is cons) x) ((_ is nil) x)))
(check-sat)
