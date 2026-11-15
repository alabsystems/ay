; D1 (2026-09-23 hunt, strings-dt-fp w08): the recursive-datatype face.
; |U| = 1 by the universal, so two one-element lists cons(hd, nil) are equal:
; unsat (z3 5.1.0). AY answered sat in both postures on main f399eca07a.
(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((L 0)) (((nil) (cons (hd U) (tl L)))))
(declare-const a L)
(declare-const b L)
(declare-const u U)
(assert (distinct a b))
(assert ((_ is cons) a))
(assert ((_ is cons) b))
(assert (= (tl a) nil))
(assert (= (tl b) nil))
(assert (forall ((x U)) (= x u)))
(check-sat)
