; D1 (2026-09-23 hunt, strings-dt-fp w13): wrong SAT carrying confirmed-sat.
; |U| <= 2 by the universal, so W = w(U) | w2 has at most 3 values and four
; distinct W values are impossible: unsat (z3 5.1.0). AY answered sat in both
; postures on main f399eca07a, with the model a0 = w(@U!3) holding a U element
; the finite-universe certificate never enumerated.
(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((W 0) (L 0) (P 0)) (
 ((w (g U)) (w2))
 ((nil) (cons (hd U) (tl L)))
 ((p (p1 U) (p2 U)))))
(declare-const u0 U)
(declare-const u1 U)
(declare-const a0 W)
(declare-const a1 W)
(declare-const a2 W)
(declare-const a3 W)
(assert (distinct a0 a1 a2 a3))
(assert (forall ((x U)) (or (= x u0) (= x u1))))
(check-sat)
