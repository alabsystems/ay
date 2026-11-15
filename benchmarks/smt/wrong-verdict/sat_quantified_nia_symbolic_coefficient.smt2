; D11 (2026-09-23 hunt, quantifiers W1 p1): the infeasible-forall rewrite
; read the binder's coefficient 1 + w with w set to 0 and refuted the
; universal. At w = -1 the body is 0 = 0 for every v: sat (z3 5.1.0).
; AY --z3-mode answered unsat on main f399eca07a.
(set-logic NIA)
(declare-fun w () Int)
(assert (forall ((v Int)) (= (+ v (* v w)) 0)))
(check-sat)
