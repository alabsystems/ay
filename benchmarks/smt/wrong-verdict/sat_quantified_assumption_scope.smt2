; D10(b) (2026-09-23 hunt, quantifiers W2 m3): a check-sat-assuming literal
; over a quantified problem stayed asserted for later queries. Both queries
; are sat (z3 5.1.0: P false everywhere, g1 free). AY --z3-mode answered
; sat, unsat on main f399eca07a.
(set-logic UF)
(declare-sort U 0)
(declare-fun P (U) Bool)
(declare-fun g1 () Bool)
(assert (forall ((x U)) (not (P x))))
(check-sat-assuming (g1))
(check-sat-assuming ((not g1)))
