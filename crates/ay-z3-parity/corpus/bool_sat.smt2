; expected: sat
; QF_UF pure boolean — a satisfiable propositional formula.
(set-logic QF_UF)
(set-info :status sat)
(declare-const p Bool)
(declare-const q Bool)
(assert (or p q))
(assert (=> p (not q)))
(check-sat)
