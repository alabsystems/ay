; expected: unsat
; QF_UF pure boolean — a propositional contradiction.
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
