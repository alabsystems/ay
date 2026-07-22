; expected: sat
; EPR (effectively propositional) — a universally quantified predicate that
; holds everywhere is consistent with an instance, so this is satisfiable.
(set-logic UF)
(set-info :status sat)
(declare-sort U 0)
(declare-fun p (U) Bool)
(declare-const a U)
(assert (forall ((x U)) (p x)))
(assert (p a))
(check-sat)
