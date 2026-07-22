; expected: sat
; QF_UF — uninterpreted function, consistent constraints.
(set-logic QF_UF)
(set-info :status sat)
(declare-sort U 0)
(declare-fun f (U) U)
(declare-const a U)
(declare-const b U)
(assert (= (f a) b))
(assert (= a b))
(check-sat)
