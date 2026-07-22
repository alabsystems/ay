; expected: unsat
; QF_AX — read-over-write axiom violated, so unsatisfiable.
(set-logic QF_AX)
(set-info :status unsat)
(declare-sort Index 0)
(declare-sort Elem 0)
(declare-const a (Array Index Elem))
(declare-const i Index)
(declare-const v Elem)
(assert (not (= (select (store a i v) i) v)))
(check-sat)
