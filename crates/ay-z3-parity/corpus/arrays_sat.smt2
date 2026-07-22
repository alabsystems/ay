; expected: sat
; QF_AX — array store/select that is satisfiable.
(set-logic QF_AX)
(set-info :status sat)
(declare-sort Index 0)
(declare-sort Elem 0)
(declare-const a (Array Index Elem))
(declare-const i Index)
(declare-const v Elem)
(assert (= (select (store a i v) i) v))
(check-sat)
