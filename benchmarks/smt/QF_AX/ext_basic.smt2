; Extensionality: if a != b then exists i such that select(a, i) != select(b, i)
; This is SAT: a and b can differ
; Expected: sat
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun b () (Array Index Element))
(assert (not (= a b)))
(check-sat)
(exit)
