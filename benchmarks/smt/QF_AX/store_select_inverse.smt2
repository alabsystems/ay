; Store-select inverse: store(a, i, select(a, i)) = a (self-store)
; This is a tautology in array theory. Asserting the negation should be unsat.
; Expected: unsat
(set-logic QF_AX)
(declare-sort Index 0)
(declare-sort Element 0)
(declare-fun a () (Array Index Element))
(declare-fun i () Index)
(assert (not (= (store a i (select a i)) a)))
(check-sat)
(exit)
