(set-logic QF_ALIA)
; Store 5 at index i, but claim select at i returns 10: UNSAT
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (= (select (store a i 5) i) 10))
(check-sat)
(exit)
