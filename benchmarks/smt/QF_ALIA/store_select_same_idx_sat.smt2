(set-logic QF_ALIA)
; Store and select at the same index: SAT
(declare-const a (Array Int Int))
(declare-const i Int)
(assert (> (select a i) 0))
(assert (> i 0))
(check-sat)
(exit)
