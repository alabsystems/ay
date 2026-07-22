; QF_NIA benchmark: sign consistency test
; Tests that sign lemmas work correctly
; x > 0, y > 0 implies x*y > 0
; With constraint x*y < 0 this should be UNSAT
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (> x 0))
(assert (> y 0))
(assert (< (* x y) 0))
(check-sat)
(exit)
