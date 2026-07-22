; UFLRA logic acceptance test
; Tests that AY accepts (set-logic UFLRA) as a valid SMT-LIB logic
(set-logic UFLRA)
(declare-const x Real)
(assert (< x 0))
(assert (> x 0))
(check-sat)
(exit)
