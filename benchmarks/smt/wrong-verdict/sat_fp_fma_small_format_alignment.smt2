; D13 (2026-09-24 fp-strings fix-up, fresh hunt file g6_00041). The exact
; reference (the hunt's fpref.py) and z3 5.1.0: sat. main 6818b5d067: unsat
; in both postures. fp.fma in (2,3): the alignment cap 2*sb + 3 = 9 did not fit
; the eb + 2 = 4 signed exponent bits (it read as -7), so the addend was never
; aligned. x0 = -2.0: -2 * 0.75 + 3 = 1.5 exactly.
(set-logic ALL)
(declare-const x0 (_ FloatingPoint 2 3))
(assert (= (fp.fma RTN x0 (fp #b0 #b00 #b11) (fp #b0 #b10 #b10)) (fp #b0 #b01 #b10)))
(check-sat)
