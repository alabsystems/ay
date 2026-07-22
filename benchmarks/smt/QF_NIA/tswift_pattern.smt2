; QF_NIA benchmark: tSwift-style pattern
; Simulates width * height verification
; width > 0, height > 0, area = width * height, area <= 100
; Expected: SAT
(set-logic QF_NIA)
(declare-fun width () Int)
(declare-fun height () Int)
(declare-fun area () Int)
(assert (> width 0))
(assert (> height 0))
(assert (= area (* width height)))
(assert (<= area 100))
(assert (>= area 1))
(check-sat)
(exit)
