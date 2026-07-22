; Three variables that must all be distinct
; With tight bounds - SAT
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)

; Bounds: all in [1,3]
(assert (>= x 1)) (assert (<= x 3))
(assert (>= y 1)) (assert (<= y 3))
(assert (>= z 1)) (assert (<= z 3))

; All distinct
(assert (distinct x y z))

(check-sat)
; Expected: sat - {1,2,3} is a solution
