; Blocking clause pattern - 3x3 grid
; Block 6 of 9 points, leaving 3 solutions
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)

; Bounds: x in [1,3], y in [1,3]
(assert (>= x 1)) (assert (<= x 3))
(assert (>= y 1)) (assert (<= y 3))

; Block 6 points: (1,1), (1,2), (2,1), (2,2), (3,2), (3,3)
(assert (or (distinct x 1) (distinct y 1)))
(assert (or (distinct x 1) (distinct y 2)))
(assert (or (distinct x 2) (distinct y 1)))
(assert (or (distinct x 2) (distinct y 2)))
(assert (or (distinct x 3) (distinct y 2)))
(assert (or (distinct x 3) (distinct y 3)))

(check-sat)
; Expected: sat - (1,3), (2,3), (3,1) are valid
