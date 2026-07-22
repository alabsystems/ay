; Edge case: block all but one point
; 2x2 grid with 3 points blocked, 1 remaining
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)

; Bounds: x in [1,2], y in [1,2]
(assert (>= x 1)) (assert (<= x 2))
(assert (>= y 1)) (assert (<= y 2))

; Block 3 of 4 points, leaving (2,2)
(assert (or (distinct x 1) (distinct y 1)))  ; block (1,1)
(assert (or (distinct x 1) (distinct y 2)))  ; block (1,2)
(assert (or (distinct x 2) (distinct y 1)))  ; block (2,1)

(check-sat)
; Expected: sat - only (2,2) is valid
