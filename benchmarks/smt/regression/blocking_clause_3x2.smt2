; Blocking clause pattern from #294 - 3x2 variant
; 3x2 grid with blocking clauses - should be SAT
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)

; Bounds: x in [1,3], y in [1,2]
(assert (>= x 1)) (assert (<= x 3))
(assert (>= y 1)) (assert (<= y 2))

; Block some points
(assert (or (distinct x 1) (distinct y 1)))  ; block (1,1)
(assert (or (distinct x 2) (distinct y 2)))  ; block (2,2)
(assert (or (distinct x 3) (distinct y 2)))  ; block (3,2)

(check-sat)
; Expected: sat - (1,2), (2,1), (3,1) are valid
