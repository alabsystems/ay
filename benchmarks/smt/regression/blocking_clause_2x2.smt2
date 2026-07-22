; Blocking clause pattern from #294
; 2x2 grid with blocking clauses - should be SAT
; Pattern: bounded integers with disjunctions of disequalities
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)

; Bounds
(assert (>= x 1)) (assert (<= x 2))
(assert (>= y 1)) (assert (<= y 2))

; Block (1,1) and (2,2) - leaves (1,2) and (2,1) as solutions
(assert (or (distinct x 1) (distinct y 1)))  ; block (1,1)
(assert (or (distinct x 2) (distinct y 2)))  ; block (2,2)

(check-sat)
; Expected: sat
