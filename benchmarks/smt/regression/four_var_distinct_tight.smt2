; Four variables that must all be distinct
; With bounds [1,3] - UNSAT (pigeonhole)
(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)

; Bounds: all in [1,3] - only 3 values available
(assert (>= a 1)) (assert (<= a 3))
(assert (>= b 1)) (assert (<= b 3))
(assert (>= c 1)) (assert (<= c 3))
(assert (>= d 1)) (assert (<= d 3))

; All distinct - impossible with 4 vars in 3 values
(assert (distinct a b c d))

(check-sat)
; Expected: unsat (pigeonhole principle)
