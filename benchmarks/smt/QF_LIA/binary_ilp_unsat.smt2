; Binary 0/1 ILP that is UNSAT
; The LP relaxation is SAT (fractional solution exists)
; but no integer solution exists.
;
; x1 + x2 + x3 = 2
; x1 + x2 + x4 = 2
; x3 + x4 = 1
; x1, x2, x3, x4 in {0,1}
;
; From constraints: x3 + x4 = 1, and substituting into first two:
; x1 + x2 = 2 - x3 and x1 + x2 = 2 - x4
; So x3 = x4, but x3 + x4 = 1 means x3 = x4 = 0.5 (contradiction for integers)
;
; LP relaxation: x1=1, x2=0.5, x3=0.5, x4=0.5 satisfies all.
(set-logic QF_LIA)
(declare-fun x1 () Int)
(declare-fun x2 () Int)
(declare-fun x3 () Int)
(declare-fun x4 () Int)

; Binary domain
(assert (<= 0 x1)) (assert (<= x1 1))
(assert (<= 0 x2)) (assert (<= x2 1))
(assert (<= 0 x3)) (assert (<= x3 1))
(assert (<= 0 x4)) (assert (<= x4 1))

; Constraints
(assert (= (+ x1 x2 x3) 2))
(assert (= (+ x1 x2 x4) 2))
(assert (= (+ x3 x4) 1))

(check-sat)
