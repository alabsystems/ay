; Constant-folding coverage for the integer `rem` operator (#8730).
; Uses Z3 semantics: rem takes the sign of the divisor.
;   (rem  7  3) =  1
;   (rem -7  3) =  2
;   (rem  7 -3) = -1
;   (rem -7 -3) = -2
; Expected: sat (all equalities hold).
(set-logic QF_LIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(assert (= a (rem 7 3)))
(assert (= b (rem (- 7) 3)))
(assert (= c (rem 7 (- 3))))
(assert (= d (rem (- 7) (- 3))))
(assert (= a 1))
(assert (= b 2))
(assert (= c (- 1)))
(assert (= d (- 2)))
(check-sat)
