; int_incompleteness2.smt2
; Leonardo de Moura's classic LIA completeness test
; If 3 divides x1 and 6 divides x2, then 3 divides (x1 + x2)
; Formulated as: x1 = 3*k1, x2 = 6*k2, x1+x2 = 3*k3+r, r in {1,2}
; Since x1+x2 = 3*k1 + 6*k2 = 3*(k1+2*k2), this is always divisible by 3
; so r != 0 is unsatisfiable.
; Expected: unsat
(set-logic QF_LIA)
(declare-const x1 Int)
(declare-const x2 Int)
(declare-const k1 Int)
(declare-const k2 Int)
(declare-const k3 Int)
(declare-const r Int)
(assert (= x1 (* 3 k1)))
(assert (= x2 (* 6 k2)))
(assert (= (+ x1 x2) (+ (* 3 k3) r)))
(assert (>= r 1))
(assert (<= r 2))
(check-sat)
(exit)
