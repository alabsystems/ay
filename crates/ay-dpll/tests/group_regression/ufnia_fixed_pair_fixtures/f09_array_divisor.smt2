; Satisfiable; z3 4.12.5 sat with d = 0, e = 0, x = 2, y = -1, z = -1, A
; constant 0, f(0) = 8, f(8) = 2, (div 0 0) = 5, (div -1 0) = -1. The
; incdiv fuzz case the reductions came from: a divisor read from an array.
; AY answered unsat before the fixed-term export required both sides justified.
(declare-fun f (Int) Int)
(declare-fun gg (Int Int) Int)
(declare-fun pb (Int) Bool)
(declare-const bq Bool)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(declare-const d Int)
(declare-const e Int)
(declare-const A (Array Int Int))
(assert (= (div d d) 5))
(assert (distinct (* (f 0) d) (* x y)))
(assert (>= (* (- x y) (abs 0)) d))
(assert (= (- (* y y) (f (f d))) (div (+ 0 z) (select A (+ (select A x) e)))))
(check-sat)
