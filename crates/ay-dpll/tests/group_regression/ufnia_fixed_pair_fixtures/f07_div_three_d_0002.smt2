; Satisfiable; z3 4.12.5 sat with d = 0, c = 1, y = 1, x = 2, f(0) = -1,
; f(2) = 0, (div 0 0) = 0, (div -1 0) = 0. (div (* 3 d) d) = 0 forces d = 0.
; AY answered unsat before the fixed-term export required both sides justified.
(declare-fun f (Int) Int)
(declare-fun g (Int Int) Int)
(declare-const x Int)
(declare-const y Int)
(declare-const d Int)
(declare-const e Int)
(declare-const c Int)
(declare-const z Int)
(assert (= (div (* 3 d) d) 0))
(assert (distinct (* (f 0) d) (* c y)))
(assert (distinct 3 (div (f 0) (f x))))
(check-sat)
