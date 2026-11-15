; Satisfiable; z3 4.12.5 sat with d = 0, c = 0, x = -1, f(e) = 0, (div 0 0) = 5, (div 7 0) = 3.
; AY answered unsat before the fixed-term export required both sides justified.
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const d Int)
(declare-const e Int)
(declare-const c Int)
(assert (= (div d d) 5))
(assert (not (= (* c d) (* x x))))
(assert (= 3 (div 7 (f e))))
(check-sat)
