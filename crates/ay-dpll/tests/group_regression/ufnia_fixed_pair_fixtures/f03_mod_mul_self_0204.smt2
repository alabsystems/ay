; Satisfiable; z3 4.12.5 sat with d = 0, c = 0, x = -1, g(e, y) = 0, (mod 0 0) = 5, (mod 7 0) = 4.
; AY answered unsat before the fixed-term export required both sides justified.
(declare-fun f (Int) Int)
(declare-fun g (Int Int) Int)
(declare-const x Int)
(declare-const y Int)
(declare-const d Int)
(declare-const e Int)
(declare-const c Int)
(declare-const z Int)
(assert (= (mod (* c d) d) 5))
(assert (distinct (* (f 0) d) (* x x)))
(assert (= 4 (mod 7 (g e y))))
(check-sat)
