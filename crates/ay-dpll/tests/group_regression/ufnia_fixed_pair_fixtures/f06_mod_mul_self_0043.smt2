; Satisfiable; z3 4.12.5 sat with d = 0, c = -2, e = 1, g(e, y) = 0, f(0) = -1, (mod 0 0) = 5, (mod -1 0) = 1.
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
(assert (distinct (* e d) (* c e)))
(assert (distinct 3 (mod (f 0) (g e y))))
(check-sat)
