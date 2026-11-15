; Satisfiable; z3 4.12.5 sat with d = 0, x = 2, e = -1, f(0) = 2, g(e, y) = 3.
; AY answered unsat before the fixed-term export required both sides justified.
(declare-fun f (Int) Int)
(declare-fun g (Int Int) Int)
(declare-const x Int)
(declare-const y Int)
(declare-const d Int)
(declare-const e Int)
(assert (<= d 0))
(assert (>= d 0))
(assert (distinct (* x d) (* x e)))
(assert (<= 2 (mod (f 0) (g e y))))
(check-sat)
