; Unsat twin: f01_min3_bounds.smt2 with one product changed so that the forced
; d = 0 makes both sides of the disequality 0. z3 4.12.5 unsat; AY must refute it.
(declare-fun f (Int) Int)
(declare-fun g (Int Int) Int)
(declare-const x Int)
(declare-const y Int)
(declare-const d Int)
(declare-const e Int)
(assert (<= d 0))
(assert (>= d 0))
(assert (distinct (* x d) (* d e)))
(assert (<= 2 (mod (f 0) (g e y))))
(check-sat)
