; Unsat twin: f03_mod_mul_self_0204.smt2 with one product changed so that the forced
; d = 0 makes both sides of the disequality 0. z3 4.12.5 unsat; AY must refute it.
(declare-fun f (Int) Int)
(declare-fun g (Int Int) Int)
(declare-const x Int)
(declare-const y Int)
(declare-const d Int)
(declare-const e Int)
(declare-const c Int)
(declare-const z Int)
(assert (= (mod (* c d) d) 5))
(assert (distinct (* (f 0) d) (* x d)))
(assert (= 4 (mod 7 (g e y))))
(check-sat)
