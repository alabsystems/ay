; Unsat twin: f07_div_three_d_0002.smt2 with one product changed so that the
; forced d = 0 makes both sides of the disequality 0. AY must refute it.
(declare-fun f (Int) Int)
(declare-fun g (Int Int) Int)
(declare-const x Int)
(declare-const y Int)
(declare-const d Int)
(declare-const e Int)
(declare-const c Int)
(declare-const z Int)
(assert (= (div (* 3 d) d) 0))
(assert (distinct (* (f 0) d) (* c d)))
(assert (distinct 3 (div (f 0) (f x))))
(check-sat)
