; Unsat twin: f10_div_self_free_dividend.smt2 with one product changed so that
; the forced d = 0 makes both sides of the disequality 0. AY must refute it.
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const z Int)
(declare-const d Int)
(declare-const e Int)
(declare-const c Int)
(assert (= (div d d) 5))
(assert (not (= (* c d) (* x d))))
(assert (= 3 (div z (f e))))
(check-sat)
