; Unsat twin: f08_nclip_div_self.smt2 with one product changed so that the
; forced d = 0 makes both sides of the disequality 0. AY must refute it.
(declare-fun nClip (Int) Int)
(declare-const x Int)
(declare-const d Int)
(declare-const e Int)
(declare-const c Int)
(assert (<= 0 (nClip e)))
(assert (= (div d d) 5))
(assert (not (= (* c d) (* x d))))
(assert (= (div 7 (nClip e)) 3))
(check-sat)
