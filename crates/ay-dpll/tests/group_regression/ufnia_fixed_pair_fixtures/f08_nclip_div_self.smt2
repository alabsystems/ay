; Satisfiable; z3 4.12.5 sat with d = 0, c = 0, x = -1, nClip(e) = 2,
; (div 0 0) = 5. The divisor is a clip-style UF with a lower bound.
; AY answered unsat before the fixed-term export required both sides justified.
(declare-fun nClip (Int) Int)
(declare-const x Int)
(declare-const d Int)
(declare-const e Int)
(declare-const c Int)
(assert (<= 0 (nClip e)))
(assert (= (div d d) 5))
(assert (not (= (* c d) (* x x))))
(assert (= (div 7 (nClip e)) 3))
(check-sat)
