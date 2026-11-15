; Satisfiable; z3 4.12.5 sat with d = 0, c = 0, x = -1, z = -1, f(e) = 0,
; (div 0 0) = 5, (div -1 0) = 3. The tests also run it under each logic line
; the review tried (ALL, QF_AUFLIA, QF_UFLIA, QF_UFNIA): all answered unsat.
; AY answered unsat before the fixed-term export required both sides justified.
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const z Int)
(declare-const d Int)
(declare-const e Int)
(declare-const c Int)
(assert (= (div d d) 5))
(assert (not (= (* c d) (* x x))))
(assert (= 3 (div z (f e))))
(check-sat)
