; Sat twin of q01_min2_eucdiv.smt2: the definitions inlined. z3 4.12.5 sat.
; AY answered unsat on it too before the fix.
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const d Int)
(declare-const e Int)
(declare-const c Int)
(assert (= (div d d) 5))
(assert (not (= (* c d) (* x x))))
(assert (= 3 (div 7 (f e))))
(check-sat)
