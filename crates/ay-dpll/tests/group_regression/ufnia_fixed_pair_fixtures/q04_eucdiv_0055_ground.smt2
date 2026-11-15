; Sat twin of q04_eucdiv_0055.smt2: the definitions inlined. z3 4.12.5 sat.
; AY answered unsat on it too before the fix.
(declare-fun f (Int) Int)
(declare-fun g (Int Int) Int)
(declare-const x Int)
(declare-const y Int)
(declare-const d Int)
(declare-const e Int)
(declare-const c Int)
(declare-const z Int)
(assert (= (mod d d) 7))
(assert (distinct (* c d) (* c x)))
(assert (<= 2 (div (f 0) (f (+ e 1)))))
(check-sat)
