; NIA bounded-enumeration false-UNSAT (false-PROVE) regression.
;
; SAT witness: x = -4, y = -10  ->  x*y = 40 >= 6, y in [-10, 3], x <= 10,
; x^3 = -64 < 0. Z3 answers `sat`.
;
; The NIA bounded-enumeration lower-bound inference used to manufacture a
; lower bound on x ( x >= ceil(6 / upper(y)) = ceil(6/3) = 2 ) whenever every
; OTHER factor merely had a positive UPPER bound -- without checking the other
; factor could be negative. y in [-10, 3] has positive upper bound 3 but can be
; negative, so x*y >= 6 is also met deep in the negative-product cone (neg*neg).
; Clamping x >= 2 excised that cone, the enumerated box became empty, and ay
; returned a spurious `unsat`. On the no-proof-check subprocess backend that
; UNSAT becomes a development verifier false proof. ay must answer `sat` or `unknown`, never
; `unsat`.
(set-logic QF_NIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (>= (* x y) 6))
(assert (>= y (- 10)))
(assert (<= y 3))
(assert (<= x 10))
(assert (< (* x (* x x)) 0))
(check-sat)
