; Diophantine 2x2 system with no unit coefficients.
;
; SAT witness: x = 2, y = 3  (2*2 + 3*3 = 13, 4*2 + 5*3 = 23). Z3 answers `sat`.
;
; The diophantine solver introduces fresh elimination variables for non-unit
; coefficients. Their determined values used to leak into the Solved result map
; (indices >= the original-variable boundary), tripping a debug_assert in
; dioph_bridge ("Solved value has out-of-range var index") and panicking debug
; builds; in release the bridge's range guard dropped them. The panic emitted NO
; verdict, so on the no-proof-check subprocess backend the VC silently degraded to
; Unknown -- a common, simple integer shape (two linear equations) that could
; never be proved. ay must answer `sat`, never panic or `unsat`.
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= (+ (* 2 x) (* 3 y)) 13))
(assert (= (+ (* 4 x) (* 5 y)) 23))
(check-sat)
