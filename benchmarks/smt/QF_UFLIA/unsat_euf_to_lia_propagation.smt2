; Test UNSAT: EUF→LIA propagation
; Issue #316: EUF equality (f 5) = -1 must propagate to LIA
; so that 0 <= (f 5) becomes 0 <= -1 → contradiction
;
; This test requires Nelson-Oppen in the EUF→LIA direction.
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(assert (= (f 5) (- 1)))
(assert (<= 0 (f 5)))
(check-sat)
; Expected: unsat
