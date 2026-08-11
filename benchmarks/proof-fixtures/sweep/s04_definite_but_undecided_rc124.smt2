; FIXTURE: the other arm of DEFINITE_BUT_UNDECIDED -- a definite answer paired
; with the timeout exit code. Fires through the rc branch, with a clean stderr.
; EXPECT-SWEEP: flagged-unconfirmed
; EXPECT-SWEEP-FLAGS: DEFINITE_BUT_UNDECIDED
;
; AY-ANSWER: unsat
; AY-RC: 124
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(exit)
