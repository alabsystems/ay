; FIXTURE: AY agrees with the header and reports no doubt. Must not be flagged.
; EXPECT-SWEEP: clean
;
; AY-ANSWER: unsat
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(exit)
