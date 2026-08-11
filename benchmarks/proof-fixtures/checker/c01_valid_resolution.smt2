; FIXTURE: a proof carcara fully checks.
; EXPECT-CHECK-VERDICT: valid
;
; AY-ANSWER: unsat
; AY-PROOF-BEGIN
;| (assume h1 p)
;| (assume h2 (not p))
;| (step t3 (cl) :rule resolution :premises (h1 h2) :args (p true))
; AY-PROOF-END
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(exit)
