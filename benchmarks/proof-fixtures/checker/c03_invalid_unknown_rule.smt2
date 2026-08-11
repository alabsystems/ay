; FIXTURE: an INVENTED rule name. This is the original 2026-07-30 defect
; (`:rule dt_distinct` -- no such Alethe rule). Not a proof; a hard failure.
; EXPECT-CHECK-VERDICT: invalid
; EXPECT-CHECK-REASON-CONTAINS: unknown rule
;
; AY-ANSWER: unsat
; AY-PROOF-BEGIN
;| (assume h1 p)
;| (assume h2 (not p))
;| (step t3 (cl) :rule dt_distinct :premises (h1 h2))
; AY-PROOF-END
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(exit)
