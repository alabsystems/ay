; FIXTURE: an HONEST proof -- structure checks, one step is an explicit `hole`.
; Must never be reported as `valid`; must never be reported as `invalid`.
; EXPECT-CHECK-VERDICT: holey
;
; AY-ANSWER: unsat
; AY-PROOF-BEGIN
;| (assume h1 p)
;| (assume h2 (not p))
;| (step t3 (cl) :rule hole :premises (h1 h2))
; AY-PROOF-END
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(exit)
