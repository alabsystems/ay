; FIXTURE: the OTHER half of defect #2. A proof that carcara accepts while still
; emitting a [WARN]. The obvious over-correction for c05 -- "treat any stderr
; output as a failure reason" -- would break this one, reporting a reason (or a
; failure) for a proof that is `valid`. Warnings are recorded, never promoted.
; EXPECT-CHECK-VERDICT: valid
; EXPECT-CHECK-REASON-IS-EMPTY: 1
; EXPECT-CHECK-WARN-CONTAINS: appears after
;
; AY-ANSWER: unsat
; AY-PROOF-BEGIN
;| (assume h1 p)
;| (step t2 (cl p) :rule reordering :premises (h1))
;| (assume h3 (not p))
;| (step t4 (cl) :rule resolution :premises (t2 h3) :args (p true))
; AY-PROOF-END
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(exit)
