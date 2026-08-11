; FIXTURE: AY prints `unknown`. A legitimate non-answer -- no proof is expected,
; nothing is checked, and it must NOT be confused with `no-answer` (the signature
; of a broken work cell, which the guard treats as a measurement failure).
; EXPECT-CHECK-VERDICT: unknown
;
; AY-ANSWER: unknown
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(exit)
