; FIXTURE: AY answers unsat and writes NO proof at all (no AY-PROOF block).
; A gap, not a lie: classified `no-proof`, and a hard failure only under
; --require-proof.
; EXPECT-CHECK-VERDICT: no-proof
;
; AY-ANSWER: unsat
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(exit)
