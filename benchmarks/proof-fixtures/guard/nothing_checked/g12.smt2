; FIXTURE (guard): every instance answers `unknown`. Each individual outcome is
; legitimate, but the RUN checked zero proofs -- it measured nothing about proof
; emission and must not be reported as a pass.
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
