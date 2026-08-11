; FIXTURE: AY contradicts the declared :status -- says `sat` on an instance the
; header (and z3, and cvc5) call unsat. This is the accident that turned a proof
; harness into a soundness harness on 2026-08-01. It must be a HARD failure and
; must never be silently bucketed with "unknown/timeout, no proof expected".
; EXPECT-CHECK-VERDICT: WRONG-ANSWER
;
; AY-ANSWER: sat
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(exit)
