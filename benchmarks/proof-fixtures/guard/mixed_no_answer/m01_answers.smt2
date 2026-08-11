; FIXTURE (guard): the one healthy instance in a mostly-dead directory. It gives
; the run a non-zero "proofs checked" count, so guard 1 stays quiet and guard 2
; (the no-answer RATE) is tested on its own.
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
