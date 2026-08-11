; FIXTURE: an artifact carcara cannot PARSE at all -- the S2 class, reproduced
; exactly (a `declare-fun` leaking into the proof document):
;   [ERROR] parser error: unexpected token: 'declare-fun' (on line 0, column 1)
; A parse error must still be classified `invalid`, not `checker-error`.
; EXPECT-CHECK-VERDICT: invalid
; EXPECT-CHECK-REASON-CONTAINS: parser error
;
; AY-ANSWER: unsat
; AY-PROOF-BEGIN
;| (declare-fun sk!?V_8_2_6 () Int)
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
