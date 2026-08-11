; FIXTURE: the header is WRONG and AY is right. The problem is plainly
; satisfiable; the `:status unsat` line is a lie (older benchmark families carry
; these, and this campaign has already been misled once by trusting a single
; source). AY says sat, so the header check flags it -- but z3 and cvc5 both say
; sat, agreeing WITH AY, so adjudication must return `unconfirmed` and this must
; NOT count towards the wrong-answer total.
;
; Without this fixture the cross-check could be deleted entirely and the suite
; would still pass.
; EXPECT-SWEEP: flagged-unconfirmed
; EXPECT-SWEEP-FLAGS: CONTRADICTS_STATUS
;
; AY-ANSWER: sat
(set-logic QF_UF)
(set-info :status unsat)
(declare-const q Bool)
(assert (or q (not q)))
(check-sat)
(exit)
