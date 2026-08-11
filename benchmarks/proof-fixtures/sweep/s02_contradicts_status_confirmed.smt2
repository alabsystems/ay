; FIXTURE: a REAL wrong answer. AY says `sat` on a genuinely unsatisfiable
; problem. The header says unsat, and so do z3 and cvc5 -- so adjudication must
; CONFIRM it and the sweep must exit non-zero.
; EXPECT-SWEEP: confirmed-wrong
; EXPECT-SWEEP-FLAGS: CONTRADICTS_STATUS
;
; AY-ANSWER: sat
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(exit)
