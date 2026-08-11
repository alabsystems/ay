; FIXTURE: THE REGRESSION TEST FOR HARNESS DEFECT #2.
;
; carcara writes to stderr, in this order:
;   [WARN] `assume` command 'h3' appears after `step` commands
;   [ERROR] checking failed on step 't2' with rule 'and_neg': ...
;
; check_proofs.sh recorded `grep -m1 . "$err"` -- the FIRST stderr line -- so the
; WARN was reported as the reason and the real ERROR was thrown away. Two real
; instances were consequently filed under an "assume-after-step" defect class
; that DOES NOT EXIST; both were really `and_pos`. The harness was not wrong
; about the verdict, it was wrong about WHY, which is worse: it invented a bug
; class and sent work after it.
;
; The reason must name the RULE THAT FAILED. The warning must survive, but in a
; separate field.
; EXPECT-CHECK-VERDICT: invalid
; EXPECT-CHECK-REASON-CONTAINS: and_neg
; EXPECT-CHECK-REASON-EXCLUDES: appears after
; EXPECT-CHECK-WARN-CONTAINS: appears after
;
; AY-ANSWER: unsat
; AY-PROOF-BEGIN
;| (assume h1 p)
;| (step t2 (cl (and p p)) :rule and_neg :premises (h1))
;| (assume h3 (not p))
;| (step t4 (cl) :rule resolution :premises (h1 h3) :args (p true))
; AY-PROOF-END
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(exit)
