; FIXTURE (guard): AY emits NOTHING -- no verdict line at all. This is the
; signature of a broken work cell (the 2026 dangling-symlink incident: every
; instance "answered" in 0s, nothing was checked, and the sweep printed PASS).
; A whole directory of these must make the harness FAIL, not pass.
; EXPECT-CHECK-VERDICT: no-answer
;
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(exit)
