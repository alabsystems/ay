; FIXTURE: THE REGRESSION TEST FOR HARNESS DEFECT #3.
;
; AY prints a DEFINITE answer while also admitting it did not decide. The
; admission -- `(:reason-unknown ...)` -- goes to STDERR. soundness_sweep.py
; scanned only stdout, so DEFINITE_BUT_UNDECIDED could physically only fire via
; rc == 124; on the corpus of the day every such instance happened to also carry
; rc 124, so nothing was missed and the hole stayed invisible. This fixture
; carries the stderr signal and rc 0, so it fires ONLY through the stderr scan.
;
; The answer here matches the header, so adjudication must come back
; `unconfirmed` -- flagged is not the same as wrong.
; EXPECT-SWEEP: flagged-unconfirmed
; EXPECT-SWEEP-FLAGS: DEFINITE_BUT_UNDECIDED
;
; AY-ANSWER: unsat
; AY-STDERR: (:reason-unknown "incomplete quantifier instantiation")
; AY-RC: 0
(set-logic QF_UF)
(set-info :status unsat)
(declare-const p Bool)
(assert p)
(assert (not p))
(check-sat)
(exit)
