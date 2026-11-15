; FIXTURE: a proof pinned carcara answers `valid` for, resting on an `evaluate`
; step over `bvsge`. Pinned carcara 1.1.0 computes signed bit-vector operators
; wrongly inside `evaluate` (a negative operand reads as its magnitude), and it
; prints `valid` for the same shape over the SATISFIABLE `(bvsge #xf #xe)`. So
; on any `evaluate` step over such an operator its verdict is not evidence in
; either direction (this instance happens to be true: 0 >= 1 is false), and
; `ay check carcara-guard` -- the scan every Rust gate applies,
; `ay_core::pinned_carcara` -- refuses the pair. A hard failure, never a pass.
; EXPECT-CHECK-VERDICT: misjudged
; EXPECT-CHECK-REASON-CONTAINS: misjudged-evaluate
;
; AY-ANSWER: unsat
; AY-GUARD: refused
; AY-PROOF-BEGIN
;| (assume t0 (bvsge #x0 #x1))
;| (step t1 (cl (= (bvsge #x0 #x1) false)) :rule evaluate)
;| (step t2 (cl (not (= (bvsge #x0 #x1) false)) (not (bvsge #x0 #x1)) false) :rule equiv_pos2)
;| (step t3 (cl (not false)) :rule false)
;| (step t4 (cl) :rule resolution :premises (t2 t1 t0 t3))
; AY-PROOF-END
(set-logic QF_BV)
(set-info :status unsat)
(assert (bvsge #x0 #x1))
(check-sat)
(exit)
