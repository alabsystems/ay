; THE SHAPE THAT IS 230 OF THE 252 (#inc-fparith-last-mile).
;
; `(not (exists ((d Float32)) ...))` is a positive-polarity FP universal. The
; elaborator rewrites it to a literal FP `forall`, which sets
; `has_unsafe_partial_quantifiers` and fails the query closed BEFORE the two
; `result_mapping` rescue sites — `--debug-cert` printed no `FMQ` line at all.
; The last-chance consult in `finite_model_mbqi.rs` now reaches the lane on
; this shape; on THIS file it still (correctly) declines, because the lane is a
; SAT lane and the answer is `unsat`:
;
;   FMQ last-chance: consulting the finite-sort certificate
;   FMQ round 0: pins=1 total=true model=true
;   FMQ round 0: all determined; confirm=false      <- residual AND pins is UNSAT
;
; Ground truth: UNSAT. Y is +0, and d = +zero satisfies the body
; (0 <= +0 <= 16 and fp.sub RNE 0.0 +0 = +0 = Y), so the negated existential is
; false. bitwuzla 0.9.1 answers `unsat`; AY answers `unknown`.
;
; This is the residual the next build has to take: an UNSAT-only, instance-based
; refutation resting on `forall x. P(x) |= P(t)` alone. The witness term `+zero`
; occurs LITERALLY in the body; E-matching produces zero instances because the
; body carries no trigger.
;
; ORACLE TRAP, live here: z3 rejects `(set-logic BVFPLRA)`, then the
; `FloatingPoint` sort, then `RNE` — and then prints `sat` anyway, the opposite
; of the truth. Force `(set-logic ALL)` before believing z3 on this file.
(set-logic BVFPLRA)
(declare-fun c_main_~Y~6 () (_ FloatingPoint 8 24))
(assert (= ((_ to_fp 8 24) RNE (_ bv0 32)) c_main_~Y~6))
(assert (not (exists ((main_~D~6 (_ FloatingPoint 8 24)))
  (and (fp.geq main_~D~6 (_ +zero 8 24))
       (fp.leq main_~D~6 ((_ to_fp 8 24) RNE 16.0))
       (= (fp.sub RNE ((_ to_fp 8 24) RNE (_ bv0 32)) main_~D~6) c_main_~Y~6)))))
(check-sat)
