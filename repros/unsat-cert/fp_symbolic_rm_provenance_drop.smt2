; Two RoundingMode constants forced equal while their rounding behaviours
; conflict. UNSAT, and ay computes the UNSAT every time.
;
; MEASURED 2026-08-19 at 120192833: publication is refused with
; `AssertionEpochMismatch` — "the UNSAT proof provenance is not bound to the
; authored assertion epoch" — and the answer degrades to
; `(:reason-unknown (incomplete self-check-rejected))`. Same for the sibling
; `rm_symbolic_mode_wrong_pin_unsat` shape.
;
; The refusal is BOOKKEEPING, not proof content. With the provenance-lifecycle
; probes added in this commit, `--probe-cert-reject` shows the record is
; present when the solve starts:
;   install_proof_source_provenance INSTALLED: roots=3
;   begin_public_solve: tracker=true provenance=true authored_roots=3
;   install_proof_source_provenance INSTALLED: roots=3
;   bind_materialized_public_query: had_provenance=true rebound=true provenance=true epoch=true
;   assertion epoch: no proof provenance is installed        <-- gone by mint time
; and NEITHER `invalidate_last_check_result` NOR
; `publish_quantified_verdict_only_unsat` reports clearing it (both probes are
; live in this commit and neither fires), so a third writer drops it. Not yet
; identified; the epoch itself survives, which is why this presents as
; AssertionEpochMismatch and not MissingEpoch.
(declare-const r1 RoundingMode)
(declare-const r2 RoundingMode)
(assert (= r1 r2))
(assert (= (fp.roundToIntegral r1 ((_ to_fp 8 24) RNE 2.5)) ((_ to_fp 8 24) RNE 3.0)))
(assert (= (fp.roundToIntegral r2 ((_ to_fp 8 24) RNE 2.5)) ((_ to_fp 8 24) RNE 2.0)))
(check-sat)
