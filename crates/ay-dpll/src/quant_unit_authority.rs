// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Runtime switches for the P3a/P3b exact-proof derivation-authority channels
//! (#quant-unit-authority).
//!
//! Two independent controls:
//!
//! * [`quant_unit_authority_enabled`] — the kill switch. `--no-quant-unit-authority`
//!   (or `0`) disables EVERY channel this campaign added:
//!   - the producer-side vacuous-quantifier collapse certification
//!     (`ProofTracker::add_vacuous_quantifier_collapse` call site in
//!     `simplify_vacuous_quantifiers`, which then falls back to the baseline
//!     conservative `quantified_proof_translation_incomplete` marker),
//!   - `SkolemInstanceRecord` provenance recording in
//!     `skolemize_existentials` AND at the finite-expansion route's
//!     recording site in `expand_finite_domains`
//!     (#finite-exists-skolem-provenance),
//!   - the Boolean-ITE guard-clause trust-leaf rebuild
//!     (`promote_shannon_ite_guard_trust_leaves`,
//!     #ite-guard-promotion),
//!   - (P3b) `BvMbqiFalseInstanceRecord` provenance recording at the
//!     `try_bv_mbqi_refinement` push site
//!     (#bv-mbqi-false-instance-authority),
//!   - the sealed derivation maps in `sealed_fragment_derivation_maps`
//!     (starving the c4/c5 fragment channels — including the P3b
//!     eval-folded-`false` bridge records — of input),
//!   - the c2 (`and`-conjunct closure), c3/c3b (closed tautology / ground
//!     comparison), c4 (`forall_inst` chain, with the P3b
//!     eval-folded-`false` bridge), c5 (Skolemization chain), and (P3b) c6
//!     (`or`-with-false-disjuncts fold chain) arms of
//!     `build_exact_original_proof_fragment_metered`, which then keeps only
//!     the pre-campaign c1 authored-unit check,
//!   - (P3b) the quantifier-loop artifact firewall's consult of a
//!     current-query checked SAT-refutation sidecar in
//!     `quantified_semantic_unsat_or_unknown`, which then downgrades exactly
//!     as at baseline,
//!   - (L1 #ppp-provenance) `PropagateValues` producer provenance minting
//!     (`extend_propagated_value_provenance`) and the proof-rebuild-lane
//!     replay (`derive_propagated_value_assumptions`),
//!   - (L2 #ppp-c7) `QpfPremiseForcedInstanceRecord` recording plus the
//!     refutation-driven re-solve at the `premise_forced_binder_refutation`
//!     success site (`qpf_premise_forced_refutation_resolve` records
//!     nothing, pushes nothing, and re-solves nothing when off),
//!   - (L2) the sealed propagation environment and qpf instance-root maps
//!     (`sealed_propagation_environment`,
//!     `sealed_instance_root_derivations` — both empty when off, starving
//!     the c7 arm), and the c7 propagated-unit-chain arm of
//!     `build_exact_original_proof_fragment_metered` itself (inside the same
//!     per-build `unit_authority` flag as c2-c6),
//!   - (#bitblast-original-clause-authority) the trace-free qpf
//!     instance-refutation consult in `quantified_semantic_unsat_or_unknown`
//!     (`checked_qpf_instance_refutation_authorizes_current_query`, guarded
//!     at the call site AND internally): with the switch off no
//!     `QpfPremiseForcedInstanceRecord` is recorded upstream and the consult
//!     itself declines, restoring the baseline downgrade byte-for-byte,
//!   - (L3 #ppp-l3) the AUFLIA `FlattenAnd`+`PropagateValues` fixpoint
//!     drain (`extend_propagated_value_provenance_direct` — nothing stored
//!     when off) and the licensing-source augmentation of
//!     propagation/int-const-rewritten assertion provenance in
//!     `solve_harness` (`augment_propagation_rewritten_sources` and the
//!     `substitute_int_constants_preserving_definitions` planner), which
//!     when off invalidate rewritten slots to `None` exactly as the pre-L3
//!     baseline did,
//!   - (#skolem-witness-sat) the skolem-witness SAT confirmation channel
//!     (`SkolemWitnessRecord` recording in `skolemize_existentials` plus the
//!     restore-time confirmation arms in `try_skolem_witness_sat_confirmation`;
//!     see [`skolem_witness_sat_enabled`], which also has its own dedicated
//!     `--no-skolem-witness-sat` switch).
//!
//!   The checker-side `sko_ex` arm in `ay-proof` is NOT env-gated: with every
//!   producer channel off, no `sko_ex`-shaped step is ever emitted, and the
//!   arm itself is strictly stronger than the pre-existing `sko_forall`
//!   validation (all existing checks PLUS a registered-`SkolemChoice`
//!   identity requirement), so it admits nothing a producer did not
//!   explicitly register.
//!
//! * [`vacuous_marker_narrowing_enabled`] — the staged narrowing of the
//!   `quantified_proof_translation_incomplete` marker, DEFAULT OFF
//!   (#sat-grants-are-staged). `--vacuous-marker-narrow` stops setting
//!   the conservative marker for a vacuous collapse the tracker certified.
//!   The landing audit (see
//!   the development design notes) found the
//!   marker's single read site downgrades an UNSAT verdict to
//!   `Unknown(QuantifierUnhandled)`, and phases 2.4/2.5 of result mapping can
//!   later upgrade exactly such an Unknown to a certified SAT — so the marker
//!   value transitively selects between an UNSAT and a SAT publication and
//!   the narrowing may not ship as a default flip. With the stage off the
//!   marker is set in byte-for-byte the same situations as baseline; a
//!   certified collapse instead discharges the marker through the
//!   pre-existing strict-proof gate in result mapping (the sanctioned path:
//!   "only the strict checker may discharge the marker").
//!
//! Both switches are read per call site: every use is at most once per
//! (re)solve on a cold path, and per-call reads keep in-process tests able to
//! toggle the environment without `OnceLock` staleness.

/// Kill switch for every P3a derivation-authority channel (default ON;
/// `--no-quant-unit-authority` restores pre-campaign behaviour).
pub(crate) fn quant_unit_authority_enabled() -> bool {
    !ay_core::misc_cli_flags().no_quant_unit_authority
}

/// Kill switch for the authored consequence-replay UNSAT translation
/// (#consequence-replay): the producer that re-solves the authored ground
/// conjuncts plus the recorded `forall_inst` instances on a same-context
/// probe and stitches the probe's strict proof onto authored-scope
/// derivations. Default ON; `--no-consequence-replay` (or `0`) disables
/// both the trust-rejected cascade member and the CEGQI certification
/// translation leg, restoring the baseline fail-closed `unknown`s
/// byte-for-byte. UNSAT-only: this switch never gates a SAT grant.
pub(crate) fn consequence_replay_enabled() -> bool {
    !ay_core::misc_cli_flags().no_consequence_replay
}

/// Kill switch for QUANTIFIED-query trace arming under competition proof
/// shedding (#quantified-trace-arming). Default ON — on a public query whose
/// authored problem contains a quantifier, `--rigor fast` records the internal
/// proof trace instead of shedding it.
///
/// WHY THIS IS NOT AN ARTIFACT PREFERENCE. On a quantified problem the
/// recorded trace is not a user-facing artifact, it is the mechanism that
/// publishes an instantiation-driven refutation: E-matching / CEGQI writers
/// register their exact ground instances as `forall_inst` derivations, and
/// `disambiguate_cegqi_unsat` (result_mapping.rs) publishes `unsat` precisely
/// when those recorded derivations strict-check against the immutable authored
/// problem. Shedding the tracker deletes the evidence, so the SAME refutation
/// that publishes at `--rigor standard` degrades to `unknown` at `--rigor
/// fast`. Measured on a 40-instance SQ Equality_LinearArith sample: `fast`
/// solved 1, `standard` solved 6, with the five lost rows all independently
/// confirmed `unsat` by z3 and cvc5 — the weaker rigor level publishing
/// strictly less, which is a non-monotone ladder and a pure loss on the
/// competition posture.
///
/// WHERE IT FIRES. On the `Unknown` FALLBACK only
/// (`Executor::quantified_trace_arming_unknown_retry`), never at the
/// public-solve boundary. Two measured reasons:
///
///  * Routing publication through the certified funnel — the first attempt,
///    which made the quantified case defeat `competition_shedding_active()`
///    outright — lost
///    `UFDTLIA/20241211-verus/anvil/splinterdb-smt-exec__MiniAllocator_v.1`:
///    a 0.3s raw `unsat` became a 60s `unknown` in the trust-rejected proof
///    cascade.
///  * Arming the recorder for the whole solve — the second attempt — is not
///    verdict-neutral either: `produce_proofs_enabled()` flips true, which
///    changes proof-preserving preprocessing and the classification arms that
///    consult it. Over a 231-instance sweep spanning every non-incremental
///    quantified logic it gained 9 rows and LOST 6 the shed path answers
///    today, three of them in well under a second.
///
/// On the fallback there is by construction no verdict to lose: the first pass
/// is byte-identical to the shed baseline, the B3 `CompetitionRaw` admission
/// lane is untouched, and the retry can only replace `unknown` with a verdict
/// that cleared every mandatory gate.
///
/// Setting `--no-quantified-shedding-yield` restores the pre-change behaviour
/// byte-for-byte so the barrier can be mutation-tested.
pub(crate) fn quantified_shedding_yield_enabled() -> bool {
    !ay_core::misc_cli_flags().no_quantified_shedding_yield
}

/// Kill switch for the negated-existential ground-instantiation artifact
/// firewall translation (#inc-fparith-negated-exists-inst): the producer that
/// instantiates the De Morgan dual of an authored `(not (exists ...))` root at
/// ground terms drawn from the problem, hands the resulting ground consequence
/// set to the consequence-replay stitcher, and installs the stitched strict
/// proof as `last_proof`.
///
/// Default ON. `--no-negated-exists-ground-inst` (or the parent
/// `--no-consequence-replay`, which starves the stitcher itself) restores the
/// baseline fail-closed `unknown` byte-for-byte. UNSAT-only: consulted at
/// exactly one place — the artifact firewall's downgrade — so its only
/// reachable transition is `unknown -> unsat`, and the verdict it lets through
/// is still adjudicated by the unchanged mandatory certification mint.
pub(crate) fn negated_exists_ground_inst_enabled() -> bool {
    consequence_replay_enabled() && !ay_core::misc_cli_flags().no_negated_exists_ground_inst
}

/// Kill switch for the ground-conflict decomposition arms of the proof
/// builder (#ground-conflict-decomp): the general EUF-chain + Farkas-bridge
/// split of a fused ground Generic conflict, and the array read-over-write
/// chain-under-equality split (both in `split_euf_congruence_lemmas`'s
/// trust-lemma cascade). Default ON; `--no-ground-conflict-decomp` disables
/// both arms, leaving each Generic lemma byte-identical for the unchanged
/// fail-closed strict gate. UNSAT-only producer surgery: neither arm can
/// produce or influence a SAT grant, and every emitted step is re-validated
/// by the untouched strict checker.
pub(crate) fn ground_conflict_decomp_enabled() -> bool {
    !ay_core::misc_cli_flags().no_ground_conflict_decomp
}

/// Staged `quantified_proof_translation_incomplete` narrowing, DEFAULT OFF.
/// Requires the kill switch on AND `--vacuous-marker-narrow`.
pub(crate) fn vacuous_marker_narrowing_enabled() -> bool {
    quant_unit_authority_enabled() && ay_core::misc_cli_flags().vacuous_marker_narrow
}

/// Kill switch for the skolem-witness SAT confirmation arm
/// (#skolem-witness-sat) — the documented SAT-side sibling of the
/// `--no-quant-unit-authority` channel list. Default ON;
/// `--no-skolem-witness-sat` (or the parent `--no-quant-unit-authority`
/// switch) disables BOTH the `skolem_witness_records` provenance recording in
/// `skolemize_existentials` AND the consuming confirmation arm in
/// `restore_assertions` (`try_skolem_witness_sat_confirmation`), restoring
/// the baseline fail-closed
/// `unknown (incomplete quantifier-ematching-exists)` byte-for-byte.
///
/// This channel is a SAT grant ENABLER, not a SAT publisher: it can only stop
/// the restore-time producer demote after re-evaluating every public query
/// root — with the independent gate's own evaluator, under the already-emitted
/// model — through the polarity-sound witnessed rewrite. The verdict it lets
/// through is still adjudicated by the unchanged, unconditional emission
/// gates (`apply_quantified_model_failclosed_gate` and
/// `apply_independent_model_gate`), which know nothing about this channel.
pub(crate) fn skolem_witness_sat_enabled() -> bool {
    quant_unit_authority_enabled() && !ay_core::misc_cli_flags().no_skolem_witness_sat
}
