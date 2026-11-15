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

/// Kill switch for the authored fold-identity refutation
/// (#authored-fold-identity): the derivation recorded for a preprocessor
/// fold-to-`false` whose argument is visible on the authored conjunction —
/// two operands of a disequality that are one term after arithmetic
/// normalization, or a conjunct and its negation. Default ON;
/// `--no-authored-fold-identity` restores the bare-hole erasure
/// byte-for-byte. UNSAT-only: the pass can only replace a proof the erasure
/// was about to reduce to `(step t0 (cl) :rule hole)`, never grant a verdict.
pub(crate) fn authored_fold_identity_enabled() -> bool {
    !ay_core::misc_cli_flags().no_authored_fold_identity
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

/// Kill switch for the nested-CEGQI quantified-LRA lane (#qlra-nested-cegqi).
///
/// Default ON. The lane is a PROBE, not a pre-empt: it runs before the legacy
/// quantifier path, publishes only through the existing strict routes
/// (authored consequence replay for UNSAT, the quantified model gate for SAT),
/// and on any decline hands the query back unchanged. `--no-qlra-cegqi`
/// removes the probe entirely.
pub(crate) fn qlra_cegqi_enabled() -> bool {
    !ay_core::misc_cli_flags().no_qlra_cegqi
}

/// Kill switch for the SAT-only equality-QE quantifier lane (#eq-qe-lane).
///
/// Default ON. The lane is a PROBE, not a pre-empt: it answers only `sat`,
/// and only after the quantified model gate confirmed every authored
/// quantified conjunct against the lane's model; on any other outcome it
/// hands the query back (the lane's module docs list what a decline leaves
/// behind). `--no-eq-qe-lane` removes the probe.
pub(crate) fn eq_qe_lane_enabled() -> bool {
    !ay_core::misc_cli_flags().no_eq_qe_lane
}

/// Kill switch for the lane's NESTED search (#qlra-nested-cegqi), default ON:
/// problems the depth-1 builder declines run the Fig. 8 recursion. A nested
/// `unsat` publishes only through the M3a expansion certificate (strict
/// boundary), a `sat` only through the quantified model gate (M3b
/// expansion route). `--no-qlra-nested` removes it. Needs the lane on.
pub(crate) fn qlra_nested_enabled() -> bool {
    qlra_cegqi_enabled() && !ay_core::misc_cli_flags().no_qlra_nested
}

/// Kill switch for the authored BOOLEAN-SKELETON refutation
/// (#authored-skeleton-refutation): the producer that refutes the authored
/// roots by unit propagation over their `and`/`not_and`/`or` decomposition,
/// treating every quantifier as an opaque Boolean atom, and installs the
/// resulting `and_pos`/`not_and`/`or`/`resolution` derivation as `last_proof`.
///
/// Default ON. `--no-authored-skeleton-refutation` (or the parent
/// `--no-consequence-replay`, which starves the shared installation boundary)
/// restores the baseline fail-closed `unknown` byte-for-byte. UNSAT-only:
/// consulted at the quantified artifact firewall's downgrade and after an
/// ordinary UNSAT proof is rejected. Its only accepting transition is
/// `unknown -> unsat`, adjudicated by the unchanged mandatory certification mint.
pub(crate) fn authored_skeleton_refutation_enabled() -> bool {
    consequence_replay_enabled() && !ay_core::misc_cli_flags().no_authored_skeleton_refutation
}

/// Kill switch for the consequence-replay LIFTED-ASSERTION trust-leaf
/// promoter (#probe-ite-lift-promoter).
///
/// Ground preprocessing Shannon-expands every term-level arithmetic `ite`
/// before the SAT layer sees an assertion, so the proof tracker assumes the
/// LIFTED term — no probe assertion and no `and`-conjunct of one — and export
/// demotes it to a premiseless `trust` unit the probe's strict check refuses.
/// Measured on AUFDTLIRA `P630-039 bug.ads_32_25_range_check` (the
/// `ground_core` leg's 6-formula core, default posture): the only residual
/// trust step is the lift of `(not (in_range (length b)))`, and every
/// same-context consequence-replay probe over that core declined because of
/// it.
///
/// The promoter recognizes the leaf by re-running the lifter on each probe
/// assertion and derives the unit through checker-validated steps only
/// (`ite_intro` branch equalities, EUF congruence transfers, Farkas-verified
/// constant evaluations, Tseitin tautologies, propositional resolution); the
/// probe's unchanged strict check still gates the rebuilt candidate.
///
/// Default ON. `--no-probe-ite-lift-promoter` (or the parent
/// `--no-consequence-replay`) restores the baseline byte-for-byte: the leaf
/// stays a trust step and the probe declines as before. UNSAT-only, and it
/// cannot lower an admission: its two outcomes are "a probe that produced no
/// strict proof now produces one" and "nothing changed".
pub(crate) fn probe_ite_lift_promoter_enabled() -> bool {
    consequence_replay_enabled() && !ay_core::misc_cli_flags().no_probe_ite_lift_promoter
}

/// Kill switch for the quantifier PROXY ABSTRACTION
/// (#quantifier-proxy-abstraction): stage 2 of the quantifier-instantiation
/// plan. Before it, `flatten_and_strip_quantifiers` deleted every assertion
/// that mentioned a quantifier anywhere, so an UltimateAutomizer goal
/// `(or (not G1) … (not Gn) (forall x̄. ¬φ))` lost its GROUND disjuncts too and
/// the ground solve reported `num_conflicts=0 num_decisions=0`. With it on, the
/// maximal quantifier subterms of such an assertion are replaced by fresh Bool
/// proxies and the rewritten assertion survives, so the ground solver finally
/// sees the goal.
///
/// Default ON; `--no-quantifier-proxy-abstraction` restores the deletion
/// byte-for-byte (nothing is minted, no assertion is rewritten, and
/// `quantifier_abstraction_active` is never set, so every downstream gate reads
/// exactly its baseline value).
///
/// UNSAT-ONLY BY CONSTRUCTION. The abstraction is an over-approximation — a
/// model of the authored problem extends to the abstracted one by
/// `q_i := ⟦Q_i⟧`, but a model of the abstracted problem assigns the proxies
/// freely — so a refutation transfers to the authored problem while a
/// satisfying assignment does not. Every solve in which the pass fired
/// therefore publishes `unknown` instead of `sat`; see the arm at the head of
/// `classify_quantifier_result` and the publication sweep at the tail of
/// `map_quantifier_result`.
pub(crate) fn quantifier_proxy_abstraction_enabled() -> bool {
    !ay_core::misc_cli_flags().no_quantifier_proxy_abstraction
}

/// Kill switch for Skolem-witness guarded instantiation of proxied
/// quantifiers (#skolem-guarded-proxy-instances).
///
/// The proxy abstraction above keeps the ground disjuncts of a
/// disjunct-position quantifier but leaves the proxy `q` FREE, so the ground
/// solver assigns it at will and reports `Sat` over an over-approximation.
/// This pass adds the one class of constraint that is sound for a quantifier in
/// ANY position: `(or (not phi[t]) q)` for a proxied existential and
/// `(or (not q) phi[t])` for a proxied universal, at ground tuples `t` drawn
/// from THIS solve's Skolem constants. No instance is ever conjoined
/// unconditionally, which is exactly what separates it from the
/// `#auflia-disjunct-forall-false-unsat` wrong-`unsat`.
///
/// Requires the proxy abstraction: with no proxy there is no guard to hang an
/// instance on. Default ON; `--no-skolem-guarded-proxy-instances` restores the
/// free-proxy assertion vector byte-for-byte.
///
/// UNSAT-ONLY. The guards constrain the proxies but do not define them, so the
/// abstraction stays an over-approximation and
/// `quantifier_abstraction_active` continues to forbid every `sat`
/// publication. The only transition this pass can cause is `unknown -> unsat`.
pub(crate) fn skolem_guarded_proxy_instances_enabled() -> bool {
    quantifier_proxy_abstraction_enabled()
        && !ay_core::misc_cli_flags().no_skolem_guarded_proxy_instances
}

/// Kill switch for GUARDED INSTANCE CLAUSES from the E-matcher
/// (#quantifier-guarded-instances): stage 3a of the quantifier-instantiation
/// plan. Requires the stage-2 abstraction, and is off whenever that is off,
/// because a guarded clause names the Boolean proxy that pass minted — with no
/// proxy there is nothing to guard the instance with.
///
/// Before it, `perform_ematching_with_generations` refused outright to
/// instantiate a `forall` the assertion set does not ENTAIL
/// (`ematching/mod.rs`, `#auflia-disjunct-forall-false-unsat`), because every
/// caller conjoins the returned instance as a TOP-LEVEL fact and that is
/// licensed only for an entailed universal. With it on, such a quantifier is
/// still never conjoined: its instances are collected in a SEPARATE result
/// vector and asserted only as `(or (not q) body[t̄])`, which is valid at any
/// polarity and in any position.
///
/// Default ON; `--no-quantifier-guarded-instances` restores the refusal
/// byte-for-byte (the matcher takes the same `continue`, nothing lands in the
/// guarded vector, and no clause is built).
///
/// UNSAT-ONLY BY CONSTRUCTION, twice over. The clause is asserted only while
/// the proxy abstraction is live, and that already forbids every `sat`
/// publication for the solve; and independently, a guarded instance is never
/// tagged as a support axiom, never marks its quantifier `instantiated`, and
/// never enters `unconditional_forall_roots` — so every SAT-side gate reads the
/// value it read before the guarded clause existed.
pub(crate) fn quantifier_guarded_instances_enabled() -> bool {
    quantifier_proxy_abstraction_enabled()
        && !ay_core::misc_cli_flags().no_quantifier_guarded_instances
}

/// Whether the guarded ENUMERATIVE lane is the problem's ONLY route to any
/// quantifier material in this solve (#quantifier-guarded-enumerative).
///
/// This is the structural trigger the lane is gated on. It is a property of
/// the solve, read at the one point that can see it — after the E-matching
/// rounds have run and before `setup_cegqi_for_unhandled` enumerates — never a
/// property of a division, a file name, or a logic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EnumerativeAdmission {
    /// The E-matcher created NO instance in this solve. Whatever the guarded
    /// clauses carry is the whole of the quantifier material the ground solve
    /// will see, so enumeration is the only route there is.
    OnlyRoute,
    /// The E-matcher already created instances. The ground problem is already
    /// carrying instantiation material and the enumerated clauses would be
    /// piled on top of a search that is working.
    MatcherProduced,
}

/// GUARDED ENUMERATIVE instances (#quantifier-guarded-enumerative): stage 3b.
/// Same clause shape and the same proxy requirement as
/// [`quantifier_guarded_instances_enabled`], applied to the triggerless
/// enumerative lane in `setup_cegqi_for_unhandled` instead of to the
/// E-matcher. Enumeration ranges over a synthesized ground basis rather than
/// over terms the problem already contains, so it can enlarge the clause set
/// on files the matcher leaves alone — which is why it carries its own gate.
///
/// # The gate is STRUCTURAL, and the structure was measured
///
/// A global default was tried and reverted: corpus-wide, uniform, 779 files in
/// both arms, it was **net −1** (the development design notes
/// 2026-09-11-guarded-enumerative-ab.md`) while being worth **+65 of 200** on
/// `BV 2018-Preiner-cav18`. An effect with that shape needs a predicate, not a
/// default.
///
/// The predicate is `admission == OnlyRoute`, and it is the measured separator
/// rather than a guess. On the AUFDTLIRA `spark2014bench` files where the lane
/// LOSES a refutation the E-matcher had already created 423-1 295 instances
/// before the lane ran; on every `2018-Preiner-cav18` file that reaches the
/// quantifier pipeline it has created **0** (15 of 15 sampled, and 0 author
/// triggers). Clause volume does NOT separate them — a gained AUFDTLIRA file
/// and a lost one assert 122 and 124 guarded clauses respectively — so a
/// budget on the clause count would have cut the wrong set.
///
/// # Why the loss happens, measured
///
/// On `AUFDTLIRA …string_search.ads_35_14_postcondition___00` the lane takes
/// the guarded clause count from 24 to 524 (5 triggerless non-entailed
/// universals x the 100-instance enumeration cap). That takes the ground
/// problem from 6 028 to 24 119 clauses, 2 883 to 11 141 variables, 7 681 to
/// 38 175 terms and 47 MB to 1 441 MB — and the DT+LIRA theory's final check
/// then returns `Unknown` (`ExtensionUnknown`) at the same DT unroll depth
/// where the lane-off arm returns `Unsat` in 0.52 s. It is NOT a deadline (at
/// `-T:600` it still stops at 59 s), NOT the E-matching budget (3 rounds and
/// 555 instances in BOTH arms), NOT memory (1.4 GB against a ~41 GB ceiling)
/// and NOT the ground conflict/decision budget (132 conflicts and 165k
/// decisions against allowances of 400k and 24M). The lane makes a search the
/// solver would otherwise finish become *theory-inconclusive*.
///
/// `--quantifier-guarded-enumerative` forces the lane on everywhere, which is
/// the arm the corpus-wide default measurement used and the way to reproduce
/// it. `--no-quantifier-guarded-enumerative` restores the pre-gate assertion
/// vector byte-for-byte; so does the parent `--no-quantifier-guarded-instances`.
pub(crate) fn quantifier_guarded_enumerative_enabled(admission: EnumerativeAdmission) -> bool {
    let flags = ay_core::misc_cli_flags();
    quantifier_guarded_instances_enabled()
        && !flags.no_quantifier_guarded_enumerative
        && (flags.quantifier_guarded_enumerative || admission == EnumerativeAdmission::OnlyRoute)
}

/// Kill switch for the COUNTEREXAMPLE-FREE CONSEQUENCE RE-SOLVE
/// (#quantifier-ce-free-resolve): stage 4 of the quantifier-instantiation
/// plan.
///
/// CEGQI asserts the counterexample lemma `¬B[c̄]` of an entailed universal as
/// a top-level conjunct. That formula is a HYPOTHESIS (the negation of an
/// assertion, at fresh constants), so a refutation of the CE-augmented ground
/// problem is ambiguous, and `disambiguate_cegqi_unsat` exists to attribute it
/// afterwards — which, for a published query, needs a translated authored-scope
/// certificate the consequence replay can build only for small instance sets.
/// Every other exit of that apparatus is fail-closed `unknown`, and a second
/// exit refuses the dispatch outright when a counterexample constant sits
/// under integer `div`/`mod`.
///
/// With this on, a CEGQI-forall solve that fails closed on either exit is
/// RE-SOLVED, live, over the exact pre-dispatch assertion vector with the
/// counterexample conjuncts removed (plus the entailed-instance support axioms
/// recorded since). Every remaining member is a consequence of the authored
/// problem, so the re-solve's UNSAT is a refutation of it — no attribution
/// question remains, and the verdict is classified exactly as an
/// E-matching-only refutation of the same problem. The plan named the
/// cvc5/z3 counterexample-literal clause `(or (not g) ¬B[c̄])` for this; for a
/// refutation-only re-solve that clause is satisfiable by `g := false` in any
/// model of the rest, so omitting it is the same theorem with less to solve.
/// The invariant that licenses the routing ("no counterexample conjunct, and
/// no term over a counterexample constant, survives in the re-solved vector")
/// is COMPUTED over that vector at the point it is consumed, never carried as
/// a producer-set boolean.
///
/// Default ON; `--no-quantifier-ce-free-resolve` restores the fail-closed
/// `unknown` byte-for-byte (no re-solve runs).
///
/// UNSAT-ONLY BY CONSTRUCTION. It runs only after every existing CEGQI arm has
/// produced a fail-closed `unknown`, so no existing `sat` or `unsat` verdict
/// is reachable through it, and a re-solve that does not refute restores the
/// predecessor state and keeps that `unknown`. Every `sat` gate on the CEGQI
/// path reads exactly the values it read before.
pub(crate) fn quantifier_ce_free_resolve_enabled() -> bool {
    !ay_core::misc_cli_flags().no_quantifier_ce_free_resolve
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
