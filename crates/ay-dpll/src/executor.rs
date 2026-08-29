// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT executor - orchestrates frontend and theory solver
//!
//! Provides a high-level interface for executing SMT-LIB commands with
//! theory integration.

// #8529: Use deterministic hash maps in all builds.
use crate::executor_types::{
    ExecutorError, Result, SolveResult, Statistics, UnknownOrigin, UnknownReason,
};
use crate::incremental_state::IncrementalSubsystem;
use crate::quantifier_manager::QuantifierManager;
use crate::VerificationLevel;
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{ClausificationProof, Proof, Sort, TermId, TermStore, TheoryLemmaProof};
use ay_frontend::{Command, CommandResult, Context, OptionValue};
use ay_proof::PartialProofCheck;
use ay_sat::{ClauseTrace, SatUnknownReason};
use proof_original_rebuild::bv_lia_recovery_state::ExactIteUfDefinitionRecovery;
use std::cell::{Cell, RefCell};
use std::sync::{atomic::AtomicBool, Arc};
use std::time::Duration;

// Combined theory solvers
pub use crate::combined_solvers::TheoryCombiner;
// Attributed reason for a refutation that carries no derivation. Public
// because `Executor::last_proof_decline` returns it; diagnostic only.
pub use proof::ProofDeclineMechanism;
// Format helpers - format_sort, format_symbol now used in executor/commands.rs

// Incremental state types
use crate::incremental_state::{IncrementalBvState, IncrementalFpState, IncrementalTheoryState};

include!("executor/config.rs");

mod accessors;
mod array_ext_shadow;
pub(crate) use array_ext_shadow::ArrayExtShadow;
mod assumption_solving;
mod bv_mbqi;
mod cert_accounting;
// Re-exported at the crate root as `ay_dpll::CertificationAccounting` so a
// benchmark harness or CI gate outside this crate can read the counters
// without `--stats` plumbing. Read-only: the type exposes totals and a
// diagnostic reset, and nothing in the solver consults it.
pub use cert_accounting::CertificationAccounting;
mod check_sat;
mod check_sat_assuming;
mod commands;
mod core_minimize;
mod diff_logic;
pub(crate) mod dl_theory;
mod dt_axioms;
mod exact_exists_bounds;
mod exact_forall_exists;
mod finite_model_mbqi;
pub(crate) mod ite_lift;
pub(crate) mod lean_firewall;
pub(crate) mod lemma_cache;
mod lnh_symmetry;
mod logic_detect;
mod mbqi;
mod mod_div_elim;
mod model;
mod nra_model_state;
pub(crate) mod optimization;
mod partition_rescue;
mod proof;
mod proof_array_ext;
mod proof_euf_lemma;
mod proof_fresh_def;
mod proof_original_rebuild;
mod proof_repair;
use proof_repair::*;
pub(crate) mod proof_propagated_rewrite;
mod proof_resolution;
mod proof_rewrite;
mod proof_rewrite_division;
mod proof_rewrite_terms;
mod proof_surface_syntax;
mod purify_bool_args;
mod purify_int_uf_arith;
mod qe_prepass;
mod qe_route;
mod quantified_sat;
mod quantifier_loop;
mod query_authority;
mod query_role;
pub(crate) use query_role::QueryPublicationRole;
mod query_state;
mod rewrite_const_array_reads;
mod rm_domain;
mod solve_deadline;
mod stats_contract;
pub(crate) mod theories;
mod uflia_model_repair;
mod unsat_cert;
use model::Model;
// Re-export the SAT-emission witness token so the API boundary
// (`api::types::results`) can name it while its constructor stays private to
// the `sat_emit` module's two complete checked lanes (#sat-chokepoint).
pub(crate) use model::sat_emit::SatCertificate;
pub(in crate::executor) use query_authority::AuthoredPlainHardQueryPermit;
pub(in crate::executor) use query_authority::QuantifiedSatAuthorityGrant;
pub(crate) use query_authority::{NativeSoftQueryBinding, QueryAuthorityEpoch};
include!("executor/query_state_exports.rs");
pub(crate) use solve_deadline::SolveDeadlineCell;
pub(crate) use unsat_cert::{probe_cert_reject_raw, UnsatCertificate};

/// Red zone for `stacker::maybe_grow` at the executor entry points
/// ([`Executor::new`], [`Executor::execute`], the check-sat pipeline, and
/// `api::Solver` construction). When remaining stack is below this threshold,
/// stacker allocates a new segment before entering the guarded body. This
/// prevents repeated mmap/munmap cycles from inner theory guards (e.g., NRA's
/// 4 MiB red zone) that cause extreme slowdown on small thread stacks in debug
/// mode (#6783), and lets embedders drive the executor from small threads
/// (e.g. libtest's default 2 MiB test threads) without overflow: the
/// construction + command-dispatch chain alone has large constant frames in
/// low-opt builds (~0.3 MiB at opt-level 1, ~0.6 MiB at opt-level 0 measured
/// 2026-07-18 — an embedder's dev-profile build compiles ay-dpll at opt 0).
///
/// Must exceed NRA's own 4 MiB red zone so the outer grow covers the inner
/// check, eliminating the double-grow penalty.
pub(crate) const EXECUTOR_STACK_RED_ZONE: usize = if cfg!(debug_assertions) {
    6 * 1024 * 1024 // 6 MiB in debug — exceeds NRA's 4 MiB red zone
} else {
    2 * 1024 * 1024 // 2 MiB in release
};

/// Stack segment size allocated by stacker when the red zone is reached.
/// 16 MiB provides ample room for the entire solve pipeline including
/// theory solvers, model validation, and proof checking in debug mode.
pub(crate) const EXECUTOR_STACK_SIZE: usize = 16 * 1024 * 1024;
pub(crate) use theories::ArrayExtWitnessCache;
pub(crate) use theories::BoundRefinementReplayKey;
pub(crate) use theories::{SharedRescuePairCounter, DEFAULT_RESCUE_PAIR_BUDGET};

// NOTE: Clause Retention for Incremental Solving (Kani Fast Requirement 1.2)
//
// IMPLEMENTED: BV incremental (via solve_bv_core + BvSolveConfig::qf_bv_incremental)
// uses assumption-based clause retention.
//
// Key design:
// 1. A persistent SAT solver is maintained across check-sat calls
// 2. Each assertion gets a selector variable `s`
// 3. Clauses are added as implications: (-s ∨ clause_lits)
// 4. At check-sat time, selectors for in-scope assertions are passed as assumptions
// 5. Popped assertions have their selectors excluded, disabling their clauses
// 6. Learned clauses are retained across calls, providing the performance benefit
//
// This approach avoids the complexity of tracking global vs scoped assertions
// and syncing SMT push/pop with SAT push/pop. Instead, we let the SAT solver's
// assumption-based solving handle the scoping naturally.

/// SMT executor that coordinates frontend parsing with theory solving.
pub struct Executor {
    /// Frontend context for elaboration
    pub(crate) ctx: Context,
    /// Opaque identity of the currently active public decision attempt.
    /// Rotated by `begin_public_solve` before preflight/elaboration so a permit
    /// from an earlier, textually identical query can never become current.
    pub(in crate::executor) query_authority_epoch: QueryAuthorityEpoch,
    /// Origin canary for query-authority unit tests.
    #[cfg(test)]
    pub(in crate::executor) last_authored_query_authority_seen: bool,
    /// Strings NF-engine closure 5 (`--str-nf`) bookkeeping: whether EVERY
    /// string lemma lowered into the SAT solver during the current solve was
    /// of a UNIVERSALLY VALID kind (exact extended-function reduction axioms
    /// over fresh cached skolems, or tautological splits `p ∨ ¬p`).
    ///
    /// Context-dependent kinds (`ConstSplit`, `VarSplit`, `ConstUnify`) and
    /// the unconditionally-asserted `ContainsPositive` decomposition clear
    /// this flag: their clauses are only valid relative to the NF alignment
    /// that produced them, so a propositional UNSAT resting on them is not a
    /// proof. Set by the single lowering chokepoint
    /// `create_string_lemma_clauses`; consumed by the post-lemma UNSAT gate.
    pub(crate) string_lemma_kinds_all_valid: bool,
    /// #boolarg-orphan: `original UF application -> solver-visible twin` for the
    /// applications `purify_bool_args` rewrote in the CURRENT check-sat.
    ///
    /// The purification pass replaces a compound Boolean argument with a fresh
    /// proxy and substitutes it through every assertion, so the solver registers
    /// — and a model pins — only `f(proxy)`. `check_sat` then RESTORES the
    /// original assertions, and every post-solve consumer (the independent model
    /// gate above all) asks about `f(<compound>)`: an application present in no
    /// assertion the solver saw, hence pinned by no model, hence "model commits
    /// no value for this application of `f`" and a fail-closed `unknown` on a
    /// genuinely satisfiable input.
    ///
    /// The index republishes the value the solve ALREADY DECIDED under the
    /// original id. It is REPLACED (never merged) at every purification, so a
    /// proxy from an earlier check-sat can never be read back.
    pub(crate) bool_arg_orphan_index: ay_core::kani_compat::DetHashMap<TermId, TermId>,
    /// QF_AX fixpoint budget multiplier (#qfax-budget-ladder): 1 = standard;
    /// the dispatch retries a degraded-unknown solve once with a raised tier.
    pub(crate) qfax_budget_multiplier: usize,
    /// #qfax-cegar: a sound blocking clause derived from a strict-oracle
    /// arrays rejection. Set by the validation pipeline when the violated
    /// chain equality is PROVEN to hold under the rejected model's index
    /// pattern by symbolic cell reduction (element-independent — cells
    /// reduce to structurally identical terms), so excluding that pattern
    /// cannot exclude any genuine model. Literals are (atom, value-to-block).
    pub(crate) qfax_refinement_clause: Option<Vec<(TermId, bool)>>,
    /// #qfax-rejected-target: the array assertion the LAST strict/gate
    /// rejection named. The witness completion's cheap already-witnessed
    /// skip (general evaluator) is unreliable exactly on such assertions
    /// (evaluator says the diseq holds; the oracle computed the chains
    /// equal), so the completion bypasses the skip for this one target —
    /// zero cost on the happy path.
    pub(crate) last_rejected_array_assertion: Option<TermId>,
    /// Re-entrancy guard for the rejected-target repair retry.
    pub(crate) qfax_retry_done: bool,
    /// #uflia-cong-repair-arm: enable-flag threaded into the UFLIA
    /// `TheoryCombiner` for the accept-point UF function-graph consistency
    /// scan. Set `true` ONLY inside `check_sat_guarded` for the single armed
    /// re-solve (then reset `false` immediately after), so it never leaks past
    /// that window — the scan is off on every first-pass solve.
    pub(crate) arm_uflia_congruence_repair: bool,
    /// #relevancy-lazy-routing: when `true`, the eager split-loop arm arms the
    /// SAT solver's wander-abort trip-wire each round, so a WANDERING eager
    /// attempt aborts early (Unknown + sticky trip signal) instead of burning
    /// the whole deadline. Set only around the UFLIA hybrid's eager first
    /// attempt; always reset immediately after.
    pub(crate) split_eager_wander_abort: bool,
    /// Inc5 #fused-detour: when `true`, the EAGER split-loop arm runs its
    /// per-round SAT solves with the relevancy brancher in HARD mode (engage
    /// on every decision) on top of the live TheoryExtension — the fused
    /// "relevancy-hard + eager theory propagation" regime
    /// (the development design notes §2 Inc5). Set
    /// ONLY around the UFLIA hybrid's fused detour arm
    /// (`--uflia-fused-detour=1`, combined/mod.rs #fused-detour slot);
    /// always reset immediately after (plus the unconditional post-attempt
    /// and entry-defensive resets in `solve_uf_lia`). Default `false` keeps
    /// every eager expansion (eager1, the hybrid resume, AUFLIA/UF+LRA
    /// lanes) byte-identical. `--sat-relevancy` still kills it (env override
    /// wins, mirroring the lazy seam).
    pub(crate) split_eager_relevancy_hard: bool,
    /// #relevancy-lazy-routing: when `true`, the lazy split-loop arm runs its
    /// per-round SAT solves with the relevancy brancher in HARD mode (engage
    /// on every decision — the design prototype's regime). Set only around the
    /// UFLIA hybrid's lazy fallback / forced-lazy attempt; always reset
    /// immediately after. `--sat-relevancy` still kills it (env override wins).
    pub(crate) split_lazy_relevancy_hard: bool,
    /// #relevancy-lazy-routing: bounded lazy-DETOUR conflict budget. When
    /// `Some(n)`, the lazy split-loop arm caps the WHOLE attempt's SAT work at
    /// `n` conflicts (plus a 32x decision-budget companion for conflict-light
    /// churn) past the persistent solver's counters at attempt entry —
    /// exhaustion surfaces as the solver's deterministic `ResourceBudget`
    /// Unknown, which breaks the split loop. Set only around the UFLIA
    /// hybrid's BOUNDED lazy detour (the forced `AY_UFLIA_ARM=lazy` arm stays
    /// unbounded); always reset immediately after. Trajectory-only: an
    /// exhausted detour yields `Unknown` and the hybrid falls back to the
    /// eager arm for the remaining budget.
    pub(crate) split_lazy_detour_conflict_budget: Option<u64>,
    /// #uflia-cong-repair-arm: `true` while a UFLIA `solve_uf_lia` combiner
    /// solve is in flight (set before its split loop, cleared per solve at
    /// `check_sat_internal` entry). Scopes the independent gate's
    /// congruence-repair arming signal to UFLIA-lane refutations so a
    /// `ModelViolates` from any other theory never triggers a wasteful
    /// re-solve.
    pub(crate) uflia_congruence_lane: bool,
    /// #uflia-cong-repair-arm: set `true` by the independent model gate's
    /// `ModelViolates` arm when `uflia_congruence_lane` — a UFLIA function-
    /// graph refutation of the emitted model. Read once by `check_sat_guarded`
    /// to decide whether to arm + re-solve. Reset at `check_sat_guarded` entry.
    pub(crate) uflia_congruence_gate_rejected: bool,
    /// #uflia-cong-repair-arm: retry-once latch (loop guard). Ensures the
    /// gate<->resolve arming fires AT MOST ONCE per public check-sat; a
    /// still-rejected armed re-solve falls through to a fail-closed Unknown.
    pub(crate) uflia_congruence_retry_done: bool,
    /// #uflia-model-repair (§3.2 targeted model-repair lever,
    /// `AY_UFLIA_MODEL_REPAIR=1`, default off = byte-identical): the UFLIA
    /// candidate model snapshotted in `check_sat_guarded` IMMEDIATELY BEFORE
    /// `emit_sat_verdict`, i.e. before the gate battery can reject it and
    /// erase it (`downgrade_sat_after_gate` / the strict-oracle degrade / the
    /// `uf_table_conflict` discard all clear `last_model`). This is the
    /// rejection EVIDENCE the targeted repair re-solve reads: which
    /// assertions the candidate falsifies and the concrete colliding value
    /// assignment. A solve can reject SEVERAL distinct candidates (07_09:
    /// an in-attempt strict rejection at ~1s AND an independent-gate
    /// rejection of the resume's model at ~10s), and each names a different
    /// trap; all of them are blocked. Capped small (see push sites).
    /// Env-gated at the capture sites; always empty flags-off.
    pub(in crate::executor) uflia_repair_candidates: Vec<Model>,
    /// #uflia-model-repair: UF function tables the `uf_table_conflict`
    /// discard (model/completion.rs) found semantically inconsistent after
    /// cross-theory merging. That discard runs BEFORE the independent gate
    /// and previously erased the evidence a repair needs (relevancy design
    /// §7); under the env gate the table names are preserved here
    /// (diagnostic + repair scoping). Verdict flow is unchanged.
    pub(crate) uflia_repair_conflict_tables: Vec<String>,
    /// #uflia-model-repair: once-per-check-sat latch for the targeted repair
    /// re-solve (mirrors `uflia_congruence_retry_done`, which stays the
    /// blind re-solve's own latch).
    pub(crate) uflia_model_repair_done: bool,
    /// #uflia-model-repair: routing flag for the ONE targeted repair
    /// re-solve (`AY_UFLIA_MODEL_REPAIR_ROUTE=detour`): `solve_uf_lia`
    /// skips the eager first attempt and enters the hybrid's bounded
    /// relevancy-hard lazy detour directly. Measured NON-default: on the
    /// model-rejection tail the detour theory-spins without reaching an
    /// accept point, while the armed eager arm converts. Set only inside
    /// `uflia_targeted_model_repair_resolve`; reset immediately after and
    /// defensively at `check_sat_guarded` entry. Can only ever be `true`
    /// under `AY_UFLIA_MODEL_REPAIR=1`.
    pub(crate) uflia_repair_detour_direct: bool,
    /// #uflia-model-repair: default routing for the ONE targeted repair
    /// re-solve: force the EAGER arm as a single full-window run (no
    /// wander-abort reroute, no detour, no resume) — the arm that reaches
    /// N-O accept points on the model-rejection tail (every rejected
    /// candidate came from an eager-family arm), now steered by the
    /// installed trap blocks and the armed accept-point repair scan +
    /// finite-domain rescue. Set only inside
    /// `uflia_targeted_model_repair_resolve`; reset immediately after and
    /// defensively at `check_sat_guarded` entry. Can only ever be `true`
    /// under `AY_UFLIA_MODEL_REPAIR=1`.
    pub(crate) uflia_repair_eager_direct: bool,
    /// L2 (combined-theory-engine campaign): `true` while the lazy-DT-AUFLIA
    /// lane (`try_solve_dt_auflia_lazy`) runs its inner combiner solve under the
    /// `AY_DT_LAZY_AUFLIA_EAGER` sub-flag. Forces the UFLIA split arm to EAGER
    /// (no hybrid lazy detour) for that inner solve only.
    ///
    /// MEASURED RATIONALE: the L1a sparse on-demand DT axioms collapse the base
    /// clausification so the residual is EAGER-tractable (gl.smt2: eager arm
    /// UNSAT in 26 decisions / ~1.2s). The default UFLIA HYBRID instead spends
    /// the whole wall budget in a non-converging lazy DETOUR (~1500 rounds, 0
    /// net progress, returns Unknown) before the eager RESUME solves it — the
    /// measured 96s+ wall is that wasted detour, NOT the per-round combiner
    /// rebuild the L2 brief hypothesized (theory-check is ~3ms/round; combiner
    /// construction is ~10% of the wall). Skipping the detour when the sparse
    /// axioms are present is the actual wall-clock lever (155s → 2.4s here).
    ///
    /// Sound: the eager arm is the pre-routing pipeline byte-identical path — a
    /// complete, independently gate-validated solve; forcing it only changes the
    /// search TRAJECTORY, never a verdict. If the eager arm returns Unknown the
    /// lane falls through to the eager DT-axioms authority exactly as before.
    /// Set only inside `try_solve_dt_auflia_lazy`; reset immediately after and
    /// defensively at `check_sat` entry. Can only be `true` under both
    /// `AY_DT_LAZY_AUFLIA` and `AY_DT_LAZY_AUFLIA_EAGER`.
    pub(crate) dt_lazy_auflia_eager_arm: bool,
    /// #abv-subst-model-retry: `true` while the current check-sat's eager BV
    /// lane solve (QF_BV/QF_ABV/QF_UFBV/QF_AUFBV single-shot) ran preprocessing
    /// with VariableSubstitution. Scopes the model-rejection retry signal to
    /// the only lane where substitution recovery can manufacture an invalid
    /// model (wishlist#1: select-over-eliminated-index decoupling). Cleared at
    /// `check_sat_internal` entry, set by `solve_bv_core_inner` when a
    /// preprocessor substitution map was actually created.
    pub(crate) bv_subst_lane: bool,
    /// #abv-subst-model-retry: set when a model built after BV variable
    /// substitution recovery was REFUTED — either by the in-loop semantic BV
    /// validator (`finalize_bv_model_validation_failure`) or by the independent
    /// model gate's `ModelViolates` arm while `bv_subst_lane`. Read once by
    /// `check_sat_guarded` to re-solve with preprocessing disabled. Reset at
    /// `check_sat_guarded` entry.
    pub(crate) bv_subst_model_rejected: bool,
    /// Permit-bound semantic routing state for exact definitional-UF rejection recovery.
    pub(in crate::executor) ite_uf_definition_recovery: ExactIteUfDefinitionRecovery,
    /// #abv-subst-model-retry: retry-once latch (loop guard). The
    /// preprocessing-free re-solve fires AT MOST ONCE per public check-sat; a
    /// still-rejected re-solve stays the fail-closed Unknown.
    pub(crate) bv_subst_retry_done: bool,
    /// #abv-subst-model-retry: `true` only for the duration of the single
    /// retry re-solve; `solve_bv_core_inner` reads it to force
    /// `config.preprocess = false` so the model is built directly from the
    /// bit-blasted original assertions (no substitution recovery at all).
    pub(crate) bv_subst_retry_disable_preprocess: bool,
    /// #nonstring-seq-unsat-corroboration: reentry latch. `true` only for the
    /// duration of the single proof-mode corroboration re-solve that verifies a
    /// non-string sequence UNSAT produced WITHOUT proofs (see
    /// `check_sat_guarded`). Prevents the corroboration re-solve from recursing
    /// into the same gate.
    pub(crate) corroborating_nonstring_seq_unsat: bool,
    /// Last check-sat result
    last_result: Option<SolveResult>,
    /// Last satisfying model (if any)
    last_model: Option<Model>,
    /// Ground-instance conflict-verification support literals accumulated during
    /// this check-sat's quantifier refinement: each is `TheoryLit::new(root,
    /// true)` for a `root` that is a ground instance of an UNCONDITIONALLY-
    /// asserted Forall (top-level conjunct) AND was actually added to
    /// `ctx.assertions` (see [`crate::ematching::collect_unconditional_foralls`]).
    /// By universal instantiation every element is true in every model of the
    /// problem. Threaded into the Executor-owned pipeline conflict-verification
    /// gates and cloned onto the constructed `DpllT` so the fail-closed AUFLIA
    /// gate can reprove a genuinely-UNSAT mixed conflict whose closure depended
    /// on e-matched Seq/prophecy instances, instead of degrading to Unknown.
    /// CLEARED at the top of `process_quantifiers` (per check-sat); empty for
    /// quantifier-free problems, making the gates byte-identical to before.
    pub(crate) active_support_axioms: Vec<ay_core::TheoryLit>,
    /// Per-check-sat memo of fail-closed semantic conflict-verification
    /// verdicts (#4535 memoized verifier), keyed by the SORTED literal set of
    /// the (already deduped) theory conflict. The verdict of
    /// `verify_conflict_semantic` is a pure function of the literal SET, the
    /// term content behind the ids (append-only within a session), and the
    /// support-axiom set — so within one query, an identically re-derived
    /// conflict (observed thousands of times on verification-consumer AUFLIA VCs) can skip
    /// the fresh-solver / Nelson-Oppen re-verification. CLEARED at the top of
    /// `check_sat_internal` and whenever `active_support_axioms` is rebuilt
    /// (`process_quantifiers`), so no verdict outlives the state it was
    /// computed against. Both verdict polarities are memoized: a memoized Ok
    /// re-admits a conflict already proven jointly-UNSAT (sound to learn); a
    /// memoized Err keeps the fail-closed bail (conservative, never learns).
    pub(crate) conflict_semantic_verify_memo: crate::verification::ConflictSemanticVerifyMemo,
    /// #verify-memo (`--verify-memo=1`): sampled semantic PROPAGATION
    /// verification memo — see [`crate::verification::PropSemanticVerifyMemo`]
    /// for the key/trust-true-only/lifecycle contract. Populated only while
    /// the env flag is armed (the extension never probes or inserts
    /// otherwise), so flag-off behavior is byte-identical.
    pub(crate) prop_semantic_verify_memo: crate::verification::PropSemanticVerifyMemo,
    /// Last assumptions from check-sat-assuming (for get-unsat-assumptions)
    last_assumptions: Option<Vec<TermId>>,
    /// Minimal UNSAT core from last check-sat-assuming (subset of assumptions)
    /// This is populated when using the SAT solver's assumption-based solving.
    ///
    /// PRECISION CAVEAT: an empty/partial stored core is NOT authoritative --
    /// theory-level conflicts can prove UNSAT without registering assumption
    /// participation (EUF transitivity does), so `get-unsat-core` pads an
    /// empty mapped core to all named assertions. Verifier consumers must
    /// not treat goal-name-in-core as proof of non-vacuity without an
    /// independent base-recheck (verification-consumer does). Origin-tagged core
    /// authority is future work.
    last_assumption_core: Option<Vec<TermId>>,
    /// Mapping from assertion TermId to assertion name for unsat core extraction.
    /// Populated when produce-unsat-cores redirects check-sat through
    /// check-sat-assuming with named assertions as assumptions.
    last_core_term_to_name: Option<HashMap<TermId, String>>,
    /// Named-assert rewrite provenance for the CURRENT check-sat call
    /// (#uc-named-provenance): `rewritten TermId -> ORIGINAL (parse-time)
    /// TermId`, recorded ONLY by preprocessing passes that are per-assertion
    /// semantically EXACT (`rewrite_assertion_bool_ites`,
    /// `rewrite_select_over_array_ite`) and only under produce-unsat-cores.
    /// The named-core redirect uses it to keep a rewritten named assertion
    /// assumption-trackable under its label instead of tripping the
    /// fail-closed provenance guard (which pads the core to ALL named
    /// assertions — reduction 0 on e.g. 2018-Goel-hwbench, whose named
    /// asserts are Bool ITEs). Cleared at every
    /// `check_sat_internal_preprocess_and_solve` entry: entries never
    /// outlive the preprocessing run that created them. Chained inserts keep
    /// values parse-time ROOTS even when both passes rewrite one assertion.
    /// SOUNDNESS: a label may only ride a rewrite that preserves
    /// per-assertion equivalence — the printed core denotes the ORIGINAL
    /// named formulas, and validators re-check those; equivalence makes the
    /// two conjunction sets interchangeable. Passes that are merely globally
    /// equisatisfiable (string var inlining, purification) MUST NOT record
    /// here.
    named_assert_rewrites: HashMap<TermId, TermId>,
    /// Last proof (for get-proof when UNSAT)
    last_proof: Option<Proof>,
    /// The current UNSAT verdict was independently certified semantically, but
    /// no proof was translated back to the authored problem scope.
    ///
    /// While set, proof reconstruction and every proof accessor must fail
    /// closed. Rebuilding from the outer trace after a CEGQI consequence
    /// re-solve could otherwise attach a CE-contaminated proof to a sound
    /// verdict established from different premises.
    last_unsat_proof_reconstruction_suppressed: bool,
    /// One aggregate parsed-source work envelope shared by every proof pass of
    /// the query in flight. Each pass charges the traversal/clone/format work
    /// it is about to perform; the ceiling is the same
    /// `MAX_AGGREGATE_SOURCE_WORK` that used to be pre-charged sixteen times
    /// over at the build preflight, so oversized sources still fail closed on
    /// their first pass while bounded ones stop being vetoed for work no pass
    /// ever performs.
    proof_source_work: proof_trust_surgery_surface_audit::ProofSourceWorkEnvelope,
    /// This solve asserted at least one quantified consequence whose exact
    /// authored-scope `forall_inst` derivation was not registered.  A raw UNSAT
    /// may still be mathematically sound, but its trace is not publication
    /// authority; result mapping must use the semantic-only proof firewall.
    quantified_proof_translation_incomplete: bool,
    /// The deep-QE `Unknown` fallback belongs only to
    /// [`Executor::deep_qe_unknown_retry`]; it is the sole condition under
    /// which the pre-pass adopts a rewrite, preserving certificate-bearing
    /// authored shapes that could still decide the solve.
    deep_qe_retry_armed: bool,
    /// The #quantified-trace-arming `Unknown`-fallback lane is active for the
    /// solve currently in flight. Set ONLY by
    /// [`Executor::quantified_trace_arming_unknown_retry`], which owns the
    /// one-attempt-per-public-solve contract.
    quantified_trace_retry_armed: bool,
    measured_negative_quantifier_routes: qe_route::MeasuredNegativeRoutes,
    /// Monotone check-sat pre-pass reachability counters (#prepass-reachability).
    /// Never cleared by result invalidation, so tests observe guarded pre-passes
    /// across ordinary public solves.
    prepass_reachability: PrepassReachability,
    /// Last LRAT certificate serialized from the SAT clause trace.
    ///
    /// Populated opportunistically for UNSAT results when the clause trace is
    /// complete enough to replay as a standalone LRAT certificate.
    last_lrat_certificate: Option<Vec<u8>>,
    /// Optional surface-syntax overrides for proof terms during Alethe export.
    /// Keys are canonical proof terms; values are the exact source-syntax
    /// strings from parsed input assertions.
    last_proof_term_overrides: Option<HashMap<TermId, String>>,
    /// Proof-premise provenance for temporary combined-theory assertion views.
    ///
    /// When combined routes solve over a rewritten assertion window, this
    /// records which temporary assertions still correspond to original problem
    /// premises plus the original assertion stack used to recover parsed
    /// surface syntax during proof export (#6759).
    proof_problem_assertion_provenance:
        Option<theories::solve_harness::ProofProblemAssertionProvenance>,
    /// Provenance of finite-domain quantifier expansions that REPLACED a
    /// top-level `forall` assertion in place with its ground instance
    /// conjunction (#quant-expansion-proof). Proof export re-derives consumed
    /// conjuncts from the ORIGINAL `forall` via `forall_inst`, so exported
    /// assumptions match the problem rather than the internal expansion.
    /// Cleared per check-sat alongside
    /// `proof_problem_assertion_provenance`.
    pub(crate) quant_expansion_records: Vec<QuantExpansionRecord>,
    /// Direct, independently authenticated E-matching instantiations for the
    /// current check-sat.  Cleared and nested-solve scoped alongside
    /// `quant_expansion_records`; no record outlives its authored authority.
    pub(crate) ematching_proof_records: Vec<EmatchingProofRecord>,
    /// Consequence-replay same-context probes consumed by the current query.
    pub(crate) consequence_replay_attempts: Cell<u8>,
    /// Query-wide wall envelope for consequence-replay probes; executor
    /// ownership prevents per-scope restoration from replenishing it.
    consequence_replay_probe_budget: proof::ConsequenceReplayProbeBudget,
    /// Query-wide gate-arm wall envelope (`independent_gate::probe_budget`).
    pub(in crate::executor) quantified_gate_probe_budget: model::QuantifiedGateProbeBudget,
    /// Last direct ground-pin input fingerprint and distinct-attempt count.
    pub(crate) consequence_replay_direct_state: Cell<Option<(u64, u8)>>,
    /// Probe attempts consumed by the negated-existential ground-instantiation
    /// artifact-firewall translation for the CURRENT check-sat
    /// (#inc-fparith-negated-exists-inst). Counted separately from
    /// `consequence_replay_attempts` so the two lanes cannot starve each
    /// other. Cleared per check-sat alongside `ematching_proof_records`.
    pub(crate) negated_exists_ground_inst_attempts: Cell<u8>,
    /// Probe attempts consumed by the implied-universal ground-instantiation
    /// artifact-firewall translation for the CURRENT check-sat
    /// (#implied-forall-ground-inst). Counted separately from
    /// `consequence_replay_attempts` and the negated-exists lane so the three
    /// lanes cannot starve each other. Cleared per check-sat alongside
    /// `ematching_proof_records`.
    pub(crate) implied_forall_ground_inst_attempts: Cell<u8>,
    /// Single-binder Skolemization provenance for assertions REPLACED in place
    /// by `skolemize_existentials` (#skolem-unit-authority). Each record binds
    /// the authored source (`exists x. B` or `not (forall x. B)`), the exact
    /// raw substituted instance, the fresh witness, and the final asserted
    /// term. Cleared per check-sat alongside `ematching_proof_records`.
    pub(crate) skolem_instance_records: Vec<SkolemInstanceRecord>,
    /// Node-local single-binder Skolemization provenance for EVERY positive
    /// `exists` / negative `forall` the deep Skolemizer eliminated, nested
    /// occurrences included (#skolem-witness-sat). Consumed ONLY by the
    /// skolem-witness SAT confirmation arm, which replays each record
    /// independently at consumption. Cleared per check-sat alongside
    /// `skolem_instance_records`.
    pub(crate) skolem_witness_records: Vec<SkolemWitnessRecord>,
    /// BV-MBQI eval-folded-`false` instance provenance
    /// (#bv-mbqi-false-instance-authority, P3b). Recorded at the exact
    /// `try_bv_mbqi_refinement` push site when a boundary instance
    /// constant-folds to the literal `false` term. Lifecycle mirrors
    /// `skolem_instance_records` exactly: cleared per check-sat /
    /// check-sat-assuming / reset, and saved+restored across both nested-solve
    /// rollbacks so no record outlives a rolled-back speculative window.
    pub(crate) bv_mbqi_false_instance_records: Vec<BvMbqiFalseInstanceRecord>,
    /// Generic-MBQI falsifying-instance provenance
    /// (#mbqi-instance-provenance). Written ONLY at `try_mbqi_refinement`'s
    /// ground re-solve UNSAT return, with the exact (source quantifier,
    /// positional binder values, folded instance) triples accumulated across
    /// the refinement rounds of that one call. Records are HINTS with no
    /// authority: the consequence-replay consumer re-derives the exact
    /// structural instance (`exact_forall_instance`) and the strict
    /// `forall_inst` validator re-replays the substitution on the stitched
    /// candidate, so a wrong record can only decline a translation. Consumed
    /// (taken) immediately by `try_skipped_quantifier_mbqi_refinement`;
    /// cleared per check-sat alongside `ematching_proof_records`.
    pub(crate) mbqi_refinement_instance_records:
        Vec<crate::ematching::ForallInstantiationProvenance>,
    /// Exact meters for the ground-conflict decomposition arms
    /// (#ground-conflict-decomp), published into `last_statistics` by
    /// `publish_strict_check_counters` (`--stats`). Cumulative within this
    /// executor.
    pub(crate) ground_conflict_decomp_meters: GroundConflictDecompMeters,
    /// qpf premise-forced instance provenance (#ppp-c7, L2). Recorded at the
    /// exact re-solve push site in `premise_forced_binder_refutation`.
    /// Lifecycle mirrors `bv_mbqi_false_instance_records` exactly: cleared
    /// per check-sat / check-sat-assuming / reset, and saved+restored across
    /// both nested-solve rollbacks so no record outlives a rolled-back
    /// speculative window.
    pub(crate) qpf_premise_forced_instance_records: Vec<QpfPremiseForcedInstanceRecord>,
    /// Sealed context-derivation hints, cleared per query and rolled back with
    /// DT speculation; cap overflow can only make authentication decline.
    pub(crate) dt_context_conflict_records: DtContextConflictSink,
    /// `PropagateValues` producer provenance for the current check-sat
    /// (#ppp-provenance): in-place rewrite records plus the asserted defining
    /// equalities that licensed each `value_map` entry, drained from the
    /// fixed-point Preprocessor loop. Consumed by
    /// `derive_propagated_value_assumptions`, which independently REPLAYS
    /// each record into strict-checker-validated steps; the records grant no
    /// authority by themselves. Lifecycle mirrors
    /// `bv_mbqi_false_instance_records` exactly: cleared per check-sat /
    /// check-sat-assuming / reset, saved+restored across both nested-solve
    /// rollbacks so no record outlives a rolled-back speculative window.
    pub(crate) propagated_value_provenance: crate::preprocess::PropagationRecords,
    /// Re-elaborated or raw-reconstructed ORIGINAL problem-assertion terms
    /// captured by the last proof rebuild.
    ///
    /// The rebuild / trust-surgery re-elaborates each parsed assertion to
    /// recover its canonical term, and re-elaborating a `forall` surface mints
    /// FRESH binder terms (alpha-renamed; the canonical id differs from the
    /// `ctx.assertions` / `rec.original` id). Fold-collapse promotion similarly
    /// rebuilds erased source structure with raw constructors. The resulting
    /// `assume` steps carry these reconstructed terms, so the leak-2
    /// provenance gate (`proof_legit_assume_set`) must accept them. Captured
    /// once during the rebuild (stable within the solve — no re-elaboration
    /// between capture and the gate) and cleared per check-sat.
    pub(crate) last_proof_rebuild_originals: Vec<TermId>,
    /// Exact raw re-interns of top-level parsed problem assertions captured by
    /// the last proof rebuild.
    ///
    /// This is deliberately narrower than `last_proof_rebuild_originals`,
    /// which can also admit strictly checked derived repair premises. A raw
    /// term may be printed directly as an Alethe `assume` only when it occurs
    /// in both sets: the general set grants proof authority, while this set
    /// proves that its identity rendering is an actual problem-file premise.
    /// Cleared and rolled back at the same query boundaries as the general
    /// rebuild scope.
    pub(crate) last_proof_raw_original_assertions: Vec<TermId>,
    /// Why the last refutation carries no derivation, when it carries none.
    ///
    /// Diagnostic only: nothing consults this to decide a verdict, mint a
    /// certificate, or authorize an export. It exists so that the one-line
    /// `(step t0 (cl) :rule hole)` artifact — which three unrelated conditions
    /// can produce — is attributable in a corpus census instead of collapsing
    /// every cause into one label. See `executor::proof::decline`.
    pub(crate) last_proof_decline: Option<ProofDeclineMechanism>,
    /// Quality metrics from last proof validation (#4420)
    last_proof_quality: Option<ay_proof::ProofQuality>,
    /// M0(a) attribution counter (the development design notes):
    /// `check_proof_strict_with_datatypes` invocations since the last public
    /// solve began. Counting only — zero behavior change. `Cell` because the
    /// wrapper takes `&self` (existing precedent: `dt_egraph_building`).
    /// Reset with `last_statistics`, dumped through
    /// `publish_strict_check_counters` as `proof.strict_check_invocations`.
    pub(in crate::executor) strict_check_invocations: Cell<u64>,
    /// Size-scoped decline latch for the retention-off `EqDiffVar` lane
    /// (#4751): 0 until its commit gate deterministically reverts a splice
    /// (strict envelope refused it, or the spliced walk is too expensive to
    /// keep re-checking), then the PRE-SPLICE step count of the declined
    /// document. Rebuilds of a similar-sized document skip the lane instead of
    /// re-paying the gate's whole-proof metered walk for the same answer
    /// (measured ~40-110 ms, ~30 rebuilds per solve on `QF_IDL/sal/bakery`).
    /// The scope is the point: a LATER assembly can rebuild a much SMALLER
    /// document whose splice is cheap and commits — measured on
    /// `queens_bench/super_queen5-1` and `sal/lpsat/lpsat-goal-1`, whose final
    /// documents shrink to 201/21 steps and strict-certify, 3/3 deterministic
    /// — so a document under HALF the declined size re-asks the gate (and, if
    /// declined again, narrows the scope; at most log2 re-asks per executor).
    pub(in crate::executor) eqdv_retention_off_declined_at_steps: Cell<usize>,
    /// M0(a) companion counter: total proof steps submitted across those
    /// strict-check invocations (the strict checker walks every step of an
    /// accepted proof; a rejected proof stops early, so this is an upper
    /// bound labelled "submitted", not a claim every step was individually
    /// accepted). Dumped as `proof.strict_check_steps_validated`.
    pub(in crate::executor) strict_check_steps_validated: Cell<u64>,
    /// #strict-walk-memo — stored strict-check verdicts keyed on the complete
    /// walk context (literal document, term-store snapshot stamp, datatype
    /// registries, authored scope). Replays a verdict the checker already
    /// established for a byte-identical input; any context drift is a miss
    /// and a real walk. See `proof/check/strict_memo.rs` for the currency
    /// argument. `RefCell` because the chokepoint takes `&self`.
    pub(in crate::executor) strict_walk_memo: RefCell<proof::StrictWalkMemo>,
    /// #strict-walk-memo companion counter: chokepoint entries answered from
    /// the memo this publication. Real walks = invocations - hits. Dumped as
    /// `proof.strict_check_memo_hits`.
    pub(in crate::executor) strict_check_memo_hits: Cell<u64>,
    /// #cert-accounting item 3: the DECLARED consumer of the decision query
    /// currently executing on this executor.
    ///
    /// Set only by the typed `execute_internal_lemma`/`execute_all_internal_lemma`
    /// entrypoints, which save and restore the previous value around the call,
    /// so the declaration is scoped to exactly the command the caller declared
    /// it for. Unreachable from parsed SMT-LIB text.
    ///
    /// READ BY EXACTLY ONE CONSUMER: `cert_accounting`. It selects no lane,
    /// relaxes no gate, and changes no verdict — see `query_role.rs` for why
    /// the declaration deliberately lands ahead of any policy that keys on it.
    /// `Cell` because the accounting hooks run under `&self`.
    pub(in crate::executor) query_publication_role: Cell<QueryPublicationRole>,
    /// Re-entrancy depth of command-boundary decision commands on THIS
    /// executor, so `cert_accounting`'s wall-clock decision timer measures the
    /// outermost command once instead of summing nested probe solves into it.
    /// Diagnostic bookkeeping only.
    pub(in crate::executor) decision_command_depth: Cell<u32>,
    /// Reason for last Unknown result (for get-info :reason-unknown)
    last_unknown_reason: Option<UnknownReason>,
    /// The quantifier classification ended `Unknown` at the MBQI-UNSAFE PARTIAL
    /// QUANTIFIER guard (`record_unsafe_partial_unknown`) and nowhere else.
    ///
    /// #cert-consult-determinism, second half. That guard fails closed for a
    /// binder sort MBQI cannot synthesize (Array / FP / Seq / RegLan), which is
    /// a QUANTIFIER incompleteness — exactly the class the self-contained SAT
    /// certificates exist to discharge. It records two DIFFERENT reason labels
    /// for the same situation, though: `QuantifierUnhandled` when no
    /// UF-completion candidate was attempted, and the generic
    /// `UnknownReason::Incomplete` when one was attempted and failed. The
    /// certificate consult keys on the label, so merely ATTEMPTING a candidate
    /// silently removed the certificates' chance to decide the query. This flag
    /// carries the structural fact instead of the label, so both branches are
    /// admitted identically. Set by `record_unsafe_partial_unknown`, cleared at
    /// the top of every `classify_quantifier_result`.
    pub(in crate::executor) unsafe_partial_quantifier_unknown: bool,
    /// Exact production boundary that published the last Unknown result.
    ///
    /// Internal solver lanes may tentatively classify an Unknown by reason;
    /// this field is installed only at the public publication chokepoint.
    last_unknown_origin: Option<UnknownOrigin>,
    /// Statistics from last check-sat call
    last_statistics: Statistics,
    /// Debug flag for QF_UFBV solving
    debug_ufbv: bool,
    /// Whether incremental mode is enabled.
    ///
    /// Enabled by push/pop and by adding assertions after a prior solve.
    /// When true, incremental solving is used which maintains a persistent SAT
    /// solver to retain learned clauses across check-sat calls.
    pub(crate) incremental_mode: bool,
    /// Override for routing incremental QF_LIA check-sats to the eager
    /// BCP-interleaved arm (Fix B1). `None` follows the
    /// `AY_DPLL_LIA_INCREMENTAL_EAGER` env flag (default ON); `Some(false)`
    /// forces the lazy model-enumeration arm. The proof-session gate applies
    /// regardless of this override.
    pub(crate) lia_incremental_eager_override: Option<bool>,
    /// Override for routing incremental QF_LRA check-sats to the eager
    /// theory-propagating standalone split-loop path (#lra-ind). `None`
    /// follows the default (eager ON for push/pop QF_LRA, unless the
    /// `AY_LRA_INCR_NO_EAGER_STANDALONE` env kill switch is set); `Some(false)`
    /// forces the lazy persistent push/pop pipeline (used by unit tests that
    /// assert lazy-pipeline internals like `persistent_sat` existence and
    /// cross-check-sat clause-count stability). The proof-session gate applies
    /// regardless of this override (eager-incremental proof artifacts are not
    /// yet validated, mirroring the QF_LIA convention).
    pub(crate) lra_incremental_eager_override: Option<bool>,
    /// Programmatic override for the incremental QF_LRA engine lane
    /// (#lra-inc-engine, S1). `None` (default) follows the CLI default
    /// (ON unless `--dpll-no-lra-inc-engine`); `Some(true)` forces the lane on and
    /// `Some(false)` forces it off, both independent of the CLI. Exists so regression
    /// tests can exercise the lane deterministically without mutating
    /// process-global env state. The proof-session gate applies regardless.
    pub(crate) lra_inc_engine_override: Option<bool>,
    /// True while the persistent-SAT QF_LRA lane (#lra-persist-sat) is running
    /// its eager-persistent split-loop arm on the SESSION-persistent
    /// `IncrementalTheoryState` (SAT solver + Tseitin encodings persist across
    /// check-sats, with SMT push/pop mirrored as SAT scope selectors).
    ///
    /// The shared split-loop macros consult this flag at the few sites whose
    /// behavior must differ when the arm runs on scoped persistent state
    /// instead of an isolated depth-0 throwaway state:
    ///   * the "requires isolated scope depth 0" guard is lifted;
    ///   * the pre-iteration abort path must NOT pop a SAT scope (there is no
    ///     private push in the eager-persistent arm; at depth 0 the pop was a
    ///     harmless no-op, but under real SMT scopes it would misalign the
    ///     selector stack);
    ///   * the budget-exhausted continue/resume fast paths are disabled while
    ///     scope selectors are active (they re-enter the CDCL loop WITHOUT
    ///     re-composing scope-selector assumptions — INV-3);
    ///   * a model-validation-failure blocking clause is never added (its
    ///     justification is clause-DB-relative, unsafe to persist across
    ///     check-sats); the arm fails closed to Unknown and the lane falls
    ///     back to the isolated from-scratch path for that check-sat;
    ///   * bound-axiom tautologies are added globally and deduplicated via
    ///     `IncrementalTheoryState::persist_injected_bound_axioms`.
    ///
    /// Default false: every macro site behaves exactly as before.
    pub(crate) lra_persist_sat_active: bool,
    /// When true, LIA theory solvers created by this executor disable LRA
    /// theory propagation on their inner `LraSolver`
    /// (`set_no_theory_propagation`, the per-instance counterpart of
    /// `AY_NO_THEORY_PROPAGATION`).
    ///
    /// Scoped fix for the DRAGON-class QF_LIA sat-type model-search livelock
    /// (the development design notes): BCP-time
    /// implied-bounds propagation yields weak learned clauses and unstable
    /// theory-hinted phases, livelocking CDCL (>300s on queries z3 solves in
    /// 9ms); with propagation off the same query solves in ~1s. Set by the
    /// CHC BMC transition-system lane via
    /// [`Executor::set_no_lra_theory_propagation`]; default off so all other
    /// lanes (and the #9505 theory-decision beneficiaries) keep propagation.
    pub(crate) no_lra_theory_propagation: bool,
    /// Persistent state for incremental BV solving with rebuild-on-pop invalidation
    incr_bv_state: Option<IncrementalBvState>,
    /// Persistent state for the incremental FP lane (fifth incremental subsystem).
    ///
    /// Only ever populated while [`Self::fp_persistent_armed`] authorized the
    /// current `solve_fp`; every other FP entry point runs the untouched
    /// stateless pipeline and never observes this field.
    pub(crate) incr_fp_state: Option<IncrementalFpState>,
    /// One-shot authorization for the persistent FP lane.
    ///
    /// FAIL-SAFE POLARITY, and that is the whole point. `solve_fp` is reachable
    /// from six callers that substitute `ctx.assertions` out from under it —
    /// symbolic-RoundingMode enumeration (mutually contradictory branches),
    /// the pinned-Real UNSAT probe, `check-sat-assuming`'s scoped merge,
    /// ABVFP store expansion, constant-index read flattening, and the
    /// symbol-disjoint partition rescue. Sharing session state with any of them
    /// is a wrong answer (a persistent activation unit for branch `RNE` is
    /// still installed when branch `RTZ` runs).
    ///
    /// Rather than enumerate those callers and hope none is missed, the lane is
    /// OFF unless something explicitly turned it on: set at exactly one site
    /// (the primary `route_to_solver` dispatch, over the authored assertion
    /// set), cleared immediately after that dispatch returns, and CONSUMED by
    /// `std::mem::take` at the top of `solve_fp` so every re-entrant call sees
    /// `false`. Missing a substituting caller therefore costs performance, not
    /// correctness.
    pub(crate) fp_persistent_armed: bool,
    /// Persistent state for incremental theory solving (UF/LRA/LIA)
    pub(crate) incr_theory_state: Option<IncrementalTheoryState>,
    /// Style for counterexample generation (model minimization)
    counterexample_style: crate::CounterexampleStyle,
    /// Proof tracker for collecting proof steps during solving
    proof_tracker: crate::proof_tracker::ProofTracker,
    /// Query-wide allocation envelope for proof-ledger rollback snapshots.
    /// Executor ownership is load-bearing: nested proof-tracker swaps must not
    /// re-arm the cumulative budget.
    proof_checkpoint_budget: theories::ProofCheckpointBudget,
    /// Explicit proof-output request, separate from source-selected internal
    /// tracking for strict quantified-BV/self-check UNSAT certification.
    proof_output_requested: bool,
    /// Whether proof production was requested as a required artifact rather
    /// than enabled for the CLI's synthesized best-effort default.  This is
    /// explicit policy state; a reconstruction budget must never silently
    /// downgrade an API caller's `set_produce_proofs(true)` request.
    proof_artifact_required: bool,
    /// Deterministic step budget for post-UNSAT SAT-proof reconstruction
    /// (RUP replay clause scans). `None` = unlimited (explicit `--proof`,
    /// `--strict-proofs`, `:produce-proofs` scripts). `Some(n)` = best-effort:
    /// the synthesized-default proof-carrying certificate gives up after `n`
    /// clause scans and the run degrades to the existing
    /// "no proof certificate emitted" warning — the verdict is computed before
    /// reconstruction and never depends on the budget (#A2b).
    pub(crate) proof_reconstruction_step_budget: Option<u64>,
    /// Last clause trace from SAT solver (for SAT resolution proof reconstruction)
    last_clause_trace: Option<ClauseTrace>,
    /// Last var_to_term mapping from Tseitin (for SAT proof reconstruction)
    last_var_to_term: Option<HashMap<u32, TermId>>,
    /// Independently checked composition of exact SMT original-clause authority
    /// with a bounded positive-RUP refutation for the current query epoch.
    /// Witness for a finite-enum pigeonhole refutation (#dt-enum-pigeonhole).
    ///
    /// `add_finite_enum_pigeonhole_conflict` refutes by finding a `k+1` clique in
    /// the disequality graph of a `k`-constructor all-nullary datatype sort, then
    /// asserts bare `false`. Recording the clique here lets the proof layer
    /// rebuild the ARGUMENT instead of publishing an uncheckable `[false]`.
    last_finite_enum_pigeonhole: Option<FiniteEnumPigeonholeWitness>,
    /// Sealed, query-bound authority for the exact canonical finite-enum proof
    /// currently stored in `last_proof`.
    last_checked_finite_enum_pigeonhole: Option<proof::CheckedFiniteEnumPigeonholeProof>,
    last_checked_sat_refutation: Option<proof_resolution::CheckedSatRefutation>,
    /// Per-variable SAT trail provenance from last SAT result (#8153, #8307).
    /// Maps 0-based SAT variable index -> (decision_level, is_propagated, antecedent_var_indices).
    /// The `antecedent_var_indices` are the 0-based SAT variable indices of the
    /// other literals in the reason clause (empty for decisions).
    /// Populated after SAT results in check_sat_guarded/check_sat_assuming
    /// when a persistent SAT solver is available (incremental mode).
    last_trail_provenance: Option<HashMap<u32, (u32, bool, Vec<u32>)>>,
    /// Last clausification proof annotations (for Alethe tautology rule steps).
    /// Parallel to Tseitin clause order — annotations[i] justifies clause[i] (#6031).
    last_clausification_proofs: Option<Vec<Option<ClausificationProof>>>,
    /// Last original-clause theory proof annotations for SAT reconstruction.
    /// Parallel to SAT original clause order, including incremental NeedLemmas.
    last_original_clause_theory_proofs: Option<Vec<Option<TheoryLemmaProof>>>,
    /// Query-scoped theory-lemma kinds for solver-INJECTED axiom assertions
    /// (the DT selector/exclusivity/reconstruction families the eager and
    /// lazy DT lanes append to `ctx.assertions`). The pipeline's
    /// activation-clause placement consults this so an injected axiom's unit
    /// original carries an indexed theory authority; without it the
    /// exact-fragment builder cannot authenticate the clause and mandatory
    /// certification discards the lane's UNSAT (#dt-lazy-axiom-authority).
    pub(crate) injected_axiom_theory_kinds:
        ay_core::kani_compat::DetHashMap<TermId, ay_core::TheoryLemmaKind>,
    /// Quantifier manager for persisting generation tracking across E-matching rounds
    pub(crate) quantifier_manager: Option<QuantifierManager>,
    /// Maximum learned clauses for SAT solver (None = no limit) (#1609)
    learned_clause_limit: Option<usize>,
    /// Maximum clause DB size (bytes) for SAT solver (None = no limit) (#1609)
    clause_db_bytes_limit: Option<usize>,
    /// Interrupt flag propagated from API-level `check_sat`/`check_sat_assuming`.
    solve_interrupt: Option<Arc<AtomicBool>>,
    /// Test hook: force the non-BV EUF congruence pass to bail immediately
    /// (as if the deadline expired at pair 0), exercising the
    /// SAT-under-partial-axiomatization degrade path deterministically.
    #[cfg(test)]
    pub(crate) test_force_non_bv_congruence_bail: bool,
    /// Re-entrancy guard for the alternation MBQI validation sub-solve, so its
    /// own (forall ...) over-approximation solve does not recurse into it.
    in_alternation_validation: bool,
    /// Re-entrancy guard for the closed-universal-validity precheck, so its
    /// ground negation sub-solve does not recurse back into the precheck.
    pub(crate) in_closed_universal_precheck: bool,
    /// Re-entrancy guard for the quantified-assertion model gate
    /// (#quantified-model-gate): its nested isolated confirm/refute solves
    /// must never recurse back into the gate (or any other emit-funnel gate).
    pub(crate) in_quantified_model_gate: bool,
    /// Typed handoff from a definitive quantified-model check to the
    /// immediately following compositional independent gate.
    ///
    /// Diagnostic statistics are never authority. This capability is bound
    /// to the exact public-query epoch, frontend source/scope stamp, ordered
    /// active roots, and sealed installed-model identity. Every solve/result
    /// invalidation revokes it with the other quantified SAT grants.
    pub(in crate::executor) quantified_model_confirmation:
        Option<model::QuantifiedModelConfirmation>,
    /// DT-MBQI-Sat certificate state (M4): set whenever
    /// `try_dt_model_sat_certificate` grants this check-sat's `Sat`, whether at
    /// the bounded pre-solve re-sequencing probe or either post-solve result-
    /// mapping arm. The certificate is the sole grant authority for the
    /// snapshot's universals (it re-verified every one against the completed
    /// model M'), so the quantified-model gate — whose budgeted nested re-checks
    /// run against the candidate M that did not witness those universals — must
    /// DEFER to the certificate rather than revalidate that intentionally
    /// incomplete candidate. Ground assertions still pass through the strict
    /// pre-skip oracle before this flag matters. Cleared at check-sat entry.
    pub(crate) dt_cert_grant_active: bool,
    /// Exact query/source/root scope paired with
    /// [`Self::dt_cert_grant_active`]. The Boolean is only routing state; both
    /// SAT gates require this opaque grant to be current.
    dt_cert_query_grant: Option<QuantifiedSatAuthorityGrant>,
    /// Sibling of [`Self::dt_cert_grant_active`] for the FINITE-TABLE SAT
    /// certificate, set on the route where CEGQI has already classified the
    /// ground remainder `Sat`.
    ///
    /// On that route `final_result` is `Sat`, so the phase-2.5 / phase-3.5 grant
    /// arms — which fire only on `Unknown` and are what record certificate
    /// authority — never run. The certificate is instead reached by the
    /// restoration-branch recompute, which computed `explicit_certificate`
    /// purely to SUPPRESS a downgrade and recorded nothing. The public emission
    /// funnel then re-checked the model against universals the certificate had
    /// already verified, could not ground-evaluate a `forall` over an infinite
    /// domain, and failed closed — turning a certified `Sat` into `unknown`.
    ///
    /// Set ONLY after `try_finite_table_sat_certificate` succeeds, which
    /// re-verifies EVERY snapshot assertion under an explicitly constructed
    /// interpretation. That is the precondition the gate documents for these
    /// markers: evidence composition, never a skip — the ground siblings are
    /// still checked independently. Cleared at check-sat entry.
    pub(crate) finite_table_cert_grant_active: bool,
    /// Sibling of [`Self::finite_table_cert_grant_active`] for the
    /// CONSTANT-INTERPRETATION SAT certificate
    /// ([`Executor::try_const_interp_sat_certificate`]).
    ///
    /// Set on EVERY route that grants with that certificate — the phase-2.5 /
    /// phase-3.5 arms (where `final_result` was a quantifier-class `Unknown`)
    /// and the restoration-branch recompute (where CEGQI had already
    /// classified the ground remainder `Sat`). Both are needed: the phase arms
    /// alone leave the CEGQI route uncovered, and the restoration arm alone
    /// never fires when the result was `Unknown`.
    ///
    /// The marker's precondition is the same one the finite-table flag
    /// documents — an authority that re-verified EVERY snapshot assertion
    /// under an explicitly constructed interpretation. This certificate meets
    /// it in the strongest available form: each assertion was discharged by an
    /// independent ground-solver `Unsat` on the negated, interpretation-
    /// substituted, freshly-Skolemized body. Without the marker the public
    /// emission funnel re-checks the candidate model against universals the
    /// certificate has already certified, cannot ground-evaluate a `forall`
    /// over an infinite domain, and fails closed — publishing a certified
    /// `Sat` as `unknown`. Cleared at check-sat entry.
    pub(crate) const_interp_cert_grant_active: bool,
    /// Sibling certificate marker for
    /// [`Executor::mbqi_sat_validated_left_inverse_axioms`]. That routine
    /// certifies every restored universal against an explicitly materialized
    /// interpretation, while the retained solver model may carry only the
    /// ground core. The public SAT funnel uses this marker to compose that
    /// quantified evidence with its independent ground-assertion checks.
    /// Cleared at check-sat entry.
    pub(crate) mbqi_sat_cert_grant_active: bool,
    /// Exact query/source/root scope paired with
    /// [`Self::mbqi_sat_cert_grant_active`].
    mbqi_sat_cert_query_grant: Option<QuantifiedSatAuthorityGrant>,
    /// Linear, query/root/source/model-scoped authority for the CEGQI UF
    /// re-completion theorem. Unlike the legacy Boolean certificate markers,
    /// this value can only be constructed by the sealed per-group verifier and
    /// becomes unusable when the query epoch, authored roots, declaration
    /// identities, source scope, or installed completed-model identity changes.
    /// Cleared at every solve/result invalidation boundary.
    pub(in crate::executor) cegqi_uf_recompletion_grant:
        Option<quantifier_loop::CegqiUfRecompletionGrant>,
    /// A finite-table certificate's outer witness, parked while later
    /// result-mapping probes run. Nested solves may overwrite `last_model` and
    /// its model-owned ground projection; the outer mapper installs this
    /// witness only after all such probes finish and the certificate is still
    /// the final Sat authority.
    finite_table_cert_witness_state: Option<mbqi::FiniteTableWitnessState>,
    /// Exact constant-interpretation witness parked until the public SAT
    /// funnel. Certificate probes and restoration may replace `last_model` or
    /// sidecar entries after the theorem was checked; publication reinstalls
    /// this model/entry pair atomically before consulting the grant marker.
    const_interp_cert_witness_state: Option<mbqi::ConstInterpWitnessState>,
    /// Session-scoped spend/yield account for the finite-model lane
    /// (#witness-check-cost). See `finite_model_mbqi::LaneAccount`.
    pub(in crate::executor) finite_model_lane: finite_model_mbqi::LaneAccount,
    /// Live API deadline cell (#quantifier-determinism). Stop closures poll a
    /// cloned handle, so backstop extension and alternation sub-deadline
    /// windows remain visible; value snapshots use `.get()`.
    solve_deadline: SolveDeadlineCell,
    /// Command deadline untouched by inner-lane halving (#dt-context-derivation).
    /// Certification may spend this outer envelope on a found refutation;
    /// search lanes narrow only `solve_deadline`, never this cell.
    certification_deadline: SolveDeadlineCell,
    /// One-shot marker: the quantified-solve wall-clock backstop extension has
    /// been applied for the current check-sat call (#quantifier-determinism,
    /// see `install_quantifier_deadline_backstop`). Re-armed per call in
    /// `install_timeout_deadline_for_call`; prevents nested quantified
    /// re-entries (alternation validation sub-solves) from compounding the
    /// extension.
    quantifier_deadline_backstop_installed: bool,
    /// Deadline policy for this executor. Public solves use the ordinary
    /// quantified backstop; accepting certification probes select `Exact` so a
    /// caller's absolute deadline can only stop work, never be extended.
    quantifier_deadline_policy: QuantifierDeadlinePolicy,
    /// Whether the caller has OPTED IN to the quantified wall-clock backstop
    /// (#honest-timeout). `false` by default, which is what makes
    /// `set_timeout(d)` an actual bound: without it,
    /// `install_quantifier_deadline_backstop` is a no-op and every stop path
    /// polls the caller's own deadline.
    ///
    /// WHY IT IS STILL HERE. The backstop buys DETERMINISM, and that is a real
    /// capability, not a bug: the quantifier pipeline's termination is governed
    /// by deterministic instantiation budgets (E-matching round/instance caps,
    /// interleaved/CEGQI/MBQI round caps), so a proof whose instantiation chain
    /// converges just inside the budget on an idle machine used to be cut short
    /// on a loaded one and the verdict flipped Verified <-> Unknown with CPU
    /// load. A caller that wants that guarantee — a verification driver
    /// replaying a fixed obligation set, where a load-dependent verdict is
    /// worse than a long one — turns it on with
    /// `set_quantifier_deadline_backstop(true)` and accepts a wall of up to 4x
    /// the remaining budget (capped at +3 min).
    ///
    /// WHY IT IS OFF BY DEFAULT. It was silently ON for every caller, so a
    /// 60 s `set_timeout` bought a ~240 s wall with nothing in the API saying
    /// so. A timeout whose only documented meaning is "moderately past" cannot
    /// be used to bound a batch, a CI job or an interactive query, and the
    /// caller had no way to decline. Opt-in keeps the capability and makes the
    /// overrun the caller's explicit choice.
    quantifier_deadline_backstop_opt_in: bool,
    /// #read-congruence-quantified-scope (#7956 tseitin regression): `true`
    /// from the moment the current check-sat's quantifier pipeline actually
    /// instantiates quantifiers (`process_quantifiers`, past its
    /// no-quantifiers early return) until the next check-sat re-arms it in
    /// `install_timeout_deadline_for_call`. Ground (re-)solve combiners
    /// constructed while it is set disable the store-carrying
    /// read-congruence index-pair obligations — see
    /// `TheoryCombiner::set_read_congruence_pairs_enabled`.
    pub(in crate::executor) quantifier_pipeline_engaged: bool,
    /// TermStore length at the last `(reset-assertions)`, i.e. the boundary
    /// between the assertion epoch now in flight and everything before it.
    ///
    /// The store is append-only and lives for the whole `Solver`, so every
    /// Skolem an EARLIER epoch minted — a quantifier instantiation, an
    /// `__ay_ext_diff` extensionality witness, a `qmg!` model-gate witness —
    /// is still there afterwards, as a `Var` no current assertion reaches.
    /// This mark is what separates "left over from a previous epoch" from
    /// "belongs to this one", and it is what
    /// [`Executor::array_axiom_dead_skolems`] is computed against.
    ///
    /// The RESET is the right boundary, not the check-sat: nested probe and
    /// retry solves re-enter the check-sat entry points with a much longer
    /// store, and arming there would have re-classified the OUTER query's own
    /// live terms as leftovers (measured: `free_dt_array_alias_consistent_
    /// reads_is_sat` degraded `sat` -> `unknown`). `0` — the value for a
    /// session that has never reset, which is every single-query problem —
    /// means "no leftovers", i.e. exactly the unfiltered behaviour.
    pub(in crate::executor) assertion_epoch_terms_len: usize,
    /// Broad solver phase currently executing, used to attribute timeouts and
    /// other Unknown results to a responsible phase.
    active_solve_phase: Option<String>,
    /// Narrow cost center currently executing inside `active_solve_phase`.
    active_solve_cost_center: Option<String>,
    /// Relative timeout applied to subsequent executor solve commands.
    timeout: Option<Duration>,
    /// Deterministic conflict budget backing the SMT-LIB `:rlimit` option
    /// (#8749). Each SAT solve in a check-sat is bounded by this many
    /// conflicts; with the theory split caps this guarantees machine-
    /// independent termination on otherwise-diverging fragments (e.g. NIA).
    /// `None` means unbounded. See [`Self::set_resource_limit`].
    pub(crate) resource_limit: Option<u64>,
    /// Explicit per-SAT-solve DECISION budget (#ground-determinism), the
    /// decision-count companion of `resource_limit`. `None` means "use the
    /// default ground allowance when the ground budget is enabled". See
    /// [`Self::set_decision_limit`].
    pub(crate) decision_limit: Option<u64>,
    /// Whether the DEFAULT deterministic ground-phase budget is in force
    /// (#ground-determinism). When true (the default) and no explicit
    /// `:rlimit` is set, the pipeline SAT solves that carry `:rlimit` wiring
    /// (incremental x2, lazy split, eager split, assume split, DPLL(T)
    /// assumption solving) are armed with the generous built-in conflict +
    /// decision allowances ([`Self::DEFAULT_GROUND_CONFLICT_ALLOWANCE`] /
    /// [`Self::DEFAULT_GROUND_DECISION_ALLOWANCE`]), so ground-phase
    /// CDCL work terminates on a machine-independent COUNT rather than the
    /// load-sensitive wall clock. (The eager-PERSISTENT arm keeps its own
    /// per-iteration wall budget system (#8256), and the BV/FP bit-blast
    /// arms keep their caller-side tight-watchdog profile — both documented
    /// residuals, unchanged by this mechanism.) `(set-option :rlimit 0)` or
    /// [`set_ground_budget_enabled(false)`](Self::set_ground_budget_enabled)
    /// (or the `AY_NO_GROUND_BUDGET` env knob) restores the pre-budget
    /// wall-clock-only behavior. See
    /// `crate::pipeline_fns::effective_conflict_allowance`.
    pub(crate) ground_budget_enabled: bool,
    /// Process-RSS ceiling (bytes) backing the SMT-LIB `:max-memory` option.
    /// When a solve crosses this bound the active check-sat returns
    /// `Unknown(MemoryLimit)`. `None` means unbounded. Enforcement mirrors the
    /// `:timeout` deadline — checked at theory-loop boundaries via
    /// [`Self::should_abort_theory_loop`]. See [`Self::set_memory_limit`].
    pub(crate) memory_limit: Option<usize>,
    /// Re-entry guard for pivot-bounded word equation enumeration (#3826).
    /// When > 0, the pivot enumeration pre-pass in solve_strings_lia is
    /// skipped to prevent infinite recursion.
    pivot_enum_depth: u8,
    /// Re-entry guard for SAT-preserving symbolic mod/div OR branch rescue.
    /// The rescue can call back into AUFLIA after strengthening a disjunction;
    /// nested calls must fail closed instead of repeatedly selecting the same
    /// branch.
    mod_div_or_branch_rescue_depth: u8,
    /// #6812 sound relaxation: re-entry guard / mode flag for verify-before-accept.
    /// When > 0, the UF+LIA eager arm is running as the FRESH re-derivation of a
    /// post-split UNSAT core (no stale learned clauses, isolated incremental
    /// state). In that mode it accepts a post-split UNSAT directly (tautological
    /// split clauses, §2 of the design) instead of recursing into another verify
    /// pass — which both terminates the recursion and lets the fresh solve
    /// actually close the genuine UNSAT.
    pub(in crate::executor) post_split_verify_depth: u8,
    /// Re-entrancy guard for the QF_LRA model-validation blocking guard's
    /// complete SAT-recovery re-solve (split-loop false-UNSAT root fix).
    ///
    /// When the model-validation-failure blocking guard finds the blocked
    /// Boolean assignment is NOT provably theory-UNSAT, it re-solves the
    /// assignment's atom conjunction with the COMPLETE standalone split-loop to
    /// recover a sound SAT verdict + valid witness. That nested solve runs the
    /// SAME eager-persistent arm whose guard invoked it; this flag tells the
    /// nested arm to take the conservative fail-closed path at its own guard
    /// (no further recovery recursion), guaranteeing termination.
    pub(in crate::executor) lra_in_assignment_recheck: bool,
    /// Re-entrancy guard for final model completion's ground-constrained
    /// arithmetic gap re-solve. The nested executor is only an untrusted
    /// candidate generator; the outer validation pipeline remains the arbiter.
    pub(in crate::executor) final_lia_resolve_disabled: bool,
    /// Result from the last proof validation run (#4393).
    /// Populated by `build_unsat_proof` after running `check_proof_partial`.
    proof_check_result: Option<PartialProofCheck>,
    /// Whether the ordinary internal UNSAT proof pass reported zero checker
    /// errors (set in `record_proof_check_stats`: `failures == 0`). This is a
    /// prerequisite for `--self-check`; its final UNSAT gate separately reruns
    /// the strict semantic checker with the problem's datatype registries and
    /// verifies that every reachable assumption belongs to the problem scope.
    proof_check_ok: bool,
    /// SAT-level unknown reason pending mapping to DPLL-level (#4622).
    /// Set by `collect_sat_stats!` macro, consumed by `solve_and_store_model`.
    pending_sat_unknown_reason: Option<SatUnknownReason>,
    /// Verification level controlling runtime correctness checks (#4444).
    ///
    /// Replaces the scattered `debug_*_enabled()` env-var checks with a
    /// single structured configuration point. Consumers set this to control
    /// what verification overhead they accept.
    verification_level: VerificationLevel,
    /// Fail-closed self-check mode (`--self-check`). When true, the SAT model
    /// must be independently confirmed assertion-by-assertion (every leaf
    /// evaluates to `Bool(true)`) or the result degrades to a sound `Unknown`;
    /// an UNSAT must carry a checked refutation proof or it likewise degrades.
    /// The principle is soundness-by-self-certification: AY never emits a
    /// `sat`/`unsat` it cannot itself verify. Off by default (completeness-first).
    self_check: bool,
    /// Competition mode (opt-in via `--competition` / `AY_COMPETITION=1`,
    /// #proof-capability B1): shed the internal proof cycle when the session
    /// has no explicit proof demand. `begin_public_solve` then leaves the
    /// proof tracker DISABLED, so clause tracing, LRAT bookkeeping,
    /// theory-lemma recording, and Alethe reconstruction are never armed.
    ///
    /// PRECEDENCE, not conflict: any explicit proof demand — `--proof` /
    /// `set_produce_proofs(true)`, in-script `(set-option :produce-proofs
    /// true)`, `(set-option :check-proofs-strict true)`, or self-check mode —
    /// defeats shedding and restores the certified lanes
    /// (`competition_shedding_active`). Publication stays fail-closed: with
    /// tracking shed, an UNSAT that cannot mint a certificate degrades to
    /// `unknown` exactly as today (the raw-admission lane is a later,
    /// separately audited milestone, B3). Off by default (certified-first).
    competition_mode: bool,
    /// Set by the last `check_sat` when it produced an UNSAT for a top-level
    /// pure-QF_BV query under `--self-check` AND emitted the eager bit-blast CNF
    /// plus its single-invocation DRAT to the self-cert temp files. The inner
    /// Alethe gate lets this candidate reach the outer `check_sat` boundary,
    /// which finalizes the CNF and runs AY's native DRAT checker before any API
    /// caller can observe `Unsat`. Fail-closed: reset to false when emission or
    /// verification fails.
    last_bv_drat_self_cert: bool,
    /// When true, the datatype-carrying-array SAT soundness gate
    /// (`problem_has_datatype_carrying_array` in `finalize_sat_model_validation`
    /// and in `solve_with_dt_axioms`) is BYPASSED because the store-value
    /// constructor-injectivity bridge (`dt_store_value_injectivity_axioms`) has
    /// provably modeled every datatype-carrying-array injectivity hazard in the
    /// problem — so a returned SAT model already respects constructor
    /// injectivity/disjointness and is sound. Computed from the ORIGINAL
    /// assertions at the start of `solve_with_dt_axioms`
    /// (`dt_array_injectivity_fully_modeled`); default `false` (fail-closed:
    /// degrade SAT to Unknown) for every other route. See
    /// `#dt-array-store-value-injectivity`.
    dt_array_injectivity_gate_bypass: bool,
    /// Set true immediately before `finalize_sat_model_validation` returns the
    /// datatype-carrying-array degrade Unknown (`problem_has_datatype_carrying_array
    /// && !dt_array_injectivity_gate_bypass`). Read by the DT iterative-deepening
    /// loop (`solve_with_dt_axioms`) as a perf backstop: because BOTH degrade
    /// inputs are DEPTH-INVARIANT (`problem_has_datatype_carrying_array` is
    /// monotone-true; the bypass is computed once from the original assertions),
    /// re-solving at a deeper selector frontier cannot change this Unknown, so the
    /// loop returns it immediately instead of spinning up to the deepening ceiling
    /// re-bit-blasting the whole instance. Strictly verdict-preserving: it only
    /// converts an eventual/timeout Unknown into a prompt Unknown, and a definitive
    /// Sat/Unsat is returned before the flag is ever consulted. Cleared at each
    /// `check_sat` / `check_sat_assuming` entry. (#dt-array-degrade-backstop)
    last_degrade_was_datatype_array: bool,
    /// Snapshot of the DT-route assertions taken IMMEDIATELY BEFORE
    /// `solve_with_dt_axioms` applies `lift_arithmetic_ite_all` (#5082). The
    /// lift Shannon-expands an unconditional constructor equality
    /// `(= x (C .. (ite g A B) ..))` into a guarded `(ite g (= x C_A) (= x C_B))`,
    /// which `collect_unconditional_equalities` (no `Ite` arm) then misses — so
    /// the acyclicity guard-forcing pass loses the entailed cycle-breaking unit
    /// (regression from the ite-lift, fuzz881). The acyclicity passes additionally
    /// mine this PRE-lift snapshot: every unit they derive is an entailed
    /// datatype consequence of the original assertions, and lifting is
    /// semantics-preserving, so pre-lift-derived units stay sound post-lift.
    /// Empty on non-DT routes.
    dt_pre_lift_assertions: Vec<TermId>,
    /// Lazy DT lane registry (`DESIGN_lazy_dt.md` stage D2): datatype
    /// registry with all-nullary markers plus the executor-materialized
    /// domain-closure split bases `(t, [(= t C1), .., (= t Ck)])`. `Some`
    /// ONLY while `try_solve_dt_lazy` runs — the array_euf pipeline factory
    /// consumes it to enable the combiner's D2 splitting-on-demand pass (and
    /// with it the search-time D0 conflict check). `None` on every other
    /// route, so the eager lanes keep their exact pre-D2 behavior.
    dt_lazy_splits: Option<(Vec<(String, Vec<String>, bool)>, Vec<(TermId, Vec<TermId>)>)>,
    /// When true, `finalize_sat_model_validation` skips validation and returns
    /// `Ok(SolveResult::Sat)` immediately. This is set during `check_sat_internal`
    /// when quantifier E-matching modifies the assertion set: the theory solver's
    /// model validation would see ground instances instead of the original quantified
    /// assertions, causing false violations. Validation is deferred to after the
    /// original assertions are restored (#2862).
    defer_model_validation: bool,
    /// Set by `try_bv_mbqi_refinement` when EVERY unhandled BV `forall` was
    /// discharged over its entire domain: either symbolically by proving
    /// `G AND NOT body[skolem]` UNSAT, or by exhaustively enumerating every
    /// value of a small BV carrier.
    ///
    /// This is the certificate that separates a PROOF from a SAMPLE.
    /// `map_quantifier_result` fails a BV-MBQI Sat closed by default, and
    /// rightly so: "no counterexample among the candidates I tried" is not a
    /// totality proof (the shifted-trigger wrong-sat). Symbolic entailment and
    /// exhaustive enumeration are total, so only those BV-MBQI Sat results may
    /// be emitted.
    ///
    /// Cleared on entry to `try_mbqi_refinement` and whenever any quantifier is
    /// discharged by a weaker route, so it is only ever true for an
    /// all-quantifiers-full-domain pass.
    bv_quantifier_full_domain_proof: bool,
    /// Linear producer evidence paired with
    /// [`Self::bv_quantifier_full_domain_proof`] until the result mapper consumes
    /// it at the query-authority boundary. A raw routing bit cannot populate
    /// this slot.
    bv_quantifier_full_domain_pending_evidence: Option<bv_mbqi::CheckedBvFullDomainSatAuthority>,
    /// Exact query/source/root scope paired with
    /// [`Self::bv_quantifier_full_domain_proof`].
    bv_quantifier_full_domain_query_grant: Option<QuantifiedSatAuthorityGrant>,
    /// When true, `solve_and_store_model_full` stores the SAT/theory model but
    /// skips SAT-preserving counterexample minimization until the caller
    /// restores the original assertion set. Used by standalone preprocessing
    /// lanes whose temporary reduced assertions are not the user-facing formula.
    defer_counterexample_minimization: bool,
    /// True when the last SAT witness passed ordinary final model validation or
    /// the independently checked total-projection evidence lane. Reset to
    /// `false` at the start of each `check_sat`. Used by the API layer to report
    /// admitted model evidence accurately (#5903).
    last_model_validated: bool,
    /// Unforgeable witness that the last emitted `Sat` passed either the
    /// ordinary validation funnel or the checked quantified-projection funnel.
    /// Minted only inside those private chokepoints; the API boundary consumes
    /// it via `take_sat_certificate` to build a public `Sat`
    /// `VerifiedSolveResult`, so no `Sat` can escape without complete evidence
    /// (#sat-chokepoint).
    last_sat_certificate: Option<SatCertificate>,
    /// One-shot witness that the last provisional UNSAT passed one complete
    /// exact-query certification lane. The sealed kind preserves literal strict
    /// proof acceptance, independently checked refutation/trust discharge, and
    /// the narrow exact semantic theorem as distinct claims.
    last_unsat_certificate: Option<UnsatCertificate>,
    /// Move-only source authentication produced by the final nested-array
    /// quarantine and consumed by the mandatory UNSAT mint.
    ///
    /// The proof checker binds its evidence to the complete term-store
    /// snapshot, so this slot is populated only after proof/sidecar building,
    /// named-core rescue, and core minimization have finished all term
    /// interning.  It is never a certificate on its own: final publication
    /// must bind it to a freshly authenticated public-query scope.
    pending_nested_array_bool_bv_unsat: Option<unsat_cert::PendingNestedArrayBoolBvUnsat>,
    /// Certification class consumed by the most recent SMT-LIB command
    /// boundary. This is separate from the one-shot token so later diagnostics
    /// cannot relabel an exact semantic certificate as a strict proof merely
    /// because the admitted result is `Unsat`.
    last_command_unsat_admission: Option<unsat_cert::CommandUnsatAdmission>,
    /// Frozen authored assertion and assumption authority for the active public
    /// decision. Solver-generated preprocessing terms never enter this epoch.
    unsat_query_epoch: Option<unsat_cert::UnsatQueryEpoch>,
    /// Phase 2 CEGAR (#dt-array-cegar): a select-congruence lemma that the model
    /// census / general select-congruence gate found the last SAT model to
    /// VIOLATE — `(=> (and (= A B) (= i j)) (= (select A i) (select B j)))` for
    /// the offending read pair. It is an array-theory TAUTOLOGY, so adding it to
    /// the assertions is verdict-preserving (UNSAT stays UNSAT, a true SAT stays
    /// SAT); the deepening loop re-solves with it installed to prune the spurious
    /// model and reach a certified SAT (or expose the genuine UNSAT). `None` when
    /// the last degrade was not a fixable congruence violation.
    cegar_pending_lemma: Option<TermId>,
    /// Remaining CEGAR refinement rounds, decremented per lemma installed. Bounds
    /// the refine-and-re-solve loop so it always terminates — to a certified
    /// verdict, or to a sound `unknown` when the budget is spent.
    cegar_rounds_remaining: u32,
    /// Congruence lemmas already installed this `check_sat`, so an ineffective
    /// lemma is never re-added (guarantees per-round progress / termination).
    cegar_emitted_lemmas: HashSet<TermId>,
    /// Validation stats from the last completed SAT validation attempt.
    /// Preserved for both validated SAT and SAT->Unknown degradation so the
    /// API layer can report why validation failed (#5777).
    pub(crate) last_validation_stats: Option<model::ValidationStats>,
    /// Restored original assertions that the current theory solve explicitly
    /// proved through a preprocessed/encoded assertion.
    ///
    /// This is narrower than treating every unmapped restored assertion as
    /// solver-covered: the producing theory path must record the exact original
    /// assertion before model validation may delegate it.
    model_validation_delegated_assertions: HashSet<TermId>,
    /// Solver-generated DT axiom terms currently appended to `ctx.assertions`
    /// by the DT/DT+X solve routes (selector/tester/exhaustiveness/congruence/
    /// acyclicity passes). Every one is a datatype-theory TAUTOLOGY or an
    /// entailed consequence of the user assertions, so the in-loop validation's
    /// `#dt-embedded-cycle` compound fail-closed guard must not fire on them —
    /// accepting an entailed axiom can never validate a wrong model of the USER
    /// formula, while fail-closing on one (e.g. a deep `(or (= v (succ (pred
    /// v))) (not (is-succ v)))` whose selector leaf is legitimately free)
    /// spuriously degrades genuine deep-recursion SATs to Unknown. Set at the
    /// axiom-append sites, cleared when the axioms are truncated back off.
    dt_solver_added_axiom_terms: HashSet<TermId>,
    /// When true, `finalize_sat_model_validation` skips full evaluation and
    /// accepts the SAT model after boolean skeleton verification only.
    /// Set ONLY by `incremental_scope.rs` for inner solve suppression.
    /// All theory solvers (Seq, FP, Strings) now run full model validation;
    /// trivially-SAT paths use `last_model_validated = true` instead (#8456).
    /// Reset at start of each `check_sat`.
    skip_model_eval: bool,
    /// Read-pin repair already ran for this check-sat
    /// (#qf-auflia-read-pin-repair). The repair is invoked from three gate
    /// sites; re-running it after intervening completion passes mixes repair
    /// ROUNDS in the final model (round-1 store entries beside later-round
    /// re-pinned var values), which the independent gate then correctly
    /// rejects. Single-shot per check-sat keeps the repaired model coherent.
    pub(crate) read_pin_repair_done: bool,
    /// Exact NRA witnesses and the one-shot model-print refinement guard.
    nra_algebraic_model: nra_model_state::NraAlgebraicModel,
    /// DT theory e-graph model exported at `Sat` by the interactive
    /// `DtSolver` lane (#mv-dt-single-source): union-find classes,
    /// constructor/tester commitments, asserted disequalities. The SINGLE
    /// SOURCE for every printed datatype value — `(get-model)`,
    /// `(get-value)` and the total selector definitions all derive their
    /// datatype values from the one per-class assignment built from this
    /// export (see `model/dt_egraph_values.rs`), so they cannot diverge the
    /// way the legacy per-term re-derivation did (M3 root cause / M4 F1).
    /// `None` on lanes without an interactive `DtSolver` (combined DT+X
    /// routes) — printing falls back to the legacy strategies there.
    /// Reset at the start of each `check_sat`/`check_sat_assuming` and on
    /// every stored solve verdict; set only when the accepted `Sat` came
    /// from the DT lane.
    dt_theory_model: Option<ay_dt::DtModel>,
    /// Set by `finalize_sat_model_validation` when it degraded a Sat to
    /// Unknown on a DATATYPE ground-assertion incompleteness gap (the
    /// #dt-completion-gate-handoff case) while the DT lane's e-graph export
    /// was still stashed aside (`solve_and_store_model_full` deliberately
    /// hides it from the in-loop validation gates). The storing caller
    /// (`solve_and_store_model_with_theories`) consumes it to attach the
    /// export and re-run finalization ONCE, so the independent fail-closed
    /// gate can re-evaluate the witness against the single-source per-class
    /// values — the same evidence the emit-time gate reads
    /// (#dt-egraph-validation-retry, mv-rerun-20260718 regression). Cleared
    /// with `clear_dt_theory_model` on every stored verdict.
    dt_validation_wants_egraph: bool,
    /// Lazily-built per-class datatype value assignment derived from
    /// `dt_theory_model` on first print/get-value use (interior-mutable
    /// memo; cleared whenever `dt_theory_model` changes). `Arc` so callers
    /// can hold the assignment without borrowing the executor.
    dt_egraph_assignment: RefCell<Option<Arc<model::DtEgraphAssignment>>>,
    /// Reentrancy latch for the assignment builder: while building, nested
    /// evaluation must not consult the (incomplete) assignment.
    dt_egraph_building: Cell<bool>,
    /// Exact-snapshot-keyed index for array definitional-equality lookups
    /// (`array_variable_definition*` / `unique_array_constructor_definition_
    /// excluding`): maps each side TermId of every asserted binary `=` to the
    /// equality assertions mentioning it, in assertion order. Rebuilt whenever
    /// the (assertions, assumptions) snapshot differs BYTE-EXACTLY from the
    /// cached one — never trusted across any change, so it can never serve a
    /// stale definition (model validation is a soundness gate). Motivation:
    /// the previous per-lookup linear scan made model evaluation
    /// O(selects × assertions); an n-ary `distinct` over N selects expands to
    /// ~N²/2 assertions, so validation cost exploded to tens of seconds by
    /// N≈400 on instances whose solve took 0.1s.
    array_def_index: RefCell<Option<model::ArrayDefIndexCache>>,
    /// Exact-snapshot structural index of reserved integer div/mod witnesses.
    ///
    /// Zero-divisor evaluation remains keyed by independently evaluated
    /// operand VALUES; this cache removes only the repeated whole-TermStore
    /// discovery scan. Its opaque store stamp forces a rebuild after append,
    /// rollback, clone, or wholesale context replacement.
    div_witness_index_cache: model::DivWitnessIndexCache,
    /// Reverse index `array term -> select(array, _) terms`, extended lazily
    /// over the APPEND-ONLY term store: `(scanned_prefix_len, map)`. Existing
    /// `TermId`s are immutable, so extending the scan over `[scanned, len)` is
    /// exact by construction — no snapshot compares needed. The one hazard is
    /// wholesale `ctx` replacement (`reset()`), which clears this index
    /// explicitly; a shrink of `terms.len()` also forces a from-scratch
    /// rebuild as belt-and-braces. Motivation: `array_witness_base_interp`
    /// scanned the WHOLE term store per array to find its constrained reads —
    /// O(arrays × terms) during model-output completion.
    #[allow(clippy::type_complexity)]
    select_by_array_index: RefCell<(usize, ay_core::kani_compat::DetHashMap<TermId, Vec<TermId>>)>,
    /// Cached ground-term reachability closure of `(assertions, assumptions)`
    /// behind `term_is_required_by_last_query`: `(assertions snapshot,
    /// assumptions snapshot, reachable set)`. Validated by BYTE-EXACT snapshot
    /// compare on every query (cheap: one id-vector compare vs the full-forest
    /// DFS it replaces, which previously ran PER CANDIDATE READ during array
    /// completion — O(reads × forest) with fresh hash-set churn each time).
    #[allow(clippy::type_complexity)]
    required_terms_index: RefCell<
        Option<(
            Vec<TermId>,
            Option<Vec<TermId>>,
            ay_core::kani_compat::DetHashSet<TermId>,
        )>,
    >,
    /// Variable substitutions (`eliminated var -> replacement RHS`) recorded
    /// by preprocessing passes during the current solve call.
    ///
    /// `VariableSubstitution` eliminates variables bound by definitional
    /// equalities (e.g. `(= v9 (or v3 (<= v8 20)))` substitutes
    /// `v9 -> RHS`), so the SAT/theory models carry no entry for them.
    /// `complete_model_for_validation` (model/completion.rs) replays these
    /// definitions at finalize time to make the model total over the
    /// original free variables before full model validation runs.
    /// Cleared at the start of each `check_sat`/`check_sat_assuming`.
    recorded_var_substitutions: HashMap<TermId, TermId>,
    /// True when the ORIGINAL problem for the current solve contained a
    /// quantifier (computed before `process_quantifiers` strips/instantiates
    /// them). Read by the AUFLIA preprocessor to gate the top-level
    /// array-variable alias collapse (`substitute_array_var_aliases`): that
    /// optimization targets quantifier-free `QF_AUFLIA` and is NOT
    /// equisatisfiable once quantifier instantiation/Skolemization has
    /// introduced ground terms tied to an eliminated array variable (it has
    /// produced spurious UNSAT, e.g. `forall x. select c x = f x` with
    /// `(= a c)`). Set fresh each solve in `check_sat`.
    original_problem_had_quantifiers: bool,
    /// #quantified-trace-arming: the internal proof trace is armed for the
    /// RETRY pass of the solve currently in flight, even though competition
    /// shedding is otherwise active.
    ///
    /// Cleared by `begin_public_solve`, so every public decision STARTS shed
    /// and its first pass is byte-identical to the pre-campaign behaviour. Set
    /// only by [`Executor::arm_quantified_trace_for_retry`], from the
    /// `Unknown` fallback in `quantified_trace_arming_unknown_retry`, because
    /// on a quantified problem the trace is the publication mechanism for an
    /// instantiation-driven refutation rather than a user-facing artifact:
    /// `disambiguate_cegqi_unsat` publishes `unsat` exactly when the recorded
    /// `forall_inst` derivations strict-check against the immutable authored
    /// problem, and with no trace that route cannot run.
    ///
    /// The ADMISSION lane — [`Executor::competition_shedding_active`] and the
    /// `CompetitionRaw` branch in `certify_unsat_presentation` — is untouched
    /// in both passes.
    quantified_query_defeats_shedding: bool,
    /// When true, SAT was established by solving a syntactically stronger
    /// symbolic mod/div OR branch. The original assertion may still contain
    /// unsupported symbolic division terms that model evaluation cannot replay,
    /// but satisfiability follows from the stronger branch after the strict
    /// definitive-false gate has ruled out known model violations.
    sat_validated_by_mod_div_or_branch: bool,
    /// When true, the current UNSAT was derived by the trust-free nested-array
    /// store-flat read-over-write reduction (`try_ufnia_store_flat_row_refutation`):
    /// each single-definition `var = store(…)` was inlined (equisatisfiable) and
    /// exact `select(store(a,i,v),i)=v` rewriting folded EVERY array term away,
    /// leaving a pure-arithmetic residue the sound NIA solver refuted. Such a
    /// refutation uses NO array-theory combination reasoning, so it is
    /// authoritative and is exempt from `quarantine_unverified_nested_array_unsat`
    /// (which fail-closes the UNVERIFIED lazy array+arith combination, a distinct
    /// path). Set only on that exact reduction; reset at each check-sat entry.
    nested_array_row_reduction_unsat: bool,
    /// When true, `unfold_ho_seq_ops` rewrote away every higher-order sequence
    /// combinator and the LIVE assertions it left behind contain no nested
    /// array, so the solver is never handed the array structure
    /// `quarantine_unverified_nested_array_unsat` guards. Unfolding is an
    /// equivalence (a function-as-array application IS `select`), so refuting
    /// what remains refutes the original: such an UNSAT is authoritative and
    /// exempt from that quarantine. Set only by that pass, consumed once at the
    /// quarantine boundary, and reset at each check-sat entry.
    ho_seq_unfold_array_free_unsat: bool,
    /// Re-entrancy latch for the nested-array-free entailed-residue rescue
    /// (`nested_array_free_residue_unsat`, #nested-array-residue-rescue). That
    /// rescue re-solves a filtered subset of the hard assertions through the
    /// ordinary `check_sat_guarded` pipeline, which funnels back through the
    /// same quarantine boundary that launched it. The latch makes the attempt
    /// STRICTLY one-shot per public check-sat: no nesting, no retry loop, so a
    /// hard instance cannot multiply the probe budget.
    in_nested_array_residue_probe: bool,
    /// How many nested-array residue probes have FAILED this session. Bounds
    /// the aggregate cost across many check-sats without ever limiting
    /// successful conversions; see `RESIDUE_MAX_FAILURES`.
    residue_probe_failures: u32,
    /// When true, `has_negated_string_equivalence_tautology` is bypassed.
    /// Set during incremental SLIA pipeline where `self.ctx.assertions` is
    /// temporarily replaced with preprocessed assertions that may falsely
    /// trigger the tautology guard (#6688).
    pub(crate) bypass_string_tautology_guard: bool,
    /// Set by the incremental macro's Unknown→Sat path when the theory
    /// returned Unknown but the model was accepted (#6688).  Used by the
    /// deferred validation in `solve_strings_lia_preprocessed` to decide
    /// whether model validation is needed.
    pub(crate) slia_accepted_unknown: bool,
    /// W7 (default ON, `--dpll-no-str-w7` kills it): the DEFINING equations
    /// (`(= v rhs)`, entailed, `v` a bare string variable) that the W7 witness
    /// pass is currently searching under.
    ///
    /// `None` everywhere else, including for the whole W4/W5/W6 cascade — the
    /// only readers are `w4_origin`, `w4_window_root`, `w4_mentions` and
    /// `w4_violations`, each of which is byte-identical when this is `None`.
    /// It exists as a field rather than a threaded parameter because those four
    /// helpers are reached from a dozen W4/W5/W6 call sites; W7 sets it for the
    /// duration of its own pass and clears it on every exit path.
    ///
    /// Search state ONLY: it can change which CANDIDATE assignments W7 builds,
    /// never which of them is accepted (every candidate still rides
    /// `finalize_sat_model_validation`).
    pub(crate) w7_defs: Option<HashMap<TermId, TermId>>,
    /// W7's INT defining equations (`(= v e)`, `v` an Int variable). Empty
    /// outside W7's own pass. The `kaluza` witness needs them: its branch pins
    /// `(= PCTEMP_LHS_1_len_0 (str.len idx_0))`, and an Int variable with no
    /// arithmetic model in the trial model evaluates to 0, so the string
    /// witness is scored as violating an atom it actually satisfies.
    pub(crate) w7_int_defs: HashMap<TermId, TermId>,
    /// W4's DETERMINISTIC search budget (`#w4-work-budget`): the value of the
    /// evaluator's node-visit clock (`model::eval_node_visits`) at which the
    /// per-position witness search currently in flight must stop starting new
    /// work. `None` — the value everywhere outside
    /// `try_per_position_witnesses` — means "unbudgeted", so W6's and W7's own
    /// passes are untouched.
    ///
    /// Counted, not timed, ON PURPOSE. W4's hill-climb is an unbounded search
    /// that can eat a whole solve budget and hand back nothing (measured:
    /// `full_str_int/restoreIpAddresses__1800` spent 12.4 s of a 20 s solve in
    /// `w4_repair_var` -> `evaluate_term`, and the refutation it was starving
    /// then takes 0.2 s). A WALL-CLOCK cap would bound that too, but it would
    /// make the search LOAD-DEPENDENT — the same file would build a witness on
    /// an idle box and not on a loaded one, which is precisely the flakiness
    /// this work is meant to remove. Node visits are the evaluator's own unit
    /// of work, so the same file gets the same search on every machine.
    ///
    /// Search state ONLY: exhausting it stops new seeds / repair rounds /
    /// placements from STARTING. No score is ever fabricated, no candidate is
    /// dropped once built, and validation runs unbudgeted — so this can cost a
    /// SAT the search had not yet found, and can never accept one.
    pub(crate) w4_work_deadline: Cell<Option<u64>>,
    /// AUTHORED assertion window of a self-checked check-sat currently in
    /// flight, captured in `check_sat_internal` BEFORE any in-place
    /// preprocessing pass runs (#selfcert-authored).
    ///
    /// The fail-closed `--self-check` SAT gate uses it to certify the model
    /// against the formula the USER actually asserted. The gate's ordinary
    /// denominator is `ctx.assertions` at validation time, which under
    /// `--self-check` (proofs forced on) also carries solver-injected theory
    /// axioms over fresh internal symbols (`__ay_*`).
    /// Those are skipped as `Internal` and counted "unverified", so a QF_AX
    /// model that satisfies every authored assertion was degraded to `unknown`.
    /// See `self_check_authored_model_certified`.
    ///
    /// Model completion and strict proof checking also consume this snapshot in
    /// self-check mode. It therefore must not be repurposed as always-on model
    /// gate state: doing so silently changes default-mode model construction.
    /// Saved/restored around nested `check_sat_internal` re-entries (probe and
    /// retry solves) so an inner solve's narrower window can never be used to
    /// certify the outer verdict. `None` (no self-check snapshot) fails closed.
    self_check_authored_assertions: Option<Vec<TermId>>,
    /// Exact pre-preprocessing assertion roots for the mandatory independent
    /// model gate during the check-sat currently in flight.
    ///
    /// This is deliberately separate from `self_check_authored_assertions`.
    /// The independent gate is mandatory in default mode too, but publishing
    /// its roots must not opt default solving into self-check-only model
    /// completion or proof behavior. Nested probe/retry solves save and restore
    /// this slot so their narrower roots cannot authorize the outer verdict.
    independent_gate_authored_assertions: Option<Vec<TermId>>,
    /// Temporary scope filter for array axiom generation in incremental mode (#6726).
    /// When `Some`, the fixpoint generators skip terms not reachable from current
    /// assertions. The `usize` is the TermStore length at fixpoint entry — terms
    /// created during the fixpoint (idx >= this) always pass the scope check.
    array_axiom_scope: Option<(HashSet<TermId>, usize)>,
    /// This executor solves a DERIVED query window on a SHARED outer term
    /// store (`checked_same_context_unsat_proof`), so whole-store array-axiom
    /// scans must be scoped to window-reachable terms exactly as in
    /// incremental mode (#6726). MEASURED on the #7956 same-context probe:
    /// unscoped, the fixpoint seeds extensionality/store congruence from the
    /// OUTER solve's dead array-equality terms — 247 axioms (218
    /// `store_base_cong`, 12 fresh `__ay_ext_diff` extensionality skolems) and
    /// no ROW clauses versus the identical standalone set's 21 — turning a
    /// sub-second refutation (391 ms standalone) into a >2000 ms timeout AND
    /// replacing the small resolution steps the strict checker accepts with
    /// one fused 8-literal `Generic` array+EUF+LIA conflict it must refuse.
    /// With the scope armed the same probe answers in 30 ms.
    pub(in crate::executor) shared_store_derived_query: bool,
    /// Dead engine-minted witnesses the array-axiom generators must not index.
    ///
    /// Every `Var` in here predates the assertion epoch in flight
    /// (`< assertion_epoch_terms_len`) and is unreachable from its assertions —
    /// the signature of a Skolem an EARLIER query minted and this one cannot name:
    /// a quantifier instantiation, an `__ay_ext_diff` extensionality witness, a
    /// `qmg!` model-gate witness. The TermStore is append-only for the whole
    /// `Solver`, so `(reset-assertions)` does not remove them, and the
    /// whole-store scans in `array_congruence` / `array_row` would otherwise
    /// treat them as live select indices. Recomputed per array fixpoint and
    /// cleared per check alongside `array_axiom_scope`; empty means "no
    /// exclusion", i.e. exactly the unfiltered behaviour.
    array_axiom_dead_skolems: HashSet<TermId>,
    /// #8785: select terms that were first created by eager ROW seeding in the
    /// current preprocessing run. These descendants must not recursively seed
    /// further eager ROW terms, or AUFLIA storecomm reproducers can project a
    /// top-level disequality onto internal store prefixes and produce false UNSAT.
    row_seeded_terms: HashSet<TermId>,
    /// Z3-compatible array-default choice point, shared by every small-finite
    /// array store with the same index sort.  This is deliberately keyed only
    /// by the INDEX sort (not by the array or element sort): Z3 5.0.0's
    /// `theory_array_full::mk_epsilon` uses exactly that sharing discipline.
    /// Entries live for the TermStore lifetime and are cleared only by reset.
    array_default_epsilon_by_sort: HashMap<Sort, TermId>,
    /// Fresh unary `diag` function name paired with each default epsilon.  The
    /// application `diag(i)` witnesses an index at which `store(a,i,v)` and `a`
    /// agree on a non-unit small finite carrier, matching Z3's third finite-
    /// store default axiom.
    array_default_diag_by_sort: HashMap<Sort, String>,
    /// #6820: Cached store-equality tuples from the last fixpoint scan.
    /// Store equalities come from the original formula and don't change
    /// during the fixpoint, so we collect them once and reuse.
    /// Tuple: (eq_term, store_base, store_index, store_value, other_side)
    cached_store_eqs: Vec<(TermId, TermId, TermId, TermId, TermId)>,
    /// #6820: High-water mark of terms scanned for store-eq collection.
    /// Only scan terms above this index on subsequent rounds.
    store_eq_scan_hwm: usize,
    /// #6820: Cached select indices grouped by base array for the current
    /// eager array fixpoint. Reused by both store congruence passes so they
    /// do not rescan the full term store every round.
    cached_select_indices_by_array: HashMap<TermId, Vec<TermId>>,
    /// #6820: High-water mark of terms scanned for select collection.
    /// Only scan terms above this index on subsequent rounds.
    select_index_scan_hwm: usize,
    /// Cached negation map from the last proof-tracking solve, reused for
    /// incremental proof reconstruction (#6590).
    pub(crate) last_negations: Option<HashMap<TermId, TermId>>,
    /// Random seed for SAT solver VSIDS tie-breaking (#6961).
    /// When `Some(seed)`, the seed is applied to every SAT solver instance
    /// before solving. Different seeds produce different search paths.
    random_seed: Option<u64>,
    /// E-matching round limit override (#7893).
    ematching_round_limit: Option<usize>,
    /// When true, SAT solvers created during solving emit periodic progress
    /// lines to stderr (~5s interval). Propagated to DpllT and raw SAT
    /// solver instances.
    progress_enabled: bool,
    /// When `Some`, SAT solvers attach a [`ay_sat::json_observer::JsonProgressObserver`]
    /// that writes JSONL events to the given file path (#8155 subtask 7b).
    progress_json_path: Option<String>,
    /// When true, an additional aggressive minimization pass is run after
    /// check-sat returns SAT. This targets BV variables with 0/1 candidates
    /// beyond the standard minimization pipeline. Exposed via CLI `--minimize-model`.
    aggressive_model_minimize: bool,
    /// When true, NOTHING in this session can consume a model: the host has
    /// proved that no model-reading command and no model-printing flag is in
    /// scope for the whole run. Set only by a host that sees the entire
    /// command list up front (the SMT-LIB FILE lane); the streaming/interactive
    /// and library lanes leave it `false`, which is the demand-assumed default.
    ///
    /// It suppresses COSMETICS ONLY — SAT-preserving counterexample
    /// minimization, whose own module doc calls it "best-effort COSMETICS for
    /// witness quality — the stored model is already valid". Every validation
    /// gate, the model completion those gates read, and the array
    /// select-congruence census run exactly as before: this flag must never be
    /// consulted from `finalize_sat_model_validation` or anything it calls.
    /// See `model_output_is_demanded`.
    model_output_shed: bool,
    /// Test-only trace of the last seed applied to a raw SAT solver instance.
    #[cfg(test)]
    last_applied_sat_random_seed: Cell<Option<u64>>,
    /// Test-only trace of the last seed applied to a DPLL(T) solver instance.
    #[cfg(test)]
    last_applied_dpll_random_seed: Cell<Option<u64>>,
    /// Test-only instrumentation: number of core-guided rounds the OLL MaxSMT
    /// engine completed on the most recent `maxsmt_solve_oll` invocation (i.e.
    /// how many disjoint UNSAT cores it extracted). 0 means the engine fell back
    /// to the binary-search baseline without making core-guided progress. Used by
    /// the MaxSMT tests to assert OLL actually exercised the core path on covered
    /// instances rather than silently always falling back (#phase2-pr1).
    #[cfg(test)]
    last_oll_core_rounds: Cell<u64>,
    /// Test-only release-soundness hook: override the exact baseline's final
    /// model-accounted violated weight once, proving production control flow
    /// rejects a mismatch rather than relying on a debug assertion.
    #[cfg(test)]
    forced_maxsmt_exact_cost: Cell<Option<u64>>,
    /// Test-only OLL core-authentication hook: inject one literal that was not
    /// among the assumptions supplied to the core-producing query.
    #[cfg(test)]
    forced_maxsmt_oll_core_anomaly: Cell<bool>,
    /// Test-only final-witness canary: flip the first Bool soft term after the
    /// SAT-emission funnel has run. The post-emission MaxSMT accounting gate
    /// must revoke the certificate/model instead of publishing stale costs.
    #[cfg(test)]
    forced_maxsmt_post_emit_soft_flip: Cell<bool>,
    /// Test-only final-witness canary: perturb a finite LIA objective after the
    /// SAT-emission funnel. The post-emission objective accounting gate must
    /// revoke the model/certificate/outcomes rather than publish stale optima.
    #[cfg(test)]
    forced_optimization_post_emit_objective_flip: Cell<bool>,
    /// Test-only instrumentation: whether the Phase 5 difference-logic engine
    /// (`try_diff_logic`) decided the most recent `check_sat_internal` call. Lets
    /// the differential gate confirm the diff-logic path actually fired when the
    /// `:ay-diff-logic` option is ON (rather than silently falling through to the
    /// normal solver and coincidentally agreeing).
    #[cfg(test)]
    last_diff_logic_decided: Cell<bool>,
    /// When true, theory lemmas are cached across push/pop scope transitions
    /// and replayed into the SAT solver on subsequent check-sat calls (#8304).
    /// Off by default. Enabled via `Solver::set_lemma_persistence(true)`.
    pub(crate) lemma_persistence: bool,
    /// Theory lemma cache for incremental solving with persistence (#8304).
    /// Only populated when `lemma_persistence` is true. Lemmas are recorded
    /// during NeedLemmas handling and replayed after pop.
    pub(crate) lemma_cache: lemma_cache::LemmaCache,
    /// Objectives found to be unbounded during the last optimization.
    ///
    /// Maps the objective's declaration-order index to its (unbounded) direction
    /// so duplicate objectives over the same term remain distinct. Term-keying
    /// is unsound here: `(maximize x)` and `(minimize x)` would overwrite one
    /// another and both public indices would report the last direction. Cleared
    /// at the start of every `optimize_check_sat`.
    pub(crate) unbounded_objectives: HashMap<usize, ay_frontend::ObjectiveDirection>,
    /// Objectives whose last optimization found a finite but UNATTAINED
    /// optimum `value + eps_coeff·ε` (#opt-epsilon): strict bounds bind the
    /// objective, so the sup/inf is approached but never reached.
    ///
    /// Maps the objective's declaration-order index (same keying rationale as
    /// `unbounded_objectives`) to `(value, eps_coeff)` with `eps_coeff != 0`,
    /// sign-matched to the direction (maximize ⇒ negative, minimize ⇒
    /// positive). Populated only after the delta-simplex outcome passed both
    /// faithfulness audits, the Int guard, the sign guard, AND the two
    /// full-solver twins (finite part unattainable + δ-close point exists).
    /// Consumers: `(get-objectives)` renders the z3 epsilon shapes from it,
    /// `objective_optimum` returns `ObjectiveOutcome::Epsilon`, lex marks the
    /// suffix unavailable instead of committing, box skips the finite record.
    /// Cleared everywhere `unbounded_objectives` is.
    pub(crate) infinitesimal_objectives:
        HashMap<usize, (num_rational::BigRational, num_rational::BigRational)>,
    /// Lexicographic objectives whose exact outcome is unavailable because an
    /// earlier objective was unbounded.
    ///
    /// Once a lexicographic prefix has no attainable optimum, later objectives
    /// cannot be optimized under an equality to that prefix. Z3 represents such
    /// outcomes as intervals; AY has no interval-valued objective result, so it
    /// records their declaration indices here and refuses to fabricate a scalar
    /// optimum. Empty for box/pareto and cleared with every query artefact.
    pub(crate) unavailable_objectives: HashSet<usize>,
    /// Dual (Farkas) optimality certificates from the last optimization
    /// (#lra-opt-cert).
    ///
    /// Maps an objective's declaration-order index to the certificate extracted
    /// from the LRA simplex at its optimum and re-verified against the term DAG
    /// (`OptimalityCertificate::verify`) before being stored, so everything in
    /// this map is checkable. Index-keying preserves distinct certificates for
    /// duplicate same-term objectives with different directions. Rendered by
    /// `(get-objective-certificates)`.
    /// Populated only on the one-shot simplex path whose optimum the full
    /// solver confirmed; cleared at the start of every `optimize_check_sat`.
    pub(crate) objective_certificates: HashMap<usize, ay_lra::OptimalityCertificate>,
    /// Optimal total violated weight from the last `(assert-soft ...)` solve.
    ///
    /// `maxsmt_check_sat()` solves the MaxSMT problem inside a push/pop scope and
    /// pops all temporaries afterward, so there is no surviving objective in
    /// `ctx.objectives()`. The minimized total weight of violated soft
    /// constraints is recorded here so `(get-objectives)` can report the optimal
    /// cost. `Some` only after a SAT MaxSMT solve; cleared whenever the
    /// last-check-result is invalidated.
    last_soft_cost: Option<u64>,
    /// Whether `last_soft_cost` is a PROVEN optimum (false = approximate:
    /// resource-limited search or the weight-incomplete count-first regime).
    last_soft_cost_optimal: bool,
    /// Indices of the soft constraints violated by the captured MaxSMT model.
    ///
    /// Stored from the relaxation indicators while they still exist; evaluating
    /// only the soft terms after cleanup is insufficient for UF/array terms that
    /// the public model evaluator cannot decide. Present only alongside
    /// `last_soft_cost` and cleared with every last-result invalidation.
    last_soft_violations: Option<Vec<usize>>,
    /// Per-objective finite outcomes from the last admitted optimization solve.
    ///
    /// Lex entries are captured during the optimizing query and authenticated
    /// against the final public model. Pareto entries are the authenticated
    /// emitted point. BOX entries are independent optima, for which no single
    /// joint model exists. Storing every finite mode here prevents a later plain
    /// feasibility model from being evaluated and mislabeled as an optimum.
    /// Cleared at every public-query boundary and published only after the
    /// optimization query's SAT witness is admitted.
    pub(crate) finite_objective_values: HashMap<usize, num_rational::BigRational>,
    /// Stateful Pareto-front enumeration state (`(set-option :opt.priority pareto)`).
    ///
    /// Pareto mode is STATEFUL like Z3: each `(check-sat)` emits the NEXT
    /// Pareto-optimal point and `(get-objectives)` reports it; once the front is
    /// exhausted `(check-sat)` returns `unsat`. This persists across consecutive
    /// `(check-sat)` calls and is reset (to `None`) by
    /// [`Self::invalidate_last_check_result`] whenever an assertion / push / pop /
    /// objective change invalidates the enumeration, so a stale front can never
    /// leak into a different problem. `None` means "no enumeration in progress"
    /// (a fresh front will be started on the next pareto `(check-sat)`).
    pub(crate) pareto_state: Option<optimization::ParetoState>,
    /// D1 shadow instrumentation for the on-assert lazy-extensionality campaign.
    /// Records the EAGER `__ay_ext_diff` witnesses emitted this solve so the
    /// finalizer can surface `auflia.ext.*` on `-st`. Measurement only.
    pub(crate) array_ext_shadow: ArrayExtShadow,
    /// Per-public-query array-extensionality witness provenance and pair cache.
    ///
    /// Active entries are reused across internal retries only. Public query
    /// boundaries retire them, preventing a native raw Term handle from
    /// capturing the next query's fresh Skolem.
    pub(crate) array_ext_witness_cache: ArrayExtWitnessCache,
    /// Aggregate finite-array closure budget for the current external query.
    pub(crate) finite_array_expansion: FiniteArrayExpansionLedger,
    /// M-A2 lazy-persistent-combiner SHADOW arm flag
    /// (ARRAY-PROCEDURE-CLOSER-BLUEPRINT §5 A2 / LAZY-M3 §M3.2).
    ///
    /// DEBUG-ONLY, OFF by default, NOT for shipping. When `true`, the lazy
    /// AUFLIA loop additionally drives a SECOND `TheoryCombiner` that is created
    /// ONCE at the start of the loop and WARM-RESET (`soft_reset_warm`) each
    /// round — the create-once + warm-reset persistent lifecycle — IN SHADOW
    /// alongside the authoritative fresh-`TheoryCombiner`-per-round path. Each
    /// engaged round both combiners solve the same synced assignment and the
    /// verdict + lemma/conflict reason-set are compared; the FRESH path stays
    /// authoritative (the persistent path NEVER overrides a verdict, and its
    /// combiner borrows a private term-store snapshot so it cannot perturb any
    /// authoritative state). Divergences are counted (the M-A2 DISAGREE gate).
    ///
    /// There is deliberately no env-var or CLI switch (ay's no-env-vars rule),
    /// and the field + its setter do not exist in release builds, so the default
    /// (fresh-only) behavior is byte-identical.
    #[cfg(debug_assertions)]
    auflia_persistent_shadow: bool,

    /// M5 demand-driven-instantiation differential FORCE-EAGER override
    /// (`demand-driven-instantiation-campaign` memory). Since the M5 flip the
    /// demand lane is the PRODUCTION path for M1-classified self-chaining /
    /// bridge-cycle families (always-on in release AND debug). This debug-only
    /// override forces the OLD eager geometric level-0 minting instead, and exists
    /// solely so the differential harness can run the DUAL-SOLVE comparison
    /// (production-demand vs forced-eager) that guards the flip. No production path
    /// sets it, and it does not exist in release builds — so release is always on
    /// the production-demand path (the eligibility gate is unconditionally `true`
    /// there). Reverting the M5 flip commit restores the shadow-only `demand_shadow`
    /// field this replaced.
    #[cfg(debug_assertions)]
    demand_force_eager: bool,
}

#[cfg(test)]
impl Executor {
    pub(crate) fn incremental_bv_state(&self) -> Option<&IncrementalBvState> {
        self.incr_bv_state.as_ref()
    }
}

include!("executor/incremental_subsystem_macro.rs");

mod command_boundary;
mod lifecycle;
mod test_hooks;

use command_boundary::CommandExecutionBoundary;

#[cfg(test)]
#[path = "executor/root_tests.rs"]
mod root_tests;

/// Whether a quantified solve may relax its nominal deadline into AY's later
/// deterministic-work backstop.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum QuantifierDeadlinePolicy {
    RelaxToBackstop,
    Exact,
}

impl Executor {
    /// Install the logic the way an API constructor does — see
    /// [`ay_frontend::elaborate::Context::set_initial_logic`]. It does NOT
    /// count as a command-stream `(set-logic ...)`, so a script parsed
    /// afterwards may still carry its own, exactly as z3 allows.
    ///
    /// # Errors
    /// Propagates the frontend's logic validation.
    pub fn set_initial_logic(&mut self, logic: &str) -> Result<()> {
        self.ctx.set_initial_logic(logic)?;
        Ok(())
    }

    /// Execute a single command
    ///
    /// Returns output to be printed, if any.
    #[must_use = "command results must be checked — errors indicate parse/solve failures"]
    pub fn execute(&mut self, cmd: &Command) -> Result<Option<String>> {
        // Guard against small embedder/test thread stacks (e.g. libtest's
        // default 2 MiB): the dispatch + frontend-elaboration chain below has
        // large constant frames in low-opt builds, and elaboration recurses
        // on nested terms. Grow once here so every command — including the
        // `set-logic` executed during `api::Solver::try_new` construction —
        // runs with headroom instead of overflowing the caller's thread
        // (2026-07-18 deductive-checks embedder overflow). The check-sat pipeline
        // keeps its own guard (#6783); on an already-grown segment it finds
        // ample remaining stack and does not re-grow.
        stacker::maybe_grow(EXECUTOR_STACK_RED_ZONE, EXECUTOR_STACK_SIZE, || {
            self.execute_stack_guarded(cmd, CommandExecutionBoundary::GenericText)
        })
    }

    /// Execute one command received directly from the audited SMT-LIB user
    /// command stream.
    ///
    /// This differs from [`Self::execute`] only for a plain hard
    /// [`Command::CheckSat`]: the authored entrypoint may mint a linear query
    /// permit before solving. Library adapters, CHC, proof checkers, nested
    /// solves, and [`Self::execute_all`] deliberately retain the generic method
    /// and therefore cannot acquire authority from a command shape alone.
    #[must_use = "command results must be checked — errors indicate parse/solve failures"]
    pub fn execute_authored(&mut self, cmd: &Command) -> Result<Option<String>> {
        stacker::maybe_grow(EXECUTOR_STACK_RED_ZONE, EXECUTOR_STACK_SIZE, || {
            self.execute_stack_guarded(cmd, CommandExecutionBoundary::AuthoredText)
        })
    }

    /// Execute one command whose verdict this caller consumes ONLY as internal
    /// search guidance — the caller's own published claim is certified by
    /// separate obligations it re-derives itself.
    ///
    /// # This does not weaken certification
    ///
    /// The command runs through [`Self::execute`]'s exact routing, boundary,
    /// gates, and publication funnel: an UNSAT returned here carries the same
    /// mandatory certification as one returned by [`Self::execute`], and the
    /// bytes of the verdict are identical. The declaration is consumed by the
    /// certification COST ACCOUNTING (`cert_accounting`) and by nothing else,
    /// so this entrypoint currently buys attribution, not speed.
    ///
    /// It is a typed method rather than a `Command` or a `(set-option ...)`
    /// deliberately: a role reachable from parsed text would let a user's own
    /// `.smt2` file label its top-level `(check-sat)` as internal. That is
    /// irrelevant while the role only counts, and load-bearing the moment any
    /// policy keys on it — so the shape is fixed now, before the policy exists.
    ///
    /// The previous role is restored on return. A panic mid-command leaves the
    /// declaration set, exactly as a panic leaves the sibling publication
    /// deadline installed in `execute_stack_guarded`; both are diagnostic
    /// state on an executor that is already in an unrecoverable condition.
    #[must_use = "command results must be checked — errors indicate parse/solve failures"]
    pub fn execute_internal_lemma(&mut self, cmd: &Command) -> Result<Option<String>> {
        let previous = self
            .query_publication_role
            .replace(QueryPublicationRole::InternalLemma);
        let result = self.execute(cmd);
        self.query_publication_role.set(previous);
        result
    }

    /// [`Self::execute_all`] under one internal-lemma declaration covering the
    /// whole command sequence. See [`Self::execute_internal_lemma`].
    #[must_use = "command results must be checked — errors indicate parse/solve failures"]
    pub fn execute_all_internal_lemma(&mut self, commands: &[Command]) -> Result<Vec<String>> {
        let previous = self
            .query_publication_role
            .replace(QueryPublicationRole::InternalLemma);
        let result = self.execute_all(commands);
        self.query_publication_role.set(previous);
        result
    }

    /// Body of [`Executor::execute`] — only called through the stack guard
    /// above so its (large, low-opt) frame lands on the grown segment.
    fn execute_stack_guarded(
        &mut self,
        cmd: &Command,
        boundary: CommandExecutionBoundary,
    ) -> Result<Option<String>> {
        // `check_sat` installs/restores its own solve-phase deadline internally,
        // but public UNSAT certification runs after that solve returns. Hold one
        // absolute deadline across the complete command so certification and
        // any nested trust re-confirmation consume the caller's ORIGINAL
        // timeout rather than receiving a renewed timeout (or no deadline).
        let is_decision_command = matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_));
        // #cert-accounting item 6: wall time of the OUTERMOST decision command
        // on this executor, so a nested probe solve entering here again cannot
        // sum its enclosing command's time into the total a second time.
        // Diagnostic bookkeeping — no gate, lane, or verdict reads it.
        let outermost_decision_command =
            is_decision_command && self.decision_command_depth.get() == 0;
        if outermost_decision_command {
            self.decision_command_depth.set(1);
        }
        let decision_timer = outermost_decision_command.then(cert_accounting::DecisionTimer::start);
        let publication_deadline =
            is_decision_command.then(|| self.install_command_publication_deadline());
        let result = self.execute_stack_guarded_with_publication_deadline(cmd, boundary);
        if let Some(previous_deadlines) = publication_deadline {
            self.restore_command_publication_deadline_after_call(previous_deadlines);
        }
        drop(decision_timer);
        if outermost_decision_command {
            self.decision_command_depth.set(0);
        }
        result
    }

    /// Command body entered with any decision-command publication deadline
    /// already installed by [`Self::execute_stack_guarded`].
    fn execute_stack_guarded_with_publication_deadline(
        &mut self,
        cmd: &Command,
        boundary: CommandExecutionBoundary,
    ) -> Result<Option<String>> {
        if boundary == CommandExecutionBoundary::NativeOptimization
            && !matches!(cmd, Command::CheckSat)
        {
            // Keep this before command processing or any solver call: if a
            // future refactor misuses the narrow native boundary, it must not
            // mint assumption/probe state and then rely on a caught panic for
            // cleanup. Revoke every predecessor decision before failing.
            self.begin_public_solve(false);
            unreachable!("the native optimization boundary is sealed to plain check-sat");
        }
        if matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_)) {
            // A new public decision query supersedes the preceding result even
            // when export preflight or command elaboration fails. Preserve only
            // Pareto's intentional cross-query enumeration state.
            match boundary {
                CommandExecutionBoundary::GenericText | CommandExecutionBoundary::AuthoredText => {
                    self.begin_external_decision_query(true);
                }
                CommandExecutionBoundary::NativeMaxSmtTextContinuation
                | CommandExecutionBoundary::NativeOptimization => self.begin_public_solve(true),
            }
        }
        // Query-local SMT-LIB 2.7 schematic instances are rebuilt by the
        // frontend at each check.  Remove them before incremental subsystems
        // snapshot or pop the assertion stack, so their scope boundaries are
        // computed from authored assertions rather than the previous query's
        // materialization.
        if matches!(
            cmd,
            Command::Push(_) | Command::Pop(_) | Command::Reset | Command::ResetAssertions
        ) {
            self.ctx.clear_materialized_polymorphic_assertions();
        }
        let internal_probe_command = match cmd {
            Command::GetConsequences(_, _) => Some("get-consequences"),
            Command::GetAbduct(_, _) => Some("get-abduct"),
            Command::Apply(tactic)
                if crate::api::Tactic::from_apply(tactic).may_invoke_solver() =>
            {
                Some("apply with ctx-solver-simplify")
            }
            _ => None,
        };
        if theories::bv_cnf_dump::requested() {
            if let Some(probe) = internal_probe_command {
                Self::invalidate_bv_cnf_export_for_rejected_check()?;
                return Err(ExecutorError::ArtifactExport(format!(
                    "--dump-bv-cnf does not support {probe} because it may run internal decision probes"
                )));
            }
        }

        // Track incremental mode: enabled on first push, disabled on reset
        // Context handles assertion scoping via push/pop (truncates on pop)
        match cmd {
            Command::Push(n) => {
                self.incremental_mode = true;
                // Theory state needs pre-push assertion capture before the
                // generic push dispatch. This is the only subsystem-specific
                // logic that can't be unified into the macro (#5992).
                {
                    let assertions_before_push = self.ctx.assertions.clone();
                    let theory_state = self
                        .incr_theory_state
                        .get_or_insert_with(IncrementalTheoryState::new);
                    if theory_state.pre_push_assertions.is_empty()
                        && theory_state.encoded_assertions.is_empty()
                        && theory_state.persistent_sat.is_none()
                        && theory_state.lia_persistent_sat.is_none()
                    {
                        theory_state
                            .pre_push_assertions
                            .extend(assertions_before_push);
                    }
                }
                // Dispatch push to all subsystems (#5992)
                for_each_incremental_subsystem!(push self, *n);
            }
            Command::Pop(n) => {
                if (*n as usize) > self.ctx.scope_depth() {
                    return Err(ExecutorError::Elaborate(
                        ay_frontend::ElaborateError::ScopeUnderflow,
                    ));
                }
                // Dispatch pop to all subsystems with underflow checks (#5992, #6230)
                let ok = for_each_incremental_subsystem!(pop self, *n);
                if !ok {
                    return Err(ExecutorError::Elaborate(
                        ay_frontend::ElaborateError::ScopeUnderflow,
                    ));
                }
                // #8304: Pop the lemma cache to the new scope level when
                // lemma persistence is enabled.
                if self.lemma_persistence {
                    let new_depth = self.incr_theory_state.as_ref().map_or(0, |s| s.scope_depth);
                    self.lemma_cache.pop_to_level(new_depth);
                }
            }
            Command::Reset => {
                self.incremental_mode = false;
                self.lemma_cache.clear();
                // `(reset)` is strictly stronger than `(reset-assertions)`, so
                // anything the latter clears this must clear too. The lane
                // account was missed: review measured `(reset)` between two
                // identical problems carrying session_certificates=2 across the
                // boundary, where `(reset-assertions)` correctly restarts at 1.
                // Costs lost answers only (a carried-over deficit closes the
                // lane early), never a wrong one.
                self.finite_model_lane.reset();
                for_each_incremental_subsystem!(reset self);
            }
            // reset-assertions clears assertions and scopes in the frontend
            // (Context::process_command), but the executor's persistent SAT
            // solvers, incremental state, and quantifier manager also need
            // resetting — otherwise stale learned clauses, scope counters,
            // and activation-clause mappings survive into subsequent queries.
            // (#5850)
            Command::ResetAssertions => {
                // Everything the append-only store holds RIGHT NOW belongs to
                // the epoch being discarded; nothing asserted after this point
                // can name the witnesses it minted. See
                // `assertion_epoch_terms_len`.
                self.assertion_epoch_terms_len = self.ctx.terms.len();
                // Discard all incremental state. A fresh state will be
                // created on the next push. Stay in incremental_mode per
                // SMT-LIB 2.6 §4.2.2.
                self.lemma_cache.clear();
                self.finite_model_lane.reset();
                for_each_incremental_subsystem!(drop self);
            }
            // Wire :random-seed option to executor for SAT solver (#6961)
            Command::SetOption(keyword, value) => {
                let key = keyword.strip_prefix(':').unwrap_or(keyword);
                if key == "random-seed" {
                    if let ay_frontend::sexp::SExpr::Numeral(ref n) = *value {
                        if let Ok(seed) = n.parse::<u64>() {
                            self.random_seed = Some(seed);
                        }
                    }
                } else if key == "timeout" {
                    // `(set-option :timeout <ms>)` installs a per-`check-sat`
                    // wall-clock deadline via the same mechanism as
                    // `set_timeout` (#8749). Without this, the option was
                    // parsed and silently dropped, so callers that configure a
                    // timeout through SMT-LIB — notably the PDR executor backend
                    // — got no deadline at all and a diverging NIA split loop
                    // ran forever. `0` means "no timeout" per Z3 convention.
                    if let ay_frontend::sexp::SExpr::Numeral(ref n) = *value {
                        if let Ok(ms) = n.parse::<u64>() {
                            self.set_timeout((ms != 0).then(|| Duration::from_millis(ms)));
                        }
                    }
                } else if key == "rlimit" {
                    // `(set-option :rlimit <conflicts>)` installs a deterministic
                    // conflict budget (#8749). Unlike `:timeout`, this bound is
                    // machine-independent — the same formula and seed stop at the
                    // same conflict count on every host — so verification results
                    // are reproducible. `0` means "no limit" per Z3 convention;
                    // since the default ground budget landed
                    // (#ground-determinism), `0` also disables that default so
                    // callers keep a true opt-out to unbounded solving.
                    // Previously this option was parsed and silently dropped, so a
                    // caller that relied on it for termination got no bound at all.
                    // Semantics live in `apply_rlimit_option` — shared with
                    // the `ay` CLI transcript layer, which echoes the option
                    // for z3-compat `get-option` but forwards the budget here.
                    if let ay_frontend::sexp::SExpr::Numeral(ref n) = *value {
                        self.apply_rlimit_option(n);
                    }
                } else if key == "max-memory" {
                    // `(set-option :max-memory <megabytes>)` installs a process-RSS
                    // ceiling, enforced at every check-sat boundary like `:timeout`
                    // (#8749). The value is megabytes (Z3 convention); `0` means "no
                    // limit". Previously parsed and silently dropped, so a caller
                    // that set a memory bound through SMT-LIB got none.
                    if let ay_frontend::sexp::SExpr::Numeral(ref n) = *value {
                        if let Ok(megabytes) = n.parse::<usize>() {
                            let bytes = megabytes.saturating_mul(1024 * 1024);
                            self.set_memory_limit((bytes != 0).then_some(bytes));
                        }
                    }
                }
            }
            // Reject only GENUINELY-UNRECOGNIZED logics (z3's `; ignoring
            // unsupported logic` frontier), not every `from_logic` miss. z3's
            // `set-logic` recognizer is structural/substring, and it SILENTLY
            // accepts many tokens AY does not map to a category (e.g. QF_UFLIRA,
            // AUFBVDTLIA): those solve with ALL semantics and exit 0. AY mirrors
            // this — `is_z3_recognized_logic` accepted-but-unmapped tokens fall
            // through here and are STORED, then route through the same content
            // detection as the unset case (verdict-identical to today's
            // post-rejection path). Only tokens z3 itself would ignore
            // (`is_z3_recognized_logic` false) are rejected → `unsupported` +
            // ALL semantics. The fail-closed combined logics (all contain "BV",
            // so `is_z3_recognized_logic` accepts them) are stored but excluded
            // from content detection in `logic_detect.rs`, keeping their sound
            // `unknown`. (#combined-bv-arith)
            Command::SetLogic(logic)
                if matches!(
                    crate::logic_detection::LogicCategory::from_logic(logic),
                    crate::logic_detection::LogicCategory::Other
                ) && !crate::logic_detection::is_z3_recognized_logic(logic) =>
            {
                return Err(ExecutorError::UnsupportedLogic(logic.clone()));
            }
            _ => {}
        }

        let result = match self.ctx.process_command(cmd) {
            Ok(result) => result,
            Err(error) => {
                // `check-sat-assuming` elaborates its assumption literals in
                // `process_command`, before the normal check transaction is
                // entered.  A failed decision command must still retire the
                // preceding certificate instead of leaving it authoritative.
                if theories::bv_cnf_dump::requested()
                    && matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_))
                {
                    Self::invalidate_bv_cnf_export_for_rejected_check()?;
                }
                return Err(error.into());
            }
        };
        if matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_)) {
            // `begin_public_solve` intentionally ran before elaboration to
            // revoke stale artifacts on every failure path. Rebind its exact
            // UNSAT/proof authority now that SMT-LIB 2.7 schematic instances
            // have been materialized, and before assumptions or solver-owned
            // transformations can enter the query.
            self.bind_materialized_public_query();
        }
        if matches!(cmd, Command::Pop(_)) {
            if let Some(ref mut state) = self.incr_theory_state {
                state.retain_encoded_assertions(&self.ctx.assertions);
            }
        }
        if Self::command_invalidates_last_check_result(cmd) {
            self.invalidate_last_check_result();
        }

        match result {
            Some(CommandResult::CheckSat) => {
                self.bind_unsat_query_assumptions(&[]);
                if !self.ctx.polymorphic_instantiation_complete() {
                    self.replace_last_result_with_unknown(UnknownReason::Unsupported);
                    return Ok(Some(SolveResult::Unknown.to_string()));
                }
                if theories::bv_cnf_dump::requested()
                    && (!self.ctx.soft_constraints().is_empty()
                        || !self.ctx.objectives().is_empty())
                {
                    Self::invalidate_bv_cnf_export_for_rejected_check()?;
                    return Err(ExecutorError::ArtifactExport(
                        "--dump-bv-cnf does not support optimization or MaxSMT checks".to_string(),
                    ));
                }
                let has_softs = !self.ctx.soft_constraints().is_empty();
                let has_objectives = !self.ctx.objectives().is_empty();
                let sat_result = if has_softs && has_objectives {
                    // Joint arithmetic-objective + soft optimization is not yet
                    // implemented. Prioritizing either branch silently drops
                    // half of the declared problem and can publish a non-joint
                    // model value as an optimum. Refuse the mixed problem until
                    // one engine certifies both objective classes together.
                    self.invalidate_last_check_result();
                    self.record_unknown_from_origin(UnknownOrigin::UnsupportedFeature);
                    SolveResult::Unknown
                } else if has_softs {
                    // `(assert-soft ...)` present: solve the MaxSMT problem.
                    // Soundness: a soft constraint is NOT a hard constraint, so
                    // this minimizes the total weight of violated softs subject
                    // to the hard assertions rather than asserting them hard.
                    self.maxsmt_check_sat()?
                } else if !has_objectives {
                    // Route through check_sat() which calls finalize_sat_model_validation().
                    // Previously called check_sat_internal() directly, bypassing model
                    // validation — an escape hatch that violated the verification invariant.
                    // Part of #5787 (Phase 6).
                    if boundary == CommandExecutionBoundary::AuthoredText {
                        self.solve_authored_plain_hard_query(&[])?
                    } else {
                        self.check_sat()?
                    }
                } else {
                    self.optimize_check_sat()?
                };
                let sat_result = self.certify_unsat_for_publication(sat_result, &[]);
                let sat_result = match boundary {
                    CommandExecutionBoundary::GenericText
                    | CommandExecutionBoundary::AuthoredText
                    | CommandExecutionBoundary::NativeMaxSmtTextContinuation => {
                        self.admit_command_solve_result(sat_result)
                    }
                    CommandExecutionBoundary::NativeOptimization => sat_result,
                };
                let display = sat_result.to_string();
                self.last_result = Some(sat_result);
                Ok(Some(display))
            }
            Some(CommandResult::CheckSatAssuming(assumptions)) => {
                self.bind_authored_unsat_query_assumptions(&assumptions, cmd);
                if !self.ctx.polymorphic_instantiation_complete() {
                    self.replace_last_result_with_unknown(UnknownReason::Unsupported);
                    return Ok(Some(SolveResult::Unknown.to_string()));
                }
                if theories::bv_cnf_dump::requested()
                    && (!self.ctx.soft_constraints().is_empty()
                        || !self.ctx.objectives().is_empty())
                {
                    Self::invalidate_bv_cnf_export_for_rejected_check()?;
                    return Err(ExecutorError::ArtifactExport(
                        "--dump-bv-cnf does not support optimization or MaxSMT checks".to_string(),
                    ));
                }
                if !self.ctx.soft_constraints().is_empty() || !self.ctx.objectives().is_empty() {
                    // Assumption-scoped optimization is not implemented.  The
                    // ordinary assumption solver treats only the hard formula
                    // and would silently drop every parsed soft constraint (as
                    // well as every arithmetic objective).  Reject both
                    // objective classes uniformly and explicitly retire any
                    // artefacts from the preceding public query.
                    self.invalidate_last_check_result();
                    return Err(ExecutorError::UnsupportedOptimization(
                        "check-sat-assuming with soft constraints or objectives is not supported"
                            .to_string(),
                    ));
                }
                let sat_result = self.check_sat_assuming_with_named_cores(&assumptions)?;
                let sat_result = self.certify_unsat_for_publication(sat_result, &assumptions);
                let sat_result = match boundary {
                    CommandExecutionBoundary::GenericText
                    | CommandExecutionBoundary::AuthoredText
                    | CommandExecutionBoundary::NativeMaxSmtTextContinuation => {
                        self.admit_command_solve_result(sat_result)
                    }
                    CommandExecutionBoundary::NativeOptimization => {
                        unreachable!("the native optimization boundary was rejected before solve")
                    }
                };
                let display = sat_result.to_string();
                self.last_result = Some(sat_result);
                Ok(Some(display))
            }
            Some(CommandResult::GetModel) => Ok(Some(self.model_after_nra_refinement())),
            Some(CommandResult::GetObjectives) => Ok(Some(self.get_objectives())),
            Some(CommandResult::GetObjectiveCertificates) => {
                Ok(Some(self.get_objective_certificates()))
            }
            Some(CommandResult::GetValue(pairs)) => Ok(Some(self.values(&pairs))),
            Some(CommandResult::Eval(term_id)) => Ok(Some(self.eval_term(term_id))),
            Some(CommandResult::GetConsequences(assumptions, variables)) => {
                Ok(Some(self.get_consequences(&assumptions, &variables)?))
            }
            Some(CommandResult::GetInfo(keyword)) => Ok(Some(self.get_info(&keyword))),
            Some(CommandResult::GetOption(keyword)) => Ok(Some(self.get_option_value(&keyword))),
            Some(CommandResult::Labels) => Ok(Some(self.labels())),
            Some(CommandResult::GetAssertions) => Ok(Some(self.assertions())),
            Some(CommandResult::Echo(msg)) => Ok(Some(msg)),
            Some(CommandResult::Display(term)) => Ok(Some(term)),
            Some(CommandResult::GetAssignment) => Ok(Some(self.get_assignment())),
            Some(CommandResult::GetUnsatCore) => Ok(Some(self.unsat_core())),
            Some(CommandResult::GetUnsatCoreWithFarkas) => Ok(Some(self.unsat_core_with_farkas())),
            Some(CommandResult::GetUnsatAssumptions) => Ok(Some(self.unsat_assumptions())),
            Some(CommandResult::GetProof) => Ok(Some(self.get_proof())),
            Some(CommandResult::Exit) => Ok(Some("exit".to_string())),
            Some(CommandResult::Simplify(term_id)) => Ok(Some(self.simplify(term_id))),
            Some(CommandResult::Apply(tactic)) => Ok(Some(self.apply_tactic_goal(&tactic))),
            Some(CommandResult::GetAbduct(name, goal)) => Ok(Some(self.get_abduct(&name, goal)?)),
            #[allow(unreachable_patterns)]
            Some(_) => Ok(Some("unsupported".to_string())),
            None => Ok(None),
        }
    }

    /// Set the maximum number of E-matching rounds per check-sat call.
    ///
    /// Clamped to `[1, MAX_EMATCHING_ROUND_CEILING]`. The solve deadline still
    /// bounds wall-clock time, so a high round limit chains deeper quantifier
    /// instantiations without risking non-termination.
    pub fn set_ematching_round_limit(&mut self, n: usize) {
        self.ematching_round_limit = Some(n.clamp(1, MAX_EMATCHING_ROUND_CEILING));
    }

    /// Returns the E-matching round limit (default: `MAX_EMATCHING_ROUNDS`).
    pub fn ematching_round_limit(&self) -> usize {
        self.ematching_round_limit.unwrap_or(MAX_EMATCHING_ROUNDS)
    }

    pub(crate) fn current_random_seed(&self) -> u64 {
        match self.ctx.get_option("random-seed") {
            Some(OptionValue::Numeral(seed)) => seed.parse::<u64>().unwrap_or(0),
            Some(OptionValue::String(seed)) => seed.parse::<u64>().unwrap_or(0),
            _ => 0,
        }
    }

    pub(crate) fn record_applied_sat_random_seed_for_test(&self, seed: u64) {
        #[cfg(test)]
        self.last_applied_sat_random_seed.set(Some(seed));
        #[cfg(not(test))]
        let _ = seed;
    }

    pub(crate) fn record_applied_dpll_random_seed_for_test(&self, seed: u64) {
        #[cfg(test)]
        self.last_applied_dpll_random_seed.set(Some(seed));
        #[cfg(not(test))]
        let _ = seed;
    }

    pub(crate) fn apply_random_seed_to_sat(&self, solver: &mut ay_sat::Solver) {
        let seed = self.current_random_seed();
        self.record_applied_sat_random_seed_for_test(seed);
        solver.set_random_seed(seed);
    }

    /// Default per-SAT-solve conflict allowance of the deterministic ground
    /// budget (#ground-determinism).
    ///
    /// Calibrated 2026-07-10 (workflow wf_94d63891) on the ay-dpll heavy
    /// suite groups (auflia, quantifiers, datatypes, theory_misc,
    /// regression: 1,104 check-sat solves, max 2,208 conflicts per solver
    /// lifetime, nothing above 10k) and the heaviest known real workload,
    /// the deductive-checks calc.rs line93 seq-chain BV<->LIA bridge (~1,266
    /// conflicts per 300k decisions — conflict-LIGHT; its conflict count
    /// stays far below this allowance for the whole decision budget).
    /// 400k = ~180x the suite ceiling: generous headroom for legitimate
    /// proofs while still bounding a conflict-churn divergence to a small
    /// deterministic multiple of any observed real workload.
    pub(crate) const DEFAULT_GROUND_CONFLICT_ALLOWANCE: u64 = 400_000;

    /// Default per-SAT-solve decision allowance of the deterministic ground
    /// budget (#ground-determinism).
    ///
    /// The decision axis exists because theory-extension churn is decision-
    /// heavy and conflict-light (calc.rs line93: ~240 decisions per
    /// conflict), so a conflict allowance alone cannot bound it.
    /// Calibration data (2026-07-10, wf_94d63891): suite ceiling 505k
    /// decisions per solver lifetime (3 of 1,104 solves above 100k — all
    /// deliberate timeout/divergence tests); the calc.rs line93 bridge
    /// solve did NOT converge within >25M decisions on this ay base
    /// (unoptimized build, 2,400s deadline override) — the "4.7M decisions"
    /// from the original flake report was mid-search, not near-convergence,
    /// so for this obligation the honest budget outcome is a deterministic
    /// Unknown(ResourceLimit) instead of a load-dependent Timeout. 24M =
    /// ~47x the passing-suite ceiling, comfortably above the pinned-era
    /// convergence scale of the heaviest legitimate proofs, and small
    /// enough that a fast host reaches the deterministic stop within the
    /// far-out wall backstop.
    pub(crate) const DEFAULT_GROUND_DECISION_ALLOWANCE: u64 = 24_000_000;

    pub(crate) fn apply_random_seed_to_dpll<T: ay_core::TheorySolver>(
        &self,
        dpll: &mut crate::DpllT<'_, T>,
    ) {
        let seed = self.current_random_seed();
        self.record_applied_dpll_random_seed_for_test(seed);
        dpll.set_random_seed(seed);
    }

    /// Apply progress setting to a raw SAT solver.
    pub(crate) fn apply_progress_to_sat(&self, solver: &mut ay_sat::Solver) {
        if self.progress_enabled {
            solver.set_progress_enabled(true);
        }
        if let Some(path) = &self.progress_json_path {
            if let Ok(obs) = ay_sat::json_observer::JsonProgressObserver::new_append(path) {
                solver.set_observer(Some(Box::new(obs)));
            }
        }
    }

    /// Apply progress setting to a DpllT solver.
    pub(crate) fn apply_progress_to_dpll<T: ay_core::TheorySolver>(
        &self,
        dpll: &mut crate::DpllT<'_, T>,
    ) {
        if self.progress_enabled {
            dpll.set_progress_enabled(true);
        }
        if let Some(path) = &self.progress_json_path {
            if let Ok(obs) = ay_sat::json_observer::JsonProgressObserver::new_append(path) {
                dpll.set_observer(Some(Box::new(obs)));
            }
        }
    }
}
