// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT executor - orchestrates frontend and theory solver
//!
//! Provides a high-level interface for executing SMT-LIB commands with
//! theory integration.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{ClausificationProof, Proof, TheoryLemmaProof};
use ay_core::{TermId, TermStore};
use ay_frontend::{Command, CommandResult, Context, OptionValue};
use ay_sat::{ClauseTrace, SatUnknownReason};
use std::cell::Cell;
use std::sync::{atomic::AtomicBool, Arc};
use std::time::Duration;

use crate::incremental_state::IncrementalSubsystem;

use ay_proof::PartialProofCheck;

use crate::executor_types::{ExecutorError, Result, SolveResult, Statistics, UnknownReason};
use crate::quantifier_manager::QuantifierManager;
use crate::VerificationLevel;

// Combined theory solvers
pub use crate::combined_solvers::TheoryCombiner;
// Format helpers - format_sort, format_symbol now used in executor/commands.rs

// Incremental state types
use crate::incremental_state::{IncrementalBvState, IncrementalTheoryState};

/// Bounded E-matching passes per check-sat to allow instantiation chaining.
///
/// Each round builds a fresh TermIndex, so terms created by instantiation in
/// round N become matchable in round N+1. A chain of depth D (where axiom A's
/// output triggers axiom B, whose output triggers axiom C, etc.) requires D
/// rounds.
///
/// Budget 16 covers typical axiom chains in verification-consumer's 21-axiom Seq encoding
/// (#3994) plus deeper iterator/permutation clusters whose instantiation chains
/// exceed the original budget of 8 (the chain output of round N only becomes
/// matchable in round N+1, so an axiom family of depth D needs D rounds).
/// Generation-based cost filtering (eager/lazy thresholds) prevents
/// self-triggering patterns from consuming the budget, and the solve deadline
/// floor keeps each chain terminating even when the round budget is raised.
const MAX_EMATCHING_ROUNDS: usize = 16;

/// Hard ceiling on the configurable E-matching round limit.
///
/// Callers (e.g. verification-consumer proof obligations) may raise the per-solver round
/// limit via [`Executor::set_ematching_round_limit`] up to this bound to allow
/// very deep quantifier chains. The solve deadline still bounds wall-clock
/// time, so a high ceiling cannot cause a non-terminating solve.
const MAX_EMATCHING_ROUND_CEILING: usize = 128;

/// Maximum interleaved E-matching refinement rounds after initial SAT solve.
///
/// After the initial E-matching preprocessing + SAT solve, the interleaved loop
/// re-runs E-matching with the fresh EUF model from the solve. New congruence
/// equalities discovered during solving can trigger new pattern matches that
/// weren't available during preprocessing. Each round: E-match → add instances
/// → re-solve → repeat until fixpoint or budget (#5927).
///
/// Budget 4 is conservative — enough for typical multi-step quantifier chains
/// (e.g., verification-consumer's `f(g(a)) = b` patterns that need 2-3 rounds) without
/// excessive overhead on already-converged formulas.
const MAX_INTERLEAVED_EMATCHING_ROUNDS: usize = 4;

mod assumption_solving;
mod bv_mbqi;
mod check_sat;
mod check_sat_assuming;
mod commands;
mod core_minimize;
mod diff_logic;
pub(crate) mod dl_theory;
mod dt_axioms;
pub(crate) mod ite_lift;
pub(crate) mod lean_firewall;
pub(crate) mod lemma_cache;
mod lnh_symmetry;
mod logic_detect;
mod mbqi;
mod mod_div_elim;
mod model;
pub(crate) mod optimization;
mod partition_rescue;
mod proof;
mod proof_array_ext;
mod proof_euf_lemma;
mod proof_farkas;
mod proof_original_rebuild;
mod proof_resolution;
mod proof_rewrite;
mod proof_rewrite_division;
mod proof_rewrite_terms;
mod proof_surface_syntax;
mod proof_trust_surgery;
mod purify_bool_args;
mod purify_int_uf_arith;
mod qe_prepass;
mod quantifier_loop;
mod rewrite_const_array_reads;
mod rm_domain;
mod solve_deadline;
mod stats_contract;
pub(crate) mod theories;
mod uflia_model_repair;
use model::Model;
// Re-export the SAT-emission witness token so the API boundary
// (`api::types::results`) can name it while its constructor stays private to
// the `sat_emit` module (mintable only inside `emit_sat_verdict`) (#sat-chokepoint).
pub(crate) use model::sat_emit::SatCertificate;
pub(crate) use solve_deadline::SolveDeadlineCell;

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

/// D1 shadow instrumentation for the on-assert lazy-extensionality campaign.
///
/// The eager path (`add_array_extensionality_axioms_up_to`) emits one
/// `__ay_ext_diff(a,b)` witness clause per SYNTACTIC array-equality atom whose
/// negation appears anywhere in the term store — an over-approximation that
/// balloons on qlock-style AUFLIA (many witnesses vs z3's few demand-driven).
/// This struct records, per solve, the EAGER set of pairs actually emitted so
/// the finalizer can correlate it against the DEMANDED set (pairs whose
/// equality atom the search forced false) and surface the dead mass on `-st`.
///
/// Measurement only: the eager path stays authoritative and is never gated on
/// this data. Kept always-on (not `cfg(debug_assertions)`) so the counters are
/// visible on release `-st` runs; the sets are tiny (bounded by the number of
/// array-equality atoms) so the overhead is negligible.
#[derive(Debug, Clone, Default)]
pub(crate) struct ArrayExtShadow {
    /// Per emitted witness: `(eq_term, lhs, rhs, not_sel_eq_atom)`.
    ///
    /// `eq_term` is the `(= a b)` atom the extensionality clause guards;
    /// `not_sel_eq` is the `¬((select a k) = (select b k))` witness literal.
    /// Deduplicated by the ordered `(lhs, rhs)` pair at record time.
    pub(crate) emitted: Vec<(TermId, TermId, TermId, TermId)>,
    /// Ordered `(lhs, rhs)` pairs already recorded, to dedup emissions.
    pub(crate) seen_pairs: HashSet<(TermId, TermId)>,
}

impl ArrayExtShadow {
    pub(crate) fn clear(&mut self) {
        self.emitted.clear();
        self.seen_pairs.clear();
    }

    /// Record one emitted extensionality witness. Returns false if the ordered
    /// pair was already recorded this solve (caller may ignore).
    pub(crate) fn record(
        &mut self,
        eq_term: TermId,
        lhs: TermId,
        rhs: TermId,
        not_sel_eq: TermId,
    ) -> bool {
        let pair = if lhs.0 <= rhs.0 {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };
        if !self.seen_pairs.insert(pair) {
            return false;
        }
        self.emitted.push((eq_term, lhs, rhs, not_sel_eq));
        true
    }
}

/// Provenance of one finite-domain quantifier expansion that replaced a
/// top-level `forall` assertion with its ground instance conjunction
/// (#quant-expansion-proof).
///
/// Recorded by `expand_finite_domains` and kept in sync by the later
/// in-place assertion rewrites of the quantifier lane (strict-int
/// tightening), so at proof-export time `expanded` still equals the
/// solver-visible assertion the exported `assume` carries. The trust
/// surgery matches an unmatched `assume` against `expanded`, then derives
/// each consumed conjunct from `original` (the genuine problem premise)
/// with `forall_inst` + guard-discharge steps, using `instances` to look
/// up the binder-value tuple that produced the conjunct.
#[derive(Debug, Clone)]
pub(crate) struct QuantExpansionRecord {
    /// The original assertion — the `forall` term itself.
    pub(crate) original: TermId,
    /// Position of the replaced assertion on the assertion stack at
    /// expansion time (aligned with `assertions_parsed()` for the
    /// non-flattened prefix; the surgery re-verifies the surface shape).
    pub(crate) assertion_index: usize,
    /// The current ground replacement conjunction (tracks in-place rewrites).
    pub(crate) expanded: TermId,
    /// Per enumerated instantiation: binder values (in binder order) and the
    /// folded instance term as merged into `expanded` (kept in sync with the
    /// same rewrites).
    pub(crate) instances: Vec<(Vec<TermId>, TermId)>,
}

/// SMT executor that coordinates frontend parsing with theory solving
pub struct Executor {
    /// Frontend context for elaboration
    pub(crate) ctx: Context,
    /// Strings NF-engine closure 5 (`AY_STR_NF=1`) bookkeeping: whether EVERY
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
    /// (`AY_UFLIA_FUSED_DETOUR=1`, combined/mod.rs #fused-detour slot);
    /// always reset immediately after (plus the unconditional post-attempt
    /// and entry-defensive resets in `solve_uf_lia`). Default `false` keeps
    /// every eager expansion (eager1, the hybrid resume, AUFLIA/UF+LRA
    /// lanes) byte-identical. `AY_RELEVANCY=0` still kills it (env override
    /// wins, mirroring the lazy seam).
    pub(crate) split_eager_relevancy_hard: bool,
    /// #relevancy-lazy-routing: when `true`, the lazy split-loop arm runs its
    /// per-round SAT solves with the relevancy brancher in HARD mode (engage
    /// on every decision — the design prototype's regime). Set only around the
    /// UFLIA hybrid's lazy fallback / forced-lazy attempt; always reset
    /// immediately after. `AY_RELEVANCY=0` still kills it (env override wins).
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
    /// #verify-memo (`AY_VERIFY_MEMO=1`): sampled semantic PROPAGATION
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
    /// conjunction (#quant-expansion-proof). The proof exporter's trust
    /// surgery uses these to re-derive each consumed conjunct from the
    /// ORIGINAL `forall` premise via `forall_inst` steps, so the exported
    /// `assume` matches the problem file instead of the merged expansion no
    /// external checker can match. Cleared per check-sat alongside
    /// `proof_problem_assertion_provenance`.
    pub(crate) quant_expansion_records: Vec<QuantExpansionRecord>,
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
    /// Quality metrics from last proof validation (#4420)
    last_proof_quality: Option<ay_proof::ProofQuality>,
    /// Reason for last Unknown result (for get-info :reason-unknown)
    last_unknown_reason: Option<UnknownReason>,
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
    /// (#lra-inc-engine, S1). `None` (default) follows the `AY_LRA_INC_ENGINE`
    /// env flag (default ON); `Some(true)` forces the lane on and `Some(false)`
    /// forces it off, both independent of the environment. Exists so regression
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
    /// Persistent state for incremental theory solving (UF/LRA/LIA)
    pub(crate) incr_theory_state: Option<IncrementalTheoryState>,
    /// Style for counterexample generation (model minimization)
    counterexample_style: crate::CounterexampleStyle,
    /// Proof tracker for collecting proof steps during solving
    proof_tracker: crate::proof_tracker::ProofTracker,
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
    /// Deadline propagated from API-level timeout settings.
    ///
    /// LIVE shared cell (#quantifier-determinism): stop closures capture a
    /// `.clone()` handle and poll through it, so the mid-call backstop
    /// extension (`install_quantifier_deadline_backstop`) and the
    /// alternation-validation sub-deadline tighten/restore windows are
    /// visible to closures built at ANY point in the call. Value snapshots
    /// (save/restore, plumbing into per-sub-solve components) use `.get()`.
    solve_deadline: SolveDeadlineCell,
    /// One-shot marker: the quantified-solve wall-clock backstop extension has
    /// been applied for the current check-sat call (#quantifier-determinism,
    /// see `install_quantifier_deadline_backstop`). Re-armed per call in
    /// `install_timeout_deadline_for_call`; prevents nested quantified
    /// re-entries (alternation validation sub-solves) from compounding the
    /// extension.
    quantifier_deadline_backstop_installed: bool,
    /// #read-congruence-quantified-scope (#7956 tseitin regression): `true`
    /// from the moment the current check-sat's quantifier pipeline actually
    /// instantiates quantifiers (`process_quantifiers`, past its
    /// no-quantifiers early return) until the next check-sat re-arms it in
    /// `install_timeout_deadline_for_call`. Ground (re-)solve combiners
    /// constructed while it is set disable the store-carrying
    /// read-congruence index-pair obligations — see
    /// `TheoryCombiner::set_read_congruence_pairs_enabled`.
    pub(in crate::executor) quantifier_pipeline_engaged: bool,
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
    /// When true, `solve_and_store_model_full` stores the SAT/theory model but
    /// skips SAT-preserving counterexample minimization until the caller
    /// restores the original assertion set. Used by standalone preprocessing
    /// lanes whose temporary reduced assertions are not the user-facing formula.
    defer_counterexample_minimization: bool,
    /// True when `finalize_sat_model_validation` actually ran and passed on the
    /// last solve call. Reset to `false` at the start of each `check_sat`.
    /// Used by the API layer to accurately report `sat_model_validated` (#5903).
    last_model_validated: bool,
    /// Unforgeable witness that the last emitted `Sat` passed the single
    /// `emit_sat_verdict` funnel (strict + independent + authoritative gates).
    /// Minted ONLY inside `emit_sat_verdict`; the API boundary consumes it via
    /// `take_sat_certificate` to build a public `Sat` `VerifiedSolveResult`, so
    /// no `Sat` can escape the boundary without the funnel (#sat-chokepoint).
    last_sat_certificate: Option<SatCertificate>,
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
    /// Exact NRA ALGEBRAIC model witnesses for the current SAT (e.g.
    /// `x*x = 2` ⇒ `x = √2` as a `root-obj`), produced by the NRA theory's
    /// exact Sturm/IVT irrational-root certificate. Variable lookup
    /// (`evaluate_var`), polynomial evaluation (`eval_arith`), get-value/
    /// get-model printing and FULL model validation all consult these
    /// witnesses and compute with them exactly, so the certificate path needs
    /// NO validation suppression: validation runs and confirms the model.
    /// Reset at the start of each `check_sat`/`check_sat_assuming`.
    nra_algebraic_model: HashMap<TermId, ay_nra::RealAlgebraicValue>,
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
    dt_egraph_assignment: std::cell::RefCell<Option<Arc<model::DtEgraphAssignment>>>,
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
    array_def_index: std::cell::RefCell<Option<model::ArrayDefIndexCache>>,
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
    select_by_array_index:
        std::cell::RefCell<(usize, ay_core::kani_compat::DetHashMap<TermId, Vec<TermId>>)>,
    /// Cached ground-term reachability closure of `(assertions, assumptions)`
    /// behind `term_is_required_by_last_query`: `(assertions snapshot,
    /// assumptions snapshot, reachable set)`. Validated by BYTE-EXACT snapshot
    /// compare on every query (cheap: one id-vector compare vs the full-forest
    /// DFS it replaces, which previously ran PER CANDIDATE READ during array
    /// completion — O(reads × forest) with fresh hash-set churn each time).
    #[allow(clippy::type_complexity)]
    required_terms_index: std::cell::RefCell<
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
    /// W7 (`AY_STR_W7=1`, default OFF): the DEFINING equations
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
    /// AUTHORED assertion window of the check-sat currently in flight, captured
    /// in `check_sat_internal` BEFORE any in-place preprocessing pass runs
    /// (#selfcert-authored).
    ///
    /// Only the fail-closed `--self-check` SAT gate reads this, and only to
    /// certify the model against the formula the USER actually asserted. The
    /// gate's ordinary denominator is `ctx.assertions` at validation time, which
    /// under `--self-check` (proofs forced on) also carries solver-injected
    /// theory axioms over fresh internal symbols (`__ay_*`).
    /// Those are skipped as `Internal` and counted "unverified", so a QF_AX
    /// model that satisfies every authored assertion was degraded to `unknown`.
    /// See `self_check_authored_model_certified`.
    ///
    /// Saved/restored around the nested `check_sat_internal` re-entries (probe
    /// and retry solves) so an inner solve's narrower window can never be used
    /// to certify the outer verdict. `None` (no snapshot) fails closed.
    self_check_authored_assertions: Option<Vec<TermId>>,
    /// Temporary scope filter for array axiom generation in incremental mode (#6726).
    /// When `Some`, the fixpoint generators skip terms not reachable from current
    /// assertions. The `usize` is the TermStore length at fixpoint entry — terms
    /// created during the fixpoint (idx >= this) always pass the scope check.
    array_axiom_scope: Option<(HashSet<TermId>, usize)>,
    /// #8785: select terms that were first created by eager ROW seeding in the
    /// current preprocessing run. These descendants must not recursively seed
    /// further eager ROW terms, or AUFLIA storecomm reproducers can project a
    /// top-level disequality onto internal store prefixes and produce false UNSAT.
    row_seeded_terms: HashSet<TermId>,
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
    /// When true, the independent fail-closed model-check gate
    /// ([`ay_model_check::confirm_model`]) is NOT run after a `Sat` result.
    ///
    /// Default `false` (the gate is ON for `check-sat`): every `Sat` model is
    /// re-checked by a separate, solver-independent evaluator, and a `Sat`
    /// whose model that evaluator ground-refutes is unconditionally downgraded
    /// to `Unknown` (fail closed); see
    /// [`Executor::apply_independent_model_gate`]. Toggle with
    /// [`Executor::set_independent_model_gate`] — a DEBUGGING-ONLY programmatic
    /// escape hatch; there is deliberately NO env-var bypass (the former
    /// `AY_NO_MODEL_CHECK_GATE` is removed — no environment variable may turn
    /// off a soundness gate), and nothing in production code, CI, or the test
    /// suites disables the gate.
    independent_gate_disabled: bool,
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

/// Central registry of incremental subsystems (#5992).
///
/// Adding a new incremental subsystem requires:
/// 1. Implementing `IncrementalSubsystem` for the type
/// 2. Adding the field to this macro (and whether it's `Option<T>` or direct)
///
/// The macro dispatches push/pop/reset to all subsystems uniformly,
/// eliminating the 4×N shotgun surgery pattern.
macro_rules! for_each_incremental_subsystem {
    // Push: init-or-get for Option fields, call directly for non-Option.
    (push $self:expr, $n:expr) => {{
        let bv = $self
            .incr_bv_state
            .get_or_insert_with(IncrementalBvState::new);
        for _ in 0..$n {
            bv.push();
        }
        // NOTE: Theory state has special pre-push assertion logic handled
        // by the caller before this macro invocation. The push itself is
        // dispatched here.
        let ts = $self
            .incr_theory_state
            .get_or_insert_with(IncrementalTheoryState::new);
        for _ in 0..$n {
            ts.push();
        }
        let qm = $self
            .quantifier_manager
            .get_or_insert_with(QuantifierManager::new);
        for _ in 0..$n {
            qm.push();
        }
        for _ in 0..$n {
            $self.proof_tracker.push();
        }
    }};
    // Pop: if-let for Option fields, call directly for non-Option.
    // Returns true if all subsystems popped successfully.
    (pop $self:expr, $n:expr) => {{
        let mut ok = true;
        if let Some(ref mut s) = $self.incr_bv_state {
            for _ in 0..$n {
                ok &= s.pop();
            }
        }
        if let Some(ref mut s) = $self.incr_theory_state {
            for _ in 0..$n {
                let popped = s.pop();
                ok &= popped;
            }
        }
        if let Some(ref mut s) = $self.quantifier_manager {
            for _ in 0..$n {
                let popped = s.pop();
                ok &= popped;
            }
        }
        for _ in 0..$n {
            let popped = $self.proof_tracker.pop();
            ok &= popped;
        }
        ok
    }};
    // Reset: if-let for Option fields, call directly for non-Option.
    (reset $self:expr) => {{
        if let Some(ref mut s) = $self.incr_bv_state {
            s.reset();
        }
        if let Some(ref mut s) = $self.incr_theory_state {
            s.reset();
        }
        if let Some(ref mut s) = $self.quantifier_manager {
            s.reset();
        }
        $self.proof_tracker.reset();
    }};
    // Drop: set Option fields to None, reset non-Option fields.
    // Used by ResetAssertions which discards all state.
    (drop $self:expr) => {{
        $self.incr_bv_state = None;
        $self.incr_theory_state = None;
        $self.quantifier_manager = None;
        $self.proof_tracker.reset();
    }};
}

mod lifecycle;

#[cfg(test)]
#[path = "executor/maxsmt_tests.rs"]
mod maxsmt_tests;

#[cfg(test)]
#[path = "executor/diff_logic_tests.rs"]
mod diff_logic_tests;

#[cfg(test)]
#[path = "executor/dl_theory_tests.rs"]
mod dl_theory_tests;

#[cfg(test)]
#[path = "executor/dl_theory_rollback_tests.rs"]
mod dl_theory_rollback_tests;

impl Executor {
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
            self.execute_stack_guarded(cmd)
        })
    }

    /// Body of [`Executor::execute`] — only called through the stack guard
    /// above so its (large, low-opt) frame lands on the grown segment.
    fn execute_stack_guarded(&mut self, cmd: &Command) -> Result<Option<String>> {
        if matches!(cmd, Command::CheckSat | Command::CheckSatAssuming(_)) {
            // A new public decision query supersedes the preceding result even
            // when export preflight or command elaboration fails. Preserve only
            // Pareto's intentional cross-query enumeration state.
            self.begin_public_solve(true);
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
                for_each_incremental_subsystem!(reset self);
            }
            // reset-assertions clears assertions and scopes in the frontend
            // (Context::process_command), but the executor's persistent SAT
            // solvers, incremental state, and quantifier manager also need
            // resetting — otherwise stale learned clauses, scope counters,
            // and activation-clause mappings survive into subsequent queries.
            // (#5850)
            Command::ResetAssertions => {
                // Discard all incremental state. A fresh state will be
                // created on the next push. Stay in incremental_mode per
                // SMT-LIB 2.6 §4.2.2.
                self.lemma_cache.clear();
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
                    if let ay_frontend::sexp::SExpr::Numeral(ref n) = *value {
                        if let Ok(budget) = n.parse::<u64>() {
                            self.set_resource_limit((budget != 0).then_some(budget));
                            if budget == 0 {
                                self.set_ground_budget_enabled(false);
                            }
                        }
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
                    self.last_unknown_reason = Some(UnknownReason::Unsupported);
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
                    self.check_sat()?
                } else {
                    self.optimize_check_sat()?
                };
                let display = sat_result.to_string();
                self.last_result = Some(sat_result);
                Ok(Some(display))
            }
            Some(CommandResult::CheckSatAssuming(assumptions)) => {
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
                let display = sat_result.to_string();
                self.last_result = Some(sat_result);
                Ok(Some(display))
            }
            Some(CommandResult::GetModel) => Ok(Some(self.model())),
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
            Some(CommandResult::GetAssertions) => Ok(Some(self.assertions())),
            Some(CommandResult::Echo(msg)) => Ok(Some(msg)),
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

    #[cfg(test)]
    pub(crate) fn last_applied_sat_random_seed_for_test(&self) -> Option<u64> {
        self.last_applied_sat_random_seed.get()
    }

    #[cfg(test)]
    pub(crate) fn last_applied_dpll_random_seed_for_test(&self) -> Option<u64> {
        self.last_applied_dpll_random_seed.get()
    }

    /// Number of core-guided rounds the OLL MaxSMT engine completed on its most
    /// recent invocation (#phase2-pr1). 0 means OLL fell back to the baseline
    /// without core-guided progress. Used by the MaxSMT soundness tests.
    #[cfg(test)]
    pub(crate) fn last_oll_core_rounds_for_test(&self) -> u64 {
        self.last_oll_core_rounds.get()
    }

    /// Force one exact MaxSMT final-accounting value for a fail-closed canary.
    #[cfg(test)]
    pub(crate) fn force_maxsmt_exact_cost_for_test(&self, cost: u64) {
        self.forced_maxsmt_exact_cost.set(Some(cost));
    }

    /// Inject one non-assumption OLL core literal for a fail-closed canary.
    #[cfg(test)]
    pub(crate) fn force_maxsmt_oll_core_anomaly_for_test(&self) {
        self.forced_maxsmt_oll_core_anomaly.set(true);
    }

    /// Corrupt the final MaxSMT witness once, after SAT emission, to prove that
    /// public soft accounting is bound to the final consumer-visible model.
    #[cfg(test)]
    pub(crate) fn force_maxsmt_post_emit_soft_flip_for_test(&self) {
        self.forced_maxsmt_post_emit_soft_flip.set(true);
    }

    /// Corrupt one finite LIA objective after SAT emission to prove that public
    /// optimization outcomes are bound to the final consumer-visible model.
    #[cfg(test)]
    pub(crate) fn force_optimization_post_emit_objective_flip_for_test(&self) {
        self.forced_optimization_post_emit_objective_flip.set(true);
    }

    /// Test-only: record whether the Phase 5 diff-logic engine decided the most
    /// recent solve. No-op outside tests.
    pub(crate) fn record_diff_logic_decided_for_test(&self, decided: bool) {
        #[cfg(test)]
        self.last_diff_logic_decided.set(decided);
        #[cfg(not(test))]
        let _ = decided;
    }

    /// Test-only: whether the Phase 5 diff-logic engine decided the last solve.
    #[cfg(test)]
    pub(crate) fn last_diff_logic_decided_for_test(&self) -> bool {
        self.last_diff_logic_decided.get()
    }

    /// Access the trail provenance data from the last SAT result (#8153, #8307).
    pub(crate) fn last_trail_provenance(&self) -> Option<&HashMap<u32, (u32, bool, Vec<u32>)>> {
        self.last_trail_provenance.as_ref()
    }

    /// Access the var-to-term mapping from the last Tseitin encoding (#8307).
    ///
    /// Maps 0-based SAT variable index to TermId. Used by `model_provenance()`
    /// to convert reason clause variable indices back to `Term` handles.
    pub(crate) fn last_var_to_term(&self) -> Option<&HashMap<u32, TermId>> {
        self.last_var_to_term.as_ref()
    }

    /// Look up the SAT variable index for a term ID from the last model (#8153).
    pub(crate) fn last_model_term_to_var(&self, term_id: TermId) -> Option<u32> {
        self.last_model.as_ref()?.term_to_var.get(&term_id).copied()
    }

    /// Capture trail provenance from the persistent SAT solver (#8153, #8307).
    ///
    /// Called after check-sat returns SAT, when pipeline borrows are released.
    /// Queries `incr_theory_state.persistent_sat` (or `lia_persistent_sat`)
    /// for each variable in the model's `term_to_var` mapping.
    ///
    /// For propagated variables, also captures the reason clause's antecedent
    /// variable indices so that `model_provenance()` can populate
    /// `antecedent_terms` with real data instead of an empty vec.
    pub(crate) fn capture_trail_provenance(&mut self) {
        let model = match self.last_model.as_ref() {
            Some(m) => m,
            None => return,
        };
        let sat = self
            .incr_theory_state
            .as_ref()
            .and_then(|s| s.persistent_sat.as_ref().or(s.lia_persistent_sat.as_ref()));
        let sat = match sat {
            Some(s) => s,
            None => return,
        };
        let mut provenance = HashMap::default();
        let sat_num_vars = sat.total_num_vars();
        for (_, &var_idx) in &model.term_to_var {
            // Optimization blocking constraints may introduce variables beyond
            // the persistent SAT solver's variable count (#8515). Skip them to
            // avoid out-of-bounds access in var_level/var_assignment_kind.
            if (var_idx as usize) >= sat_num_vars {
                continue;
            }
            let var = ay_sat::Variable::new(var_idx);
            if let Some(level) = sat.var_level(var) {
                let kind = sat.var_assignment_kind(var);
                let is_propagated = kind == ay_sat::VarAssignmentKind::Propagated;
                let antecedents = if is_propagated {
                    sat.var_reason_variable_indices(var).unwrap_or_default()
                } else {
                    vec![]
                };
                provenance.insert(var_idx, (level, is_propagated, antecedents));
            }
        }
        self.last_trail_provenance = Some(provenance);
    }

    // DT axiom generation functions (dt_selector_axioms, dt_acyclicity_depth_axioms,
    // dt_occurs_check_unsat_from_equalities) moved to executor/dt_axioms.rs.

    /// Execute a sequence of commands
    ///
    /// Returns outputs for each command that produces output.
    #[must_use = "command results must be checked — errors indicate parse/solve failures"]
    pub fn execute_all(&mut self, commands: &[Command]) -> Result<Vec<String>> {
        let mut outputs = Vec::new();
        for cmd in commands {
            if let Some(output) = self.execute(cmd)? {
                outputs.push(output);
            }
        }
        Ok(outputs)
    }

    // check_sat, check_sat_interruptible, check_sat_guarded, set_interrupt,
    // set_timeout, set_solve_controls, clear_solve_controls, make_should_stop,
    // should_abort_theory_loop, check_sat_internal, route_to_solver:
    // moved to executor/check_sat.rs

    /// Get the current logic
    pub fn logic(&self) -> Option<&str> {
        self.ctx.logic()
    }

    /// Get the number of assertions
    pub fn assertion_count(&self) -> usize {
        self.ctx.assertions.len()
    }

    /// Get the last check-sat result.
    ///
    /// Read-only accessor for the result of the last solve call. The result
    /// was validated during solve (via `finalize_sat_model_validation()`).
    /// This accessor does not bypass verification — it reads an already-validated value.
    ///
    /// `pub(crate)`: External consumers use `api::Solver::last_result()` or the
    /// narrow `last_result_is_unsat()` predicate. Part of #5787 (Phase 6).
    pub(crate) fn last_result(&self) -> Option<&SolveResult> {
        self.last_result.as_ref()
    }

    /// Returns `true` if the last check-sat call returned UNSAT.
    ///
    /// Narrow predicate for callers that only need a boolean check
    /// (e.g., proof file writing) without matching on `SolveResult` variants.
    pub fn last_result_is_unsat(&self) -> bool {
        self.last_result.as_ref().is_some_and(SolveResult::is_unsat)
    }

    /// Returns `true` if the last check-sat call returned SAT.
    ///
    /// Narrow predicate mirroring [`Self::last_result_is_unsat`]. Note that
    /// assertion-stack mutations (`push`/`pop`/`assert`/`reset`) invalidate
    /// the last result, after which all three `last_result_is_*` predicates
    /// return `false`. Callers presenting the verdict to users (e.g.
    /// `--explain`) must handle that no-result state explicitly instead of
    /// defaulting to SAT.
    pub fn last_result_is_sat(&self) -> bool {
        self.last_result.as_ref().is_some_and(SolveResult::is_sat)
    }

    /// Returns `true` if the last check-sat call returned UNKNOWN.
    pub fn last_result_is_unknown(&self) -> bool {
        self.last_result
            .as_ref()
            .is_some_and(SolveResult::is_unknown)
    }

    /// Structured reason for the last Unknown result.
    ///
    /// Returns the reason why the solver returned Unknown, if available.
    /// Returns `None` if the last result was not Unknown or if no reason was recorded.
    #[must_use]
    pub fn unknown_reason(&self) -> Option<UnknownReason> {
        match self.last_result {
            Some(SolveResult::Unknown) => self.last_unknown_reason,
            _ => None,
        }
    }

    /// True when `finalize_sat_model_validation` actually ran and passed
    /// on the last solve call (#5903).
    pub(crate) fn was_model_validated(&self) -> bool {
        self.last_model_validated
    }

    /// Take the [`SatCertificate`](model::sat_emit::SatCertificate) minted by the
    /// last `emit_sat_verdict` funnel run, if the last emitted verdict was `Sat`.
    ///
    /// The API boundary calls this to build a public `Sat` `VerifiedSolveResult`;
    /// because the certificate can only be minted inside `emit_sat_verdict`, a
    /// `Sat` that never went through the funnel yields `None` here and is
    /// fail-closed to `Unknown` at the boundary (#sat-chokepoint).
    pub(crate) fn take_sat_certificate(&mut self) -> Option<SatCertificate> {
        self.last_sat_certificate.take()
    }

    /// Return the admitted MaxSMT accounting for the current SAT result.
    ///
    /// The violated indices were captured from the temporary relaxation
    /// indicators before those internal symbols were removed. `None` means the
    /// current result is not an admitted MaxSMT witness.
    pub(crate) fn last_maxsmt_outcome(&self) -> Option<(u64, bool, &[usize])> {
        Some((
            self.last_soft_cost?,
            self.last_soft_cost_optimal,
            self.last_soft_violations.as_deref()?,
        ))
    }

    /// Test-only hook for consumer-boundary model extraction canaries.
    #[cfg(test)]
    pub(crate) fn set_model_validated_for_testing(&mut self, validated: bool) {
        self.last_model_validated = validated;
    }

    /// Get statistics from the last check-sat call
    ///
    /// Returns statistics about the solving process including:
    /// - SAT-level stats: conflicts, decisions, propagations, restarts
    /// - Theory-level stats: theory conflicts and propagations
    /// - Problem size: variables, clauses, assertions
    ///
    /// # Example
    ///
    /// ```no_run
    /// use ay_dpll::Executor;
    ///
    /// let mut exec = Executor::new();
    /// // ... setup and check_sat ...
    /// let stats = exec.statistics();
    /// println!("Conflicts: {}", stats.conflicts);
    /// println!("Decisions: {}", stats.decisions);
    /// ```
    #[must_use]
    pub fn statistics(&self) -> &Statistics {
        &self.last_statistics
    }

    /// Alias for `statistics()` (backward compat with tests).
    #[must_use]
    pub fn get_statistics(&self) -> &Statistics {
        &self.last_statistics
    }

    /// Return the reason for the last `Unknown` result, if any.
    #[must_use]
    pub fn get_reason_unknown(&self) -> Option<UnknownReason> {
        self.last_unknown_reason
    }

    // produce_assignments_enabled, produce_unsat_cores_enabled, get_assignment,
    // get_unsat_core, get_unsat_assumptions moved to executor/commands.rs
    // get_proof and produce_proofs_enabled moved to executor/proof.rs
}

#[cfg(test)]
mod pop_underflow_tests {
    use super::*;
    use std::panic::{catch_unwind, AssertUnwindSafe};

    fn assert_scope_underflow(result: Result<Option<String>>) {
        assert!(
            matches!(
                result,
                Err(ExecutorError::Elaborate(
                    ay_frontend::ElaborateError::ScopeUnderflow
                ))
            ),
            "expected scope underflow, got {result:?}"
        );
    }

    #[test]
    fn executor_pop_without_push_returns_error_without_unwind() {
        let mut exec = Executor::new();

        let unwind = catch_unwind(AssertUnwindSafe(|| exec.execute(&Command::Pop(1))));

        assert!(unwind.is_ok(), "empty pop must not panic");
        assert_scope_underflow(unwind.expect("checked above"));

        exec.execute(&Command::Push(1))
            .expect("push after failed pop should succeed");
        exec.execute(&Command::Pop(1))
            .expect("balanced pop after failed pop should succeed");
    }

    #[test]
    fn executor_pop_too_many_returns_error_without_unwind() {
        let mut exec = Executor::new();
        exec.execute(&Command::Push(1))
            .expect("push should succeed");

        let unwind = catch_unwind(AssertUnwindSafe(|| exec.execute(&Command::Pop(2))));

        assert!(unwind.is_ok(), "oversized pop must not panic");
        assert_scope_underflow(unwind.expect("checked above"));

        exec.execute(&Command::Pop(1))
            .expect("failed oversized pop should leave the scope available");
    }

    #[test]
    fn executor_misaligned_subsystem_pop_returns_error_without_unwind() {
        let mut exec = Executor::new();
        exec.execute(&Command::Push(1))
            .expect("push should succeed");

        IncrementalSubsystem::reset(&mut exec.proof_tracker);

        let unwind = catch_unwind(AssertUnwindSafe(|| exec.execute(&Command::Pop(1))));

        assert!(
            unwind.is_ok(),
            "misaligned proof tracker pop must not panic"
        );
        assert_scope_underflow(unwind.expect("checked above"));
    }
}
