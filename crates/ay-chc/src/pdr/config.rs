// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PDR solver configuration types.

use crate::cancellation::CancellationToken;
use crate::lemma_hints::{HintProviders, LemmaHint};
use crate::{ChcExpr, ChcSort};

/// Stable internal label for the arithmetic PDR/Farkas route diagnostics.
pub(crate) const LIA_FARKAS_PROFILE_NAME: &str = "lia_farkas";

/// Integer bounds tracking for init constraint analysis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct InitIntBounds {
    pub(crate) min: i128,
    pub(crate) max: i128,
}

impl InitIntBounds {
    pub(crate) fn new(v: i128) -> Self {
        Self { min: v, max: v }
    }

    /// Create bounds representing an unbounded range (for use before any constraints are added)
    pub(crate) fn unbounded() -> Self {
        Self {
            min: i128::MIN,
            max: i128::MAX,
        }
    }

    pub(crate) fn update(&mut self, v: i128) {
        self.min = self.min.min(v);
        self.max = self.max.max(v);
    }

    /// Update only the lower bound (var >= lb)
    pub(crate) fn update_lower(&mut self, lb: i128) {
        self.min = self.min.max(lb);
    }

    /// Update only the upper bound (var <= ub)
    pub(crate) fn update_upper(&mut self, ub: i128) {
        self.max = self.max.min(ub);
    }

    /// Check if this represents a valid (non-empty) range
    pub(crate) fn is_valid(&self) -> bool {
        self.min <= self.max
    }
}

/// Arithmetic template surfaces enabled for the internal LIA/Farkas profile.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct LiaFarkasTemplateSurface {
    pub(crate) affine_equalities: bool,
    pub(crate) intervals: bool,
    pub(crate) difference_bounds: bool,
    pub(crate) scaled_linear_combinations: bool,
}

impl LiaFarkasTemplateSurface {
    pub(crate) fn enabled_count(self) -> usize {
        [
            self.affine_equalities,
            self.intervals,
            self.difference_bounds,
            self.scaled_linear_combinations,
        ]
        .into_iter()
        .filter(|enabled| *enabled)
        .count()
    }
}

/// Oracle backend of the Spacer lane (`DESIGN_spacer_pob_lemma_pipeline.md` §3.4).
///
/// `Session` records the requested incremental route. The current oracle
/// retains the legacy query path, and the selection degrades to `Legacy` while
/// `PdrSolver::incremental_pdr_enabled()` is `false`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OracleBackend {
    /// Non-incremental `SmtContext` verdicts + proxied assumption cores (D1).
    Legacy,
    /// Rung-5 incremental-session route label (R4).
    Session,
}

/// Literal order of the Phase B drop round (`DESIGN` §4.2.3, §7.3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DropOrder {
    /// Pins (`v = c`), then var–var equalities, then bounds, Booleans last.
    PinsFirst,
    /// The cube's own literal order (A/B row).
    CubeOrder,
}

/// The Spacer-faithful POB/lemma lane (Workstream B; `DESIGN` §3.7).
///
/// Rung 2 by default (R3, the default flip; `ab_switches::ChcAbSwitches`).
/// When `enabled` is false every other field is ignored and the solver is
/// behaviourally identical to the legacy pipeline (lock L-V).
/// `PdrSolver::new` derives `spacer_core` from `enabled` and the problem's
/// sorts (arrays / BV / datatypes bypass the lane, §7.4).
///
/// Owner: WP-B1-S. Flags are cumulative rung presets (`rung`) with per-flag
/// overrides from `ab_switches` (`--chc-spacer-*`).
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct SpacerLane {
    /// Master switch (== B1's `spacer_core`); false ⇒ every other field ignored.
    pub enabled: bool,
    /// R2: `CubeMode::Free` (implicant of `T ∧ post`, no augmentation, minimiser off).
    pub free_pob: bool,
    /// R2: BJ-exact LIA bounds path + model-based LRA projection (default = `free_pob`).
    pub mbp_exact_lia: bool,
    /// R1: seed = `¬core` (proxied cores); off ⇒ seed = full cube (still lemma-always).
    pub core_lemma: bool,
    /// R1: Phase B/D inductive generalisation; off ⇒ lemma = `¬seed`.
    pub ind_gen: bool,
    /// R5: Phase C weakening rounds.
    pub ind_gen_weaken: bool,
    /// D1 confirmation of adopted cores; default true until the retirement metric holds.
    pub confirm_cores: bool,
    /// Oracle-call cap per derivation: 64 legacy / 256 session.
    pub ind_gen_max_queries: usize,
    /// Share of the remaining solve time one derivation may spend (0.4).
    pub ind_gen_time_share: f32,
    /// Phase D climb depth on the legacy backend (default 1).
    pub eager_push_levels: usize,
    /// QuickXplain switches to a linear loop below this literal count (16).
    pub ddmin_min_lits: usize,
    /// Phase B literal order.
    pub drop_order: DropOrder,
    /// R1: the two enumeration exits (`MAX_POINT_BLOCKS_PER_LEVEL`,
    /// `MAX_LEVEL0_BLOCKED`) become counters instead of `Unknown`.
    pub lift_caps: bool,
    /// Sequential lanes only: `Unknown` after this many point-block lemmas per
    /// level (default `None`; today's code uses 25).
    pub enum_valve: Option<usize>,
    /// Keep the already-blocked SMT pre-check (default false; measured in R1).
    pub already_blocked_fastpath: bool,
    /// R2 sub-flag: keep `false` lemmas in model extraction (§7.5 test).
    pub false_lemma_in_model: bool,
    /// Query backend (R4).
    pub backend: OracleBackend,
    /// Session `Unknown` → legacy verdict path.
    pub session_fallback: bool,
    /// The lane also runs on NONLINEAR problems (hyperedge clauses): every
    /// predicate is blocked by the lane, a hyperedge clause's query conjoins
    /// every body atom's frame (Spacer's may summaries), children come from
    /// the free MBP constructor with the other atoms' summaries as context,
    /// and reachability is tracked by concrete reach facts (Spacer's must
    /// summaries), from which counterexample trees are built. Requires
    /// `free_pob`. Off ⇒ nonlinear problems bypass the lane (the legacy
    /// profile, `lane_bypassed.nonlinear`).
    pub nonlinear: bool,
}

impl Eq for SpacerLane {}

impl SpacerLane {
    /// Everything off; the legacy pipeline (validators are pinned to this, S10).
    pub const OFF: Self = Self {
        enabled: false,
        free_pob: false,
        mbp_exact_lia: false,
        core_lemma: false,
        ind_gen: false,
        ind_gen_weaken: false,
        confirm_cores: true,
        ind_gen_max_queries: 64,
        ind_gen_time_share: 0.4,
        eager_push_levels: 1,
        ddmin_min_lits: 16,
        drop_order: DropOrder::PinsFirst,
        lift_caps: false,
        enum_valve: None,
        already_blocked_fastpath: false,
        false_lemma_in_model: false,
        backend: OracleBackend::Legacy,
        session_fallback: true,
        nonlinear: false,
    };

    /// Cumulative rung presets (`DESIGN` §4.5 / §8.4).
    ///
    /// 0 = OFF; 1 = `enabled, core_lemma, ind_gen, confirm_cores, lift_caps,
    /// false_lemma_in_model`; 2 = + `free_pob, mbp_exact_lia, nonlinear`; 3 = the same
    /// flags (R3 is the default flip, a config-selection concern); 4 = +
    /// `backend = Session` (256 queries); 5 = + `ind_gen_weaken`. Values above
    /// 5 clamp to 5.
    ///
    /// `false_lemma_in_model` is on from rung 1 (amendment to §7.5, WP-S
    /// 2026-09-23): every `false` lemma of the lane is backed by an observed
    /// UNSAT of all defining clauses of its predicate (Phase 0 on the empty
    /// seed), so `false` at level k is the proven fact "the predicate has no
    /// state reachable in ≤ k steps". Filtering it out of the frame
    /// hypothesis the model is built from (#3121, a legacy guard against
    /// UNPROVEN `false` lemmas) interprets an unreachable predicate as `true`
    /// and makes every fixed-point model fail its query clause — HOLA-44's 47
    /// demotions (`spacer_false_lemma_fixed_point` locks the fix).
    #[must_use]
    pub fn rung(n: u8) -> Self {
        let mut lane = Self::OFF;
        if n == 0 {
            return lane;
        }
        lane.enabled = true;
        lane.core_lemma = true;
        lane.ind_gen = true;
        lane.confirm_cores = true;
        lane.lift_caps = true;
        lane.false_lemma_in_model = true;
        if n >= 2 {
            lane.free_pob = true;
            lane.mbp_exact_lia = true;
            lane.nonlinear = true;
        }
        if n >= 4 {
            lane.backend = OracleBackend::Session;
            lane.ind_gen_max_queries = 256;
        }
        if n >= 5 {
            lane.ind_gen_weaken = true;
        }
        lane
    }

    /// The rung this flag set corresponds to (for the verbose/trace header).
    #[must_use]
    pub fn rung_label(&self) -> u8 {
        if !self.enabled {
            return 0;
        }
        if self.ind_gen_weaken {
            5
        } else if self.backend == OracleBackend::Session {
            4
        } else if self.free_pob {
            2
        } else {
            1
        }
    }

    /// Normalise an overridden flag set.
    ///
    /// `enabled == false` ⇒ `OFF` (every other field ignored); `lift_caps`
    /// is refused without `enabled && core_lemma` (the caps are the legacy
    /// pipeline's only defence against enumeration); `mbp_exact_lia` follows
    /// `free_pob` unless set explicitly (callers pass the post-override set).
    #[must_use]
    pub fn validate(mut self, verbose: bool) -> Self {
        if !self.enabled {
            if verbose && self != Self::OFF {
                safe_eprintln!("PDR-SPACER: lane disabled; ignoring the other spacer flags");
            }
            return Self::OFF;
        }
        if self.lift_caps && !self.core_lemma {
            if verbose {
                safe_eprintln!(
                    "PDR-SPACER: refusing lift_caps without core_lemma (enumeration exits stay)"
                );
            }
            self.lift_caps = false;
        }
        if self.ind_gen_max_queries == 0 {
            self.ind_gen_max_queries = 1;
        }
        if self.nonlinear && !self.free_pob {
            // The nonlinear lane builds every child with the free MBP
            // constructor (the other body atoms' summaries are its context).
            if verbose {
                tracing::info!("PDR-SPACER: refusing nonlinear without free_pob");
            }
            self.nonlinear = false;
        }
        if !(0.0..=1.0).contains(&self.ind_gen_time_share) {
            self.ind_gen_time_share = 0.4;
        }
        self
    }

    /// The lane selected by the process-wide A/B switches
    /// (`--chc-spacer-rung N`, default 2, + per-flag overrides on top of that
    /// rung). Rung 0 is the legacy pipeline whatever the overrides say.
    #[must_use]
    pub(crate) fn from_ab_switches(switches: &crate::ab_switches::ChcAbSwitches) -> Self {
        let mut lane = Self::rung(switches.spacer_rung);
        if !lane.enabled {
            return Self::OFF;
        }
        if let Some(v) = switches.spacer_free_pob {
            lane.free_pob = v;
            lane.mbp_exact_lia = v;
        }
        if let Some(v) = switches.spacer_core_lemma {
            lane.core_lemma = v;
        }
        if let Some(v) = switches.spacer_ind_gen {
            lane.ind_gen = v;
        }
        if let Some(v) = switches.spacer_confirm_cores {
            lane.confirm_cores = v;
        }
        if let Some(v) = switches.spacer_lift_caps {
            lane.lift_caps = v;
        }
        if let Some(v) = switches.spacer_nonlinear {
            lane.nonlinear = v;
        }
        if let Some(v) = switches.spacer_session {
            lane.backend = if v {
                OracleBackend::Session
            } else {
                OracleBackend::Legacy
            };
            if v {
                lane.ind_gen_max_queries = lane.ind_gen_max_queries.max(256);
            }
        }
        lane.validate(false)
    }
}

impl Default for SpacerLane {
    fn default() -> Self {
        Self::OFF
    }
}

/// PDR solver configuration
///
/// Techniques are enabled by default (except where disabled due to known
/// regressions/timeouts). The solver decides what to use based on the problem
/// structure; avoid treating internal technique toggles as stable user-facing
/// configuration knobs.
#[derive(Debug, Clone)]
pub struct PdrConfig {
    /// Maximum number of frames before giving up
    pub max_frames: usize,
    /// Maximum number of iterations
    pub max_iterations: usize,
    /// Maximum number of processed proof obligations in a single strengthen() call before giving up
    pub max_obligations: usize,
    /// Enable verbose logging
    pub verbose: bool,
    /// Strict proof mode: trust-proof fallbacks become errors (#8555).
    ///
    /// When true, model verification fails if any concrete cross-check is
    /// skipped due to budget exhaustion. This ensures no trust-proof fallback
    /// is silently accepted during internal PDR verification.
    pub(crate) strict_proofs: bool,
    /// Enable runtime TLA trace emission for top-level solve entrypoints.
    ///
    /// This guard prevents sub-solver instances (portfolio validation, retries,
    /// case-split branches) from reopening/truncating the shared trace file.
    pub(crate) enable_tla_trace: bool,
    /// Trace output path captured from the top-level environment.
    ///
    /// This lets top-level CHC trace mode reserve `AY_TRACE_FILE` for the PDR
    /// trace itself while temporarily suppressing nested SAT/DPLL trace writers
    /// that would otherwise corrupt the same JSONL file.
    pub(crate) tla_trace_path: Option<String>,
    /// Cancellation token for cooperative stopping (portfolio solving)
    pub cancellation_token: Option<CancellationToken>,
    /// External cancellation observer that does not imply a solve budget.
    ///
    /// Adaptive unbounded PDR lanes use this token so embedding callers can
    /// stop them without changing the historical search policy selected by
    /// `cancellation_token.is_some()` / `solve_timeout.is_some()` checks.
    pub(crate) external_cancellation_token: Option<CancellationToken>,
    /// Opt-in early hopeless self-report (wishlist item 5a).
    ///
    /// When true AND the convergence monitor reports `ConvergenceHealth::Stuck`
    /// (all generalization escalation exhausted, sustained stagnation), the
    /// main loop returns `Unknown` early with `terminated_by_stagnation` set as
    /// the stagnation evidence, instead of burning the rest of its budget.
    ///
    /// DEFAULT false: the default "log but continue" behavior is deliberate —
    /// premature stagnation abort regresses under high system load where
    /// wall-clock stall detection fires before the solver has had enough CPU
    /// time (see main_loop.rs Stuck arm). Set this ONLY from scheduler
    /// contexts that have another lane to try (sequential portfolio mode with
    /// a successor engine; adaptive staged strategies with a subsequent
    /// stage), where the released budget is immediately reused.
    ///
    /// SOUNDNESS: early Unknown can never flip a Safe/Unsafe verdict.
    pub(crate) give_up_on_stuck: bool,
    /// Wall-clock timeout for the entire solve() call (including startup).
    /// When set, the solver returns Unknown if this deadline is exceeded.
    /// Under an [`effort`](Self::effort) it is a backstop: a run it ends
    /// publishes `Deadline` as its stop, never the count's `Rlimit`. Until P4a
    /// slices 9 and 10 it also still sizes clocks the search meets on its way
    /// (the case split's deadline and branch budgets, the thread's solve
    /// deadline that clamps each query's slice; the development design notes
    /// §14).
    pub solve_timeout: Option<std::time::Duration>,
    /// Finite per-context term-store ceiling, intersected with inherited caps.
    /// Not aggregate PDR/AST/model memory or a hard process-RSS reservation.
    pub(crate) memory_budget: Option<usize>,
    /// The proof run's tick budget B, in ay-sat search ticks (the development design notes
    /// DR-37: one tick budget, every other bound a draw on it; P4a slice 8,
    /// the development design notes §14). `None`, the default: the run is as it
    /// was, and its meter decides nothing.
    ///
    /// Read by the proof-run entry points (`engines::solve_pdr_proof` and its
    /// forms, `engines::prove_external_invariant_model`). With `Some(B)` the
    /// run is a GuardTree node allotted B: every SAT solve, SMT entry, DPLL(T)
    /// round, PDR iteration and processed obligation is charged to it, the
    /// run stops (`unknown`) once it has spent B, and the frame, iteration and
    /// obligation caps are not armed. Its sub-checks stay on ay-chc's own
    /// counted path (no executor route), no BMC runs in it (the bounded unsafe
    /// precheck, the acyclic certificate, a counterexample's bounded replay:
    /// `BmcSolver::closed_under_effort`), the frame-stall window is measured
    /// in ticks, and a result decided within B is never discarded for a clock
    /// that passed. The wall clocks this field does not yet remove (the
    /// per-query slices, the case-split and validation clocks) stay; they are
    /// P4a slices 9 and 10's. `Some(0)` stops at the first charge.
    pub effort: Option<u64>,
    /// Disable PDR's internal array-argument scalarization.
    ///
    /// Portfolio validation uses backtranslated models over the original
    /// predicate signatures, so the verifier must not rewrite the problem's
    /// Array arguments out from under those interpretations.
    pub(crate) disable_array_scalarization: bool,
    /// Extra finite array keys learned by an outer abstraction/refinement loop.
    ///
    /// These indices are merged into PDR's usual constant-select scalarization
    /// when array scalarization is enabled. The solver still validates any Safe
    /// model on the unscalarized entry problem before returning it.
    pub(crate) array_scalarization_extra_indices: Vec<(ChcSort, ChcExpr)>,
    /// Keep finite constant array keys even when the same array key sort also
    /// has symbolic selects/stores.
    ///
    /// This is a CEGAR/profile knob for array-heavy CHC routes. It is only
    /// proof-grade because PDR backtranslates the scalarized model and validates
    /// it against the original, unscalarized clauses before returning SAFE.
    pub(crate) array_scalarization_keep_const_keys_with_symbolic_accesses: bool,
    /// Preserve original clauses for counterexample/model verification.
    ///
    /// Generated witnesses use original CHC clause indices. Validation solvers
    /// must not expand nullary fail predicates or split OR/ITE clauses before
    /// checking those witnesses, or the indices and predicate applications stop
    /// referring to the certificate that was produced.
    pub(crate) preserve_original_clauses: bool,
    /// Disable the bounded-BMC counterexample replay inside
    /// `verify_counterexample_without_witness` (inc-9).
    ///
    /// Set by validation contexts that themselves serve as the replay's trust
    /// anchor (the replay helper's own witness verification, BMC's
    /// `verified_unsafe_from_witness`), so cex verification can never recurse
    /// into another BMC replay.
    pub(crate) disable_cex_replay: bool,

    // Technique toggles below are internal. They exist for A/B testing and
    // portfolio-style runs, but are not intended as user-facing knobs.
    /// Enable model-based projection for predecessor generalization
    pub(crate) use_mbp: bool,
    /// Enable under-approximations (must summaries) for faster convergence
    pub(crate) use_must_summaries: bool,
    /// Enable level-priority POB ordering (Spacer technique)
    pub(crate) use_level_priority: bool,
    /// Enable mixed summaries for hyperedges (Spacer technique)
    pub(crate) use_mixed_summaries: bool,
    /// Enable derivation tracking for hyperedges (Spacer derivation technique).
    /// When enabled, creates Derivation objects to track progress through all body
    /// predicates of multi-body clauses, enabling more efficient multi-predicate solving.
    /// #1275: Scaffolding for derivation tracking.
    pub(crate) use_derivations: bool,
    /// Enable range-based inequality weakening in generalization
    pub(crate) use_range_weakening: bool,
    /// Enable init-bound weakening in generalization
    pub(crate) use_init_bound_weakening: bool,
    /// Enable Farkas combination for linear constraints in generalization
    pub(crate) use_farkas_combination: bool,
    /// Enable relational equality generalization
    pub(crate) use_relational_equality: bool,
    /// Enable interpolation-based lemma learning (Golem/Spacer technique)
    pub(crate) use_interpolation: bool,
    /// Enable convex closure for multi-lemma generalization (Z3 Spacer technique)
    pub(crate) use_convex_closure: bool,
    /// Enable GSpacer-style queued MAY proof obligations (CAV'20 global
    /// guidance): SUBSUME/CONJECTURE candidates that fail inline
    /// inductiveness are posted as gas-budgeted may-pobs for the full engine
    /// to prove. Requires `use_convex_closure` (the cluster machinery).
    /// Runtime kill switch: `AY_CHC_MAY_POB=0`.
    ///
    /// SOUNDNESS: may-pobs only ever add lemmas through the standard
    /// inductiveness-checked blocking path and never contribute to
    /// counterexample reconstruction (guards in `pdr/solver/strengthen.rs`).
    pub(crate) use_may_pobs: bool,
    /// Enable negated equality splitting in `can_push_lemma`: ¬(a = b) → (a < b) ∨ (a > b).
    ///
    /// Helps dillig-style benchmarks with relational invariants (e.g., D = 2*E)
    /// but doubles SMT queries, causing timeouts on multi-predicate problems.
    /// Portfolio runs PDR with both configs (#491).
    pub(crate) use_negated_equality_splits: bool,

    /// Enable Luby sequence restarts based on learned lemma count (#1270).
    ///
    /// When lemma growth stalls (many lemmas learned without progress), restart
    /// clears the obligation queue to break out of unproductive search branches.
    /// Reference: Z3 Spacer `spacer_context.cpp:3232-3244`.
    pub(crate) use_restarts: bool,

    /// Initial restart threshold (default: 10, per Z3 Spacer).
    ///
    /// After `restart_initial_threshold` lemmas are learned since last restart,
    /// the threshold is multiplied by the next Luby sequence value.
    pub(crate) restart_initial_threshold: usize,

    /// Enable POB push mechanism for faster lemma propagation (#1269).
    ///
    /// When a POB is blocked by existing lemmas, instead of discarding it,
    /// increment its level and re-add to the queue. This propagates lemmas
    /// to higher levels faster and discovers fixed points earlier.
    /// Reference: Z3 Spacer `spacer_context.cpp:3532-3540`.
    pub(crate) use_pob_push: bool,

    /// Maximum depth for POB push (default: usize::MAX, matching Spacer).
    ///
    /// POBs are only pushed if their depth is less than this limit.
    /// Depth tracks how many times a POB has been pushed.
    pub(crate) push_pob_max_depth: usize,

    /// User-provided hints injected at runtime (e.g., from model-checker-consumer loop invariants).
    ///
    /// These hints are merged with built-in hint providers during `apply_lemma_hints`.
    /// Default: empty vector.
    pub user_hints: Vec<LemmaHint>,

    /// Cross-engine lemma pool from a previous PDR stage (#7919).
    ///
    /// When the non-inlined PDR stage returns Unknown, its learned lemmas are
    /// captured in a `LemmaPool` and passed here. During `solve_init()`, these
    /// are converted to `LemmaHint` entries and merged into `user_hints` so
    /// that the built-in hint validation pipeline handles them.
    pub(crate) lemma_hints: Option<crate::lemma_pool::LemmaPool>,

    /// Shared lemma cache for sequential portfolio runs (#7919).
    pub(crate) lemma_cache: Option<crate::lemma_cache::LemmaCache>,

    /// User-provided runtime hint providers.
    ///
    /// These are called alongside the built-in static providers during
    /// `apply_lemma_hints`. Providers are owned via `Arc` for thread safety
    /// in portfolio solving. Default: empty.
    pub user_hint_providers: HintProviders,

    /// Cooperative blackboard for cross-engine lemma sharing (#7910).
    ///
    /// When set (portfolio parallel mode), PDR publishes learned lemmas to
    /// the blackboard at restarts. Other engines consume via their
    /// `BlackboardHintProvider` in `user_hint_providers`.
    pub(crate) blackboard: Option<std::sync::Arc<crate::blackboard::SharedBlackboard>>,

    /// Engine index in the portfolio, used for blackboard publish tagging.
    /// Set by the portfolio scheduler; 0 by default for standalone use.
    pub(crate) engine_idx: usize,

    /// Enable Entry-CEGAR discharge loop for predecessor reachability (#1615).
    ///
    /// When true (default), if an invariant candidate fails entry-inductiveness
    /// because a predecessor state is SAT, PDR attempts to prove the predecessor
    /// unreachable via a CEGAR discharge loop. This helps phase-chain benchmarks
    /// (gj2007 pattern) but adds overhead that causes timeouts on other benchmarks.
    ///
    /// When false, PDR conservatively rejects invariants with reachable-looking
    /// predecessors and tries different candidates instead. This recovers performance
    /// on benchmarks that don't benefit from Entry-CEGAR.
    ///
    /// See: the development design notes
    pub(crate) use_entry_cegar_discharge: bool,

    /// Enable startup discovery of scaled difference bounds (`B - k*A >= c`).
    ///
    /// This is powerful on some multi-predicate arithmetic benchmarks but can add
    /// substantial startup overhead on simple-loop problems where most candidates
    /// are quickly rejected.
    pub(crate) use_scaled_difference_bounds: bool,

    /// Enable built-in lemma hint providers at startup/restart.
    ///
    /// Hints are optional heuristics. Disabling them reduces SMT workload on
    /// some benchmarks with large candidate spaces.
    pub(crate) use_lemma_hints: bool,

    /// BV bit-group information from BvToBool preprocessing (#5877).
    ///
    /// When BvToBool expands BV-sorted predicate arguments into individual Bool
    /// arguments, this field records the grouping so that PDR's generalization
    /// can try dropping entire BV groups at once (all 32 bits of a BV32 variable)
    /// instead of one bit at a time.
    ///
    /// Each entry is `(start_arg_index, bit_width)` for a single original BV
    /// argument. For example, if the original predicate was `P(Bool, BV32, Int)`,
    /// after BvToBool it becomes `P(Bool, Bool*32, Int)` — 34 args. The bit group
    /// would be `vec![(1, 32)]` meaning args 1..33 are bits of one BV32 variable.
    ///
    /// Empty when BvToBool was not applied (the default).
    pub(crate) bv_bit_groups: Vec<(usize, u32)>,

    /// Legacy experimental flag for historical BvToInt-relaxed experiments
    /// (#5877). The relaxed encoding is unsound for Safe proofs under signed
    /// overflow (#6848), so production code must leave this `false`.
    pub(crate) bv_to_int_relaxed: bool,

    /// Maximum generalization escalation level (0-3). Default: 3 (all levels).
    ///
    /// For Datatype+BV problems (#7930), cap at 0: PDR generalization
    /// escalation (Farkas, range weakening, convex closure, negated equality)
    /// is unproductive for DT sorts. Without this cap, PDR spends 4x longer
    /// stagnating through 3 escalation levels before returning Unknown,
    /// starving other engines of budget.
    pub(crate) max_escalation_level: usize,

    /// Live progress snapshot for observer consumption (#8155).
    ///
    /// When set (portfolio mode with `--progress` or `--progress-json`), the
    /// PDR main loop updates this snapshot at each iteration with current
    /// frame count and total lemma count. The progress thread reads it on
    /// its 5-second cadence to emit rich progress lines.
    ///
    /// `None` in standalone / test mode -- no overhead.
    pub(crate) progress_snapshot: Option<std::sync::Arc<crate::progress::ChcProgressSnapshot>>,

    // --- Spacer-mode engine knobs (inc-12) ---
    /// Skip the startup invariant discovery pipeline entirely.
    ///
    /// Promotes the `is_quick_check_mode` early-skip (startup/mod.rs) to an
    /// explicit flag: the spacer-mode portfolio engine spends its whole
    /// window in the blocking loop, golem/Spacer style. Soundness-neutral —
    /// discovery only seeds lemmas; every Safe still passes strict final
    /// validation against the original clauses.
    pub(crate) skip_startup_discovery: bool,
    /// Interpolant-as-lemma blocking (golem Spacer.cc:328-345): accept the
    /// interpolation cascade's result without the post-hoc weakening/widening
    /// enumeration (#967 point-blocking strengthening, #816 literal-weakening
    /// ladder, #1346 equality weakening). The heuristic generalization ladder
    /// remains the fallback when interpolation fails. The init-consistency /
    /// inductiveness guard on every accepted lemma
    /// (`verify_inductiveness_or_fallback` → `is_inductive_blocking`) is
    /// unchanged.
    pub(crate) interpolant_first_blocking: bool,
    /// Spacer-faithful POB/lemma lane (Workstream B, `DESIGN` §3.7). The
    /// `Default` reads the process-wide A/B switches (`--chc-spacer-rung`,
    /// rung 2 unless the CLI asked otherwise); validators pin
    /// `SpacerLane::OFF` explicitly (S10) so the lane never reaches them.
    pub(crate) spacer: SpacerLane,
    /// Route this solver's `check_sat` calls executor-first, skipping the
    /// internal-loop slice that punts ~23% on wide-Bool transition-system
    /// queries (policy point smt/check_sat/mod.rs). Per-solver option; the
    /// global default keeps the internal-first slice.
    pub(crate) executor_first_check_sat: bool,
    /// SMT lane for this solver's context (Rung 0, CHC-COMP 2026). Default
    /// `Verification`: every validator that builds a `PdrConfig` with
    /// `strict_proofs: true, ..Default::default()` stays on the trusted lane
    /// without touching this field. Engine launch sites (portfolio
    /// `run_engine`, the adaptive LIA/Farkas solo run) set `Search`.
    pub(crate) smt_lane: crate::smt::SmtLane,
}

impl Default for PdrConfig {
    fn default() -> Self {
        // Techniques are enabled by default (batteries included).
        // Some may be disabled when known to cause regressions/timeouts.
        // The solver decides what to use based on problem structure.
        Self {
            max_frames: 20,
            max_iterations: 1000,
            max_obligations: 100_000,
            verbose: false,
            // Strict by DEFAULT (2026-07-08, wishlist rank 2): every production
            // entry point already overrides this to `true` (lib.rs:418,446,458;
            // the BV dual-lane PdrConfigs); a `false` default was a trap for new
            // callers only — a silently-accepted trust-proof fallback (#8555).
            // Config may loosen deliberately, never by omission.
            strict_proofs: true,
            enable_tla_trace: false,
            tla_trace_path: None,
            cancellation_token: None,
            external_cancellation_token: None,
            give_up_on_stuck: false, // OFF: opt-in for schedulers with another lane (item 5a)
            solve_timeout: None,
            memory_budget: None,
            effort: None,
            disable_array_scalarization: false,
            array_scalarization_extra_indices: Vec::new(),
            array_scalarization_keep_const_keys_with_symbolic_accesses: false,
            preserve_original_clauses: false,
            disable_cex_replay: false,
            // Techniques mostly ON by default
            use_mbp: true,
            use_must_summaries: true,
            use_level_priority: true,
            use_mixed_summaries: true,
            use_derivations: true, // ON: multi-body clause derivation tracking (#1275, #1398)
            use_range_weakening: true, // ON: helps with bounded problems
            use_init_bound_weakening: true,
            use_farkas_combination: true,
            use_relational_equality: true, // ON: discovers equality invariants
            use_interpolation: true,       // ON: Golem-style interpolation-based lemma learning
            use_convex_closure: true, // ON: multi-lemma generalization (circuit breaker in #107)
            use_may_pobs: true,       // ON: GSpacer queued subsume/conjecture may-pobs (agenda #6)
            use_negated_equality_splits: false, // OFF: causes timeout on multi-pred (#470)
            use_restarts: true,       // ON: Luby restarts break out of local minima (#1270)
            restart_initial_threshold: 10, // Per Z3 Spacer default
            use_pob_push: true,       // ON: POB push for faster lemma propagation (#1269)
            push_pob_max_depth: usize::MAX, // No limit, per Z3 Spacer default
            user_hints: Vec::new(),   // No runtime hints by default
            lemma_hints: None,        // No cross-engine lemma pool by default
            lemma_cache: None,        // No sequential lemma cache by default
            user_hint_providers: HintProviders::default(), // No runtime providers by default
            blackboard: None,         // No blackboard (set by portfolio parallel mode)
            engine_idx: 0,            // Default standalone index
            use_entry_cegar_discharge: true, // ON: Entry-CEGAR discharge helps gj2007 pattern
            use_scaled_difference_bounds: true,
            use_lemma_hints: true,
            bv_bit_groups: Vec::new(),
            bv_to_int_relaxed: false,
            max_escalation_level: 3, // All levels by default
            progress_snapshot: None, // No live progress by default (#8155)
            // Spacer-mode knobs (inc-12): OFF by default, set only by
            // `portfolio_spacer_variant()`.
            skip_startup_discovery: false,
            interpolant_first_blocking: false,
            executor_first_check_sat: false,
            // Workstream B lane: rung 2 unless `--chc-spacer-rung` says (§3.7).
            spacer: SpacerLane::from_ab_switches(&crate::ab_switches::get()),
            smt_lane: crate::smt::SmtLane::Verification,
        }
    }
}

/// Compute the Luby sequence value at index i (0-indexed).
///
/// The Luby sequence is: 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 2, 4, 8, ...
/// Used for restart thresholds in SAT/SMT solvers.
///
/// Reference: Luby et al. "Optimal Speedup of Las Vegas Algorithms" (1993).
pub(super) fn luby(i: u32) -> u32 {
    if i == 0 {
        return 1;
    }
    // Find k such that 2^k - 1 <= i < 2^(k+1) - 1
    let mut k = 1u32;
    while (1u32 << k).saturating_sub(1) < i + 1 {
        k += 1;
    }
    let block_size = 1u32 << k; // 2^k
    if block_size.saturating_sub(1) == i + 1 {
        // i+1 is exactly 2^k - 1, return 2^(k-1)
        1u32 << (k - 1)
    } else {
        // Recursive case: within the block
        luby(i.saturating_sub((1u32 << (k - 1)).saturating_sub(1)))
    }
}

impl PdrConfig {
    /// Create a production configuration for the CLI.
    ///
    /// Uses balanced limits to avoid runaway execution while maintaining capability:
    /// - max_frames=50: higher than default (20), sufficient for most problems
    /// - max_iterations=500: lower than default (1000) to bound runtime (#414)
    /// - max_obligations=50_000: lower than default (100k) to cap per-strengthen work
    ///
    /// Re-enables interpolation for M1 regression recovery (#816).
    pub fn production(verbose: bool) -> Self {
        Self {
            max_frames: 50,
            max_iterations: 500,
            max_obligations: 50_000,
            verbose,
            cancellation_token: None,
            // Note: interpolation is re-enabled (#816) per M1 regression recovery roadmap.
            // The 21 regressed benchmarks (39->18 score drop) are expected to improve with
            // IUC/Farkas fallback when MBP fails.
            // See: the development design notes
            use_range_weakening: false,
            use_farkas_combination: false,
            use_relational_equality: false,
            use_interpolation: true, // Re-enabled for #816 M1 recovery
            // Entry-CEGAR discharge disabled for performance (#1615).
            // The full CEGAR loop causes timeouts on 6 benchmarks.
            // The basic entry-inductiveness check is still performed.
            use_entry_cegar_discharge: false,
            ..Self::default()
        }
    }

    /// Create a production configuration with negated equality splits enabled.
    ///
    /// Intended for portfolio-style runs that want the production technique set
    /// but also want the `¬(a = b) → (a < b) ∨ (a > b)` split heuristic (#491).
    pub fn production_variant_with_splits(verbose: bool) -> Self {
        let mut config = Self::production(verbose);
        config.use_negated_equality_splits = true;
        config
    }

    /// Create the internal linear-arithmetic PDR/Farkas profile.
    ///
    /// Production PDR keeps some arithmetic generalizers disabled because they
    /// can be expensive on broad CHC-COMP mixes. This profile is used only by
    /// feature-gated arithmetic routes where the caller reserves validation
    /// time and checks the final invariant/witness on the original CHC.
    pub(crate) fn lia_farkas_profile(verbose: bool) -> Self {
        let mut config = Self::production(verbose);
        config.strict_proofs = true;
        config.disable_array_scalarization = true;
        config.preserve_original_clauses = true;
        config.use_range_weakening = true;
        config.use_init_bound_weakening = true;
        config.use_farkas_combination = true;
        config.use_relational_equality = true;
        config.use_interpolation = true;
        config.use_convex_closure = true;
        config.use_scaled_difference_bounds = true;
        config.use_lemma_hints = true;
        config.max_frames = config.max_frames.max(60);
        config.max_iterations = config.max_iterations.max(700);
        config.max_obligations = config.max_obligations.max(75_000);
        config
    }

    /// Whether this config has the safety gates required for the internal
    /// LIA/Farkas route to produce score-bearing evidence.
    pub(crate) fn is_lia_farkas_profile(&self) -> bool {
        self.strict_proofs
            && self.disable_array_scalarization
            && self.preserve_original_clauses
            && self.use_farkas_combination
            && self.use_interpolation
    }

    /// Template families available to arithmetic route diagnostics.
    pub(crate) fn lia_farkas_template_surface(&self) -> LiaFarkasTemplateSurface {
        LiaFarkasTemplateSurface {
            affine_equalities: self.use_relational_equality,
            intervals: self.use_range_weakening || self.use_init_bound_weakening,
            difference_bounds: self.use_scaled_difference_bounds,
            scaled_linear_combinations: self.use_scaled_difference_bounds
                && self.use_farkas_combination,
        }
    }

    /// Create a portfolio variant with negated equality splits enabled.
    ///
    /// Portfolio runs PDR with both negated_equality_splits on and off (#491).
    /// This escapes local maxima where one config helps dillig-style benchmarks
    /// but hurts multi-predicate problems, and vice versa.
    ///
    /// On NONLINEAR problems this variant keeps the legacy technique profile
    /// (`without_nonlinear_lane`): wherever the portfolio runs it next to
    /// `default()`, the nonlinear Spacer lane and the legacy pipeline race.
    pub fn portfolio_variant_with_splits() -> Self {
        Self {
            use_negated_equality_splits: true,
            ..Self::default()
        }
        .without_nonlinear_lane()
    }

    /// Builder: nonlinear problems bypass the Spacer lane (legacy profile);
    /// linear problems are unaffected.
    #[must_use]
    pub fn without_nonlinear_lane(mut self) -> Self {
        self.spacer.nonlinear = false;
        self
    }

    /// Spacer-mode portfolio PDR variant (inc-12).
    ///
    /// Reference behavior (golem Spacer.cc:256-294, :328-345, :357-380): no
    /// startup discovery — 100% of the window goes to the pob loop; the
    /// interpolant from one interpolating query is installed as the frame
    /// lemma at pob-block time; per-query solving is small and fast.
    ///
    /// This replaces the second of the two duplicate portfolio PDR engines
    /// on the SimpleLoop/MultiPredLinear selection arms only (the first,
    /// `PdrConfig::default()`, is unchanged and keeps the full startup +
    /// generalization ladder). It keeps the splits variant's
    /// `use_negated_equality_splits` so the engine remains a distinct probe
    /// of lemma space. The weakening/widening enumeration ladder is demoted
    /// to the interpolation-failure fallback and its most expensive phases
    /// (range weakening binary search, init-bound weakening, convex closure)
    /// are disabled, mirroring `production()`'s precedent.
    ///
    /// SOUNDNESS: config-only — every Safe from this engine passes the same
    /// strict final validation against the ORIGINAL clauses, and every
    /// accepted lemma still passes `is_inductive_blocking`.
    pub fn portfolio_spacer_variant() -> Self {
        Self {
            use_negated_equality_splits: true,
            // (i) startup discovery OFF — straight to the blocking loop.
            skip_startup_discovery: true,
            // (ii) interpolant-as-lemma: skip the post-interpolation
            // weakening/widening enumeration; ladder = fallback only.
            interpolant_first_blocking: true,
            use_range_weakening: false,
            use_init_bound_weakening: false,
            use_convex_closure: false,
            // (iii) executor-first per-pob check_sat for this engine only.
            executor_first_check_sat: true,
            ..Self::default()
        }
        // The second portfolio PDR: legacy on nonlinear problems, racing the
        // nonlinear lane of `default()` (see `portfolio_variant_with_splits`).
        .without_nonlinear_lane()
    }

    /// Spacer-core profile (Workstream B, `DESIGN` §3.7 / §4.5).
    ///
    /// Turns the lane on over `base` (rung 1 when `base.spacer` is OFF, else
    /// `base.spacer` as is) with Spacer's defaults: `push_pob=false`,
    /// `restarts=false`, `global=false` (`use_may_pobs=false`,
    /// `use_convex_closure=false`) and MBP on. Every other field of `base`
    /// is kept. Used by the portfolio roster lane (R1–R2) and, from R3, as
    /// the default PDR config for linear LIA/LRA/Bool problems.
    #[must_use]
    pub fn spacer_core_profile(base: Self) -> Self {
        let spacer = if base.spacer.enabled {
            base.spacer
        } else {
            SpacerLane::rung(1)
        };
        let mut config = Self { spacer, ..base };
        config.apply_spacer_profile_flags();
        config
    }

    /// The technique toggles of the Spacer profile (`DESIGN` §3.7): no POB
    /// push, no Luby restarts, no global guidance (may-pobs, convex closure),
    /// MBP on. `PdrSolver::new` applies them whenever the lane actually runs
    /// (`spacer_core`), so `--chc-spacer-rung N` — which reaches every PDR
    /// config through `PdrConfig::default()` — gets the profile, not only the
    /// lane flags. A problem the lane bypasses (arrays / BV / datatypes) keeps
    /// its config untouched (lane OFF ≡ before, lock L-V).
    pub(crate) fn apply_spacer_profile_flags(&mut self) {
        self.use_pob_push = false;
        self.use_restarts = false;
        self.use_may_pobs = false;
        self.use_convex_closure = false;
        self.use_mbp = true;
    }

    /// Builder: set the Spacer lane flags (validated; `enabled == false` ⇒ OFF).
    #[must_use]
    pub fn with_spacer(mut self, lane: SpacerLane) -> Self {
        self.spacer = lane.validate(self.verbose);
        self
    }

    /// Builder: put this solver's SMT context on `lane` (engines: `Search`).
    #[must_use]
    pub fn with_smt_lane(mut self, lane: crate::smt::SmtLane) -> Self {
        self.smt_lane = lane;
        self
    }

    /// Builder: set maximum number of frames.
    #[must_use]
    pub fn with_max_frames(mut self, frames: usize) -> Self {
        self.max_frames = frames;
        self
    }

    /// Builder: set maximum number of iterations.
    #[must_use]
    pub fn with_max_iterations(mut self, iterations: usize) -> Self {
        self.max_iterations = iterations;
        self
    }

    /// Builder: set maximum number of obligations per strengthen call.
    #[must_use]
    pub fn with_max_obligations(mut self, obligations: usize) -> Self {
        self.max_obligations = obligations;
        self
    }

    /// Builder: enable or disable verbose logging.
    #[must_use]
    pub fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Builder: enable or disable strict proof mode (#8555).
    #[must_use]
    pub fn with_strict_proofs(mut self, strict: bool) -> Self {
        self.strict_proofs = strict;
        self
    }

    /// Builder: enable runtime TLA tracing when `AY_TRACE_FILE` is set.
    ///
    /// This keeps tracing opt-in at top-level entrypoints while preventing
    /// nested helper/validation solvers from reopening the trace file.
    #[must_use]
    pub fn with_tla_trace_from_env(mut self) -> Self {
        // Delegates to ay-core's centralized TraceConfig (#8495).
        self.tla_trace_path = ay_core::trace_config().trace_file_path.clone();
        self.enable_tla_trace = self.tla_trace_path.is_some();
        self
    }

    /// Builder: set the proof run's tick budget ([`Self::effort`]).
    #[must_use]
    pub fn with_effort(mut self, effort: Option<u64>) -> Self {
        self.effort = effort;
        self
    }

    /// Whether the search runs under a budget: an effort, a cancellation
    /// token or a solve timeout. It arms the main loop's per-query cap and the
    /// convergence monitor. Under an effort it is true whether a backstop
    /// clock is passed or not, so the search does not depend on the backstop.
    pub(crate) fn search_is_budgeted(&self) -> bool {
        self.effort.is_some() || self.cancellation_token.is_some() || self.solve_timeout.is_some()
    }

    /// The count caps a run under an effort does not arm (DR-37: a count
    /// besides B is a draw on it or is removed): the frame, iteration and
    /// obligation caps, and with them the obligation queue's (2 x
    /// `max_obligations`) and the level-3 frame raise (`max(200)`). Each
    /// PDR iteration and processed obligation costs a tick of B instead.
    pub(crate) fn disarm_count_caps(&mut self) {
        self.max_frames = usize::MAX;
        self.max_iterations = usize::MAX;
        self.max_obligations = usize::MAX;
    }

    /// Builder: set cancellation token for cooperative stopping.
    #[must_use]
    pub fn with_cancellation_token(mut self, token: Option<CancellationToken>) -> Self {
        self.cancellation_token = token;
        self
    }

    /// Bound every PDR/validation SMT context's term store in bytes.
    ///
    /// A zero ceiling refuses solving/validation. Nested caller ceilings are
    /// intersected; None does not erase an inherited cap. This is neither a
    /// sum across contexts nor a bound on all PDR or process allocations.
    #[must_use]
    pub fn with_memory_budget(mut self, bytes: Option<usize>) -> Self {
        self.memory_budget = bytes;
        self
    }

    /// The requested per-context term ceiling, before inherited intersection.
    pub fn memory_budget(&self) -> Option<usize> {
        self.memory_budget
    }

    /// Cancellation token to pass to nested engines without turning an
    /// external-only observer into a PDR search-budget signal.
    pub(crate) fn effective_cancellation_token(&self) -> Option<CancellationToken> {
        match (&self.cancellation_token, &self.external_cancellation_token) {
            (Some(token), Some(external)) => {
                let mut combined = token.clone();
                combined.link_upstream(external);
                Some(combined)
            }
            (Some(token), None) => Some(token.clone()),
            (None, Some(external)) => Some(external.clone()),
            (None, None) => None,
        }
    }

    /// Builder: add user-provided lemma hints.
    #[must_use]
    pub fn with_user_hints(mut self, hints: Vec<LemmaHint>) -> Self {
        self.user_hints = hints;
        self
    }

    /// Builder: add user-provided runtime hint providers.
    ///
    /// These providers are called alongside the built-in static providers
    /// during hint collection. Providers are `Arc`-wrapped for thread safety
    /// in portfolio solving.
    #[must_use]
    pub fn with_user_hint_providers(mut self, providers: HintProviders) -> Self {
        self.user_hint_providers = providers;
        self
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "config_tests.rs"]
mod tests;
