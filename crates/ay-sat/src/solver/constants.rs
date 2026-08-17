// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CDCL solver tuning constants.
//!
//! All scheduling intervals, decay factors, and budget limits live here.
//! Values are calibrated against CaDiCaL defaults unless otherwise noted.
//! See `reference/cadical/src/options.hpp` for CaDiCaL's option table.
//!
//! ## CaDiCaL Parameter Audit (#7998, 2026-04-10; re-verified #8078, 2026-04-12)
//!
//! Verified parameter parity with CaDiCaL 3.0 (reference/cadical/src/options.hpp):
//!
//! | Parameter           | CaDiCaL option          | CaDiCaL default | AY value       | Match |
//! |---------------------|-------------------------|-----------------|----------------|-------|
//! | VSIDS decay         | scorefactor=950         | 1/0.95=1.0526   | decay=0.95     | Yes   |
//! | Fast EMA window     | emagluefast=33          | 1-1/33          | EMA_FAST_DECAY | Yes   |
//! | Slow EMA window     | emaglueslow=1e5         | 1-1/1e5         | EMA_SLOW_DECAY | Yes   |
//! | Focused margin      | restartmarginfocused=10 | 1.10            | 1.10           | Yes   |
//! | Stable margin       | restartmarginstable=25  | 1.25            | 1.25           | Yes   |
//! | Restart interval    | restartint=2            | 2 conflicts     | 2              | Yes   |
//! | Reluctant period    | reluctantint=1024       | 1024            | 1024           | Yes   |
//! | Reluctant max       | reluctantmax=1048576    | 1048576         | 1048576        | Yes   |
//! | Reduce init         | reduceinit=300          | 300 conflicts   | 300            | Yes   |
//! | Reduce interval     | reduceint(kissat)=1000  | sqrt(reductions)| 1000 (sqrt)    | Kissat|
//! | Reduce target       | reducehigh/low(kissat)  | dynamic 50-90%  | 50-90%         | Kissat|
//! | Tier1 glue          | reducetier1glue=2       | 2               | CORE_LBD=2     | Yes   |
//! | Tier2 glue          | reducetier2glue=6       | 6               | TIER1_LBD=6    | Yes   |
//! | Tier1 usage limit   | tier1limit=50           | 50%             | 50%            | Yes   |
//! | Tier2 usage limit   | tier2limit=90           | 90%             | 90%            | Yes   |
//! | Stabilize init      | stabilizeinit=1e3       | 1000 conflicts  | 1000           | Yes   |
//! | Rephase interval    | rephaseint=1e3          | 1000            | 1000           | Yes   |
//! | Bumpreason depth    | bumpreasondepth=1       | 1+stable        | 1+stable       | Yes   |
//! | Bumpreason rate     | bumpreasonrate=100      | 100             | 100            | Yes   |
//! | Target phases       | target=1                | stable only     | stable only    | Yes   |
//! | Chrono level limit  | chronolevelim=100       | 100             | 100            | Yes   |
//! | Chrono reuse trail  | chronoreusetrail=1      | enabled         | enabled        | Yes   |
//! | Eager subsume limit | eagersubsumelim=20      | 20              | 20             | Yes   |
//! | Phase init          | phase=1                 | positive        | positive       | Yes   |
//! | Flush               | flush=0                 | disabled        | disabled       | Yes   |
//!
//! ## Performance Gap Analysis (#8078, 2026-04-12)
//!
//! Despite parameter parity, AY is 3-13x slower than CaDiCaL in conflicts/sec:
//! - Schur_161_5: AY 15K confs/s vs CaDiCaL 45K confs/s (3x gap)
//! - FmlaEquivChain: AY 576 confs/s vs CaDiCaL 25K confs/s (43x gap, preprocess-dominated)
//! - klieber2017s: AY 922 confs/s (no-inproc) vs CaDiCaL 7.6K confs/s (8x gap)
//!
//! Root cause is NOT parameter tuning but implementation throughput:
//! - BCP: AY 5.8M props/s (no-inprocessing) vs CaDiCaL 2.5-8.7M props/s
//! - Preprocessing: AY 8-9s on 54K vars vs CaDiCaL 0.43s (congruence+BVE pipeline)
//! - Inprocessing overhead: reduces AY from 5.8M to 758K props/s (8x penalty)
//!
//! Known divergences (intentional):
//! - Stable-mode EMA restarts: AY adds Glucose EMA check with margin 1.25 OR'd
//!   with reluctant doubling (restart.rs:288-301). CaDiCaL uses reluctant only.
//!   Removing degrades clique benchmarks (#8135). Formula-class gating (#8448):
//!   Small formulas skip EMA entirely (pure reluctant); Medium/Large use
//!   STABLE_EMA_MIN_CONFLICTS=10 as conflict gate.
//! - Lookahead scheduling: Large formulas skip lookahead entirely (#8448).
//!   Probing is O(vars) even with budgets, and wall-clock enforcement has
//!   granularity issues on formulas with 100K+ variables.
//! - VMTF queue maintenance in stable mode: AY bumps VMTF on every conflict
//!   for arena compaction locality (#8036). CaDiCaL only bumps VMTF in focused
//!   mode. Extra ~5-6 cache lines per analyzed variable in stable mode.

// ─── Preprocessing Budget ──────────────────────────────────────────

/// Maximum probes during preprocessing (per round).
/// CaDiCaL uses tick-proportional budgets with preprocessinit=2e6 ticks
/// floor. Since AY doesn't track per-probe ticks during preprocessing,
/// we use a generous count limit that prevents hangs on large instances
/// (e.g., shuffling-2: 138K vars, 4.7M clauses) while allowing thorough
/// probing on moderate instances.
/// Raised from 2K to 10K (#8466): Kissat uses effort-based probing that
/// probes more aggressively than AY's fixed count limit. 10K probes
/// covers ~25-50% of variables on medium formulas like FmlaEquivChain
/// (3656 vars), matching Kissat's effective probe coverage.
/// CaDiCaL reference: `probeeffort=8`, `preprocessinit=2e6` (options.hpp).
pub(super) const MAX_PREPROCESS_PROBES: usize = 10_000;

// ─── Restart Parameters ─────────────────────────────────────────────

/// Default base restart interval (conflicts per Luby unit)
pub(super) const DEFAULT_RESTART_BASE: u64 = 100;

/// Extension-mode restart warmup: suppress restarts for the first N conflicts.
/// Theory/extension mode benefits from a slightly longer warmup than pure SAT
/// because theory propagation establishes an initial search trajectory that
/// premature restarts would disrupt. The fast EMA needs ~33 conflicts to
/// stabilize, so 50 provides a reasonable margin.
pub(super) const EXTENSION_RESTART_WARMUP: u64 = 50;

/// Fast EMA decay factor (short window, ~33 conflicts)
/// decay = 1 - 1/33 (matches CaDiCaL emagluefast=33)
pub(super) const EMA_FAST_DECAY: f64 = 1.0 - 1.0 / 33.0;

/// Slow EMA decay factor (long window, ~100000 conflicts)
/// decay = 1 - 1/100000 = 0.99999 (matches CaDiCaL's emaglueslow)
pub(super) const EMA_SLOW_DECAY: f64 = 0.99999;

/// Restart margin (focused mode): fast EMA must exceed slow EMA * margin.
/// CaDiCaL restartmarginfocused=10 → (100+10)/100 = 1.10.
/// A/B #1 finding: lowering this to 1.00/1.05 helps c7552 but over-restarts
/// SCPC (conflicts +30%), so the margin is kept at the calibrated 1.10. The
/// robust restart-cadence win came from removing the default-off trail-blocking
/// experiment, not from changing this margin.
/// Overridable at runtime via `AY_AB_FOCUSED_MARGIN` for A/B experiments.
pub(super) const RESTART_MARGIN_FOCUSED: f64 = 1.10;

/// Restart margin (stable mode): higher threshold = harder to restart.
/// CaDiCaL restartmarginstable=25 → (100+25)/100 = 1.25.
/// Used by the stable-mode Glucose EMA restart check (#7998), which
/// complements reluctant doubling to prevent pathologically deep searches.
pub(super) const RESTART_MARGIN_STABLE: f64 = 1.25;

/// Minimum conflicts between restarts in focused mode (restart blocking).
/// CaDiCaL restartint=2 with `<=` comparison: `stats.conflicts <= lim.restart`
/// where `lim.restart = stats.conflicts + restartint`. This means CaDiCaL needs
/// strictly MORE than restartint conflicts, i.e., at least 3. AY matches by
/// using `>` comparison: `conflicts_since_restart > RESTART_INTERVAL`.
pub(super) const RESTART_INTERVAL: u64 = 2;

/// Minimum conflicts since last restart before stable-mode EMA can fire (#8360).
/// Used for Medium/Large formulas; Small formulas use
/// SMALL_DENSE_EMA_MIN_CONFLICTS. Recovery commit 93835f65a proved
/// 7/23 SAT-COMP score with this value at 10. Raising to 50 caused
/// ecarev-110 and shuffling-sat04 to timeout (#8448) because reluctant
/// doubling alone lets stable mode run too deep without quality gating.
pub(super) const STABLE_EMA_MIN_CONFLICTS: u64 = 10;

/// Minimum conflicts since last restart before stable-mode EMA can fire on
/// small dense formulas (#8135, #8466). Higher than STABLE_EMA_MIN_CONFLICTS
/// (50 vs 10 on medium/large) to prevent pathological high-frequency EMA
/// firing on small dense binary formulas, but low enough to provide
/// quality-gated restarts for dense formulas like stable-300 (#8360).
/// Note: Small formulas currently skip EMA entirely (pure reluctant in
/// restart.rs), so this constant is only used if the Small-skip logic
/// is relaxed in the future.
///
/// 50 = 5% of the first reluctant period (1024), matching the original fix
/// from commit 9acba333e.
pub(super) const SMALL_DENSE_EMA_MIN_CONFLICTS: u64 = 50;

/// Threshold for adaptive focused-mode EMA throttling (#8360).
/// After this many consecutive focused-mode restarts where the Glucose EMA
/// condition fires, the conflict gate is raised from RESTART_INTERVAL to
/// num_vars/4 (capped at 100). This prevents restart storms on small dense
/// formulas (two-trees, stable-300) where the LBD is uniformly high and the
/// EMA check always fires, while not affecting normal operation where the
/// EMA condition oscillates. Value 100 means ~300 conflicts (at gate=3) must
/// pass with the EMA always firing before throttling activates.
pub(super) const FOCUSED_EMA_CONSEC_THRESHOLD: u64 = 100;

/// Default-off dense-mutex restart experiment (#9164).
///
/// Candidate shape follows the R3 #9160 clique guardrail: small active variable
/// count, clause/variable density above 10, and at least 95% binary clauses.
pub(super) const DENSE_MUTEX_FOCUSED_RESTART_MAX_ACTIVE_VARS: usize = 1000;
pub(super) const DENSE_MUTEX_FOCUSED_RESTART_MIN_DENSITY_TIMES_100: usize = 1000;
pub(super) const DENSE_MUTEX_FOCUSED_RESTART_MIN_BINARY_PERCENT: usize = 95;
pub(super) const DENSE_MUTEX_FOCUSED_RESTART_MIN_GATE: u64 = 40;
pub(super) const DENSE_MUTEX_FOCUSED_RESTART_MAX_GATE: u64 = 100;

/// Minimum conflicts before considering Glucose-style restarts.
///
/// CaDiCaL has NO warmup gate — it relies entirely on ADAM-style EMA bias
/// correction (ema.cpp) to handle the cold-start. AY implements the same
/// bias correction (update_lbd_ema), so a warmup is unnecessary.
///
/// Previously 100, which suppressed all restarts for the first 100 conflicts
/// and prevented early search diversification. Reduced to 2 to match
/// CaDiCaL's effective behavior (restartint=2 is the only gate).
pub(super) const RESTART_MIN_CONFLICTS: u64 = 2;

// ─── Theory-Aware Restart Parameters (#8452) ────────────────────────
//
// When the solver detects a high ratio of theory/extension conflicts
// (>80% of total conflicts), it switches from aggressive Glucose EMA
// restarts to Luby restarts with a longer base interval. This gives
// the theory solver more time to propagate LP-derived bounds before
// the SAT solver restarts and throws away the search trajectory.
//
// Reference: Z3 uses geometric restarts (RS_GEOMETRIC) with
// restart_adaptive=false for QF_LRA, producing the sequence
// 100, 110, 121, 133, ... AY's theory-aware Luby produces a similar
// effect: longer intervals between restarts that prevent the premature
// disruption of theory-guided search.
//
// On sc-6.induction3: without this, 85 restarts in 572 conflicts
// (1 restart / 6.7 conflicts), 15460 decisions, timeout.
// Z3 solves in 0.01s with 69 conflicts, 597 decisions.

/// Theory conflict ratio threshold for switching to Luby restarts.
/// When `ext_conflict_count / num_conflicts > threshold`, the solver
/// is in a theory-dominated regime and Glucose EMA restarts are too
/// aggressive.
pub(super) const THEORY_CONFLICT_RATIO_THRESHOLD: f64 = 0.80;

/// Base restart interval (in conflicts) for theory-heavy Luby restarts.
/// This replaces DEFAULT_RESTART_BASE (100) when theory mode is active.
/// Z3's geometric restart for QF_LRA starts at 100 conflicts. Luby(1)=1,
/// so base=100 gives the first restart at 100 conflicts, matching Z3's
/// initial interval. With the dedicated theory_luby_idx (starting at 1),
/// the sequence is: 100, 100, 200, 100, 100, 200, 400, 100, ...
pub(super) const THEORY_LUBY_BASE: u64 = 100;

/// EMA decay factor for the theory conflict ratio tracker.
/// Uses a ~64-conflict window (1 - 1/64) to adapt quickly when the
/// solver transitions between theory-heavy and pure-SAT phases.
pub(super) const THEORY_RATIO_EMA_DECAY: f64 = 1.0 - 1.0 / 64.0;

/// Initial stabilization phase length (conflicts before first mode switch)
/// CaDiCaL uses 1000 conflicts for first focused phase
pub(super) const STABLE_PHASE_INIT: u64 = 1000;

/// Default window (in conflicts) for the equiticks progress gate
/// (`--sat-eqt-progress`, opt-in). While the stable-mode `target_trail_len`
/// improved within the last this-many conflicts, the stable->focused switch is
/// deferred past the equal-effort tick budget (up to the nlogpow4 hardcap), so
/// a still-converging stable phase is not starved by the equal-effort split.
/// A plateaued phase (no target improvement for this many conflicts) switches
/// at the equal-effort budget exactly as plain equiticks would.
pub(super) const EQT_PROGRESS_WINDOW_DEFAULT: u64 = 2000;

/// Base period for reluctant doubling (Knuth's Luby sequence) in stable mode.
/// Restart interval = period x luby(n). CaDiCaL: reluctantint=1024.
pub(super) const RELUCTANT_INIT: u64 = 1024;

/// Maximum Luby sequence value before resetting to (u=1, v=1).
/// CaDiCaL: reluctantmax=1048576. Prevents unbounded interval growth.
pub(super) const RELUCTANT_MAX: u64 = 1_048_576;

// ─── Cold Restart Parameters (Zhang et al. 2024) ───────────────────
//
// Cold restart periodically forgets selected learned information to escape
// unproductive search regions. The FO (Forget Order) variant randomizes
// variable branching scores; FP (Forget Phases) randomizes polarities.
//
// Trigger: conflicts_since_last_cold >= COLD_RESTART_INTERVAL * (count + 1)
// Linear growth: later cold restarts happen less frequently.
//
// Reference: Xindi Zhang, Zhihan Chen, Shaowei Cai. "Revisiting Restarts
// of CDCL: Cold Restart." arXiv:2404.16387v2, May 2024.
//
// On SAT-COMP 2020/2021 (400 instances each), FO alone gives:
//   Kissat-MAB: 289 -> 295 (+6), CaDiCaLWS: 243 -> 252 (+9).
// Parameter p=300K is in the recommended 100K-1M range from the paper.

/// Base interval for cold restart trigger schedule (conflicts).
/// Cold restart fires when `conflicts_since_last_cold >= p * (count + 1)`.
/// 300K is in the middle of the paper's recommended 100K-1M range.
pub(super) const COLD_RESTART_INTERVAL: u64 = 300_000;

// ─── Random Decision Parameters ─────────────────────────────────────

/// Inter-burst interval multiplier (CaDiCaL randecint=500)
/// Next burst at: conflicts + phases * ln(phases) * RANDEC_INT
pub(super) const RANDEC_INT: f64 = 500.0;

/// Base length multiplier for random decision burst duration (CaDiCaL randeclength=10)
/// Burst length = RANDEC_LENGTH * ln(phase_count + 10)
pub(super) const RANDEC_LENGTH: f64 = 10.0;

// ─── Clause DB Reduction ─────────────────────────────────────────────

/// First clause DB reduction after this many conflicts.
/// CaDiCaL: `reduceinit = 300` (options.hpp:179).
/// Kissat: `reduceinit = 1000` (options.h:111).
pub(super) const FIRST_REDUCE_DB: u64 = 300;

/// Base interval for clause DB reduction scheduling (Kissat-style).
/// Kissat: `reduceint = 1000` (options.h:112).
///
/// Kissat schedule: `delta = reduceint * sqrt(reductions)`.
///   At reduction #1:   delta = 1000 * 1 = 1000
///   At reduction #10:  delta = 1000 * 3.16 = 3162
///   At reduction #100: delta = 1000 * 10 = 10000
///
/// (#8655) Ported from CaDiCaL's approach (reduceint=25, sqrt(conflicts))
/// to Kissat's approach (reduceint=1000, sqrt(reductions)). Kissat's
/// approach produces more frequent early reductions that establish DB
/// quality early, with growth bounded by reduction count. The
/// LARGE_FORMULA_REDUCE_MAX_INTERVAL cap (5000) prevents unbounded
/// intervals on deep BMC formulas.
///
/// (#8448) Combined with raised REDUCE_LOW_PERMILLE (750 vs Kissat's 500)
/// to match CaDiCaL's 75% deletion at early reductions. The original
/// Kissat 50% was too conservative for SAT-COMP formulas.
pub(super) const REDUCE_DB_INT: u64 = 1_000;

/// High reduce fraction per mille (Kissat-style dynamic reduce target).
/// Kissat: `reducehigh = 900` (options.h:110) — 90%.
///
/// The fraction of reduction candidates to delete decreases from high
/// to low as the number of reductions grows:
///   percent = high - (high - low) / log10(reductions + 9)
///
/// Early reductions (count=1): 90 - 15/1.0 = 75% (matches CaDiCaL's
/// fixed reducetarget=75).
/// Mid reductions (count=100): 90 - 15/2.04 = 82.6%.
/// Late reductions (count=1000): 90 - 15/3.0 = 85.0%.
///
/// (#8448) Raised LOW from 500 to 750 to match CaDiCaL's 75% at early
/// reductions. The original Kissat value of 50% was too conservative for
/// SAT-COMP formulas: with frequent Kissat-style scheduling (sqrt(reductions)),
/// deleting only 50% early keeps the learned DB larger than optimal,
/// bloating watch lists and slowing BCP. CaDiCaL's fixed 75% was better
/// calibrated for non-BMC search. The dynamic curve still reaches 90%
/// for late reductions where stale clause pruning is beneficial.
pub(super) const REDUCE_HIGH_PERMILLE: u64 = 900;

/// Low reduce fraction per mille (Kissat-style dynamic reduce target).
/// Kissat: `reducelow = 500` (options.h:113) — 50%.
/// (#8448) Raised to 750 — see REDUCE_HIGH_PERMILLE comment.
pub(super) const REDUCE_LOW_PERMILLE: u64 = 750;
const _: () = assert!(REDUCE_LOW_PERMILLE <= REDUCE_HIGH_PERMILLE);
const _: () = assert!(REDUCE_HIGH_PERMILLE <= 1000);

/// Small dense UNSAT formulas generate many low-glue clauses that can swamp
/// watch lists. When the small-dense reduction policy is active, start the
/// dynamic reduce curve at 85% deleted candidates instead of the default 75%.
pub(super) const SMALL_DENSE_REDUCE_LOW_PERMILLE: u64 = 850;
const _: () = assert!(SMALL_DENSE_REDUCE_LOW_PERMILLE <= REDUCE_HIGH_PERMILLE);

/// Poll the process-wide memory limit after this many conflicts.
///
/// This amortizes the global-memory probe used by `TermStore::global_memory_exceeded()`
/// while still bounding mid-solve overshoot on hard SAT instances (#6552).
pub(super) const PROCESS_MEMORY_CHECK_INTERVAL: u64 = 10_000;

/// Tier1 usage percentage limit (CaDiCaL tier1limit=50)
/// tier1 boundary is set so accumulated usage <= this % of total
pub(super) const TIER1_LIMIT_PCT: u64 = 50;

/// Tier2 usage percentage limit (CaDiCaL tier2limit=90)
pub(super) const TIER2_LIMIT_PCT: u64 = 90;

/// Initial conflict interval between clause flushes.
/// CaDiCaL: `flushint = 1e5` (options.hpp:133), but `flush` defaults to 0
/// (DISABLED). Flush is more aggressive than reduce — it marks ALL unused
/// learned clauses as garbage regardless of tier. On hard combinatorial
/// instances requiring deep search (300K-1.2M conflicts), flushing deletes
/// valuable learned clauses that took many conflicts to discover.
/// Disabled (u64::MAX) to match CaDiCaL's default.
pub(super) const FLUSH_INIT: u64 = u64::MAX;

/// Multiplicative factor for flush interval growth.
/// CaDiCaL: `flushfactor = 3` (options.hpp:132).
/// Intervals grow geometrically: 100K, 300K, 900K, 2.7M, ...
pub(super) const FLUSH_FACTOR: u64 = 3;

/// Threshold for "small formula" reduce_db interval capping (#8135).
/// Formulas with <= this many original clauses get a capped reduce_db
/// interval to prevent clause DB bloat. On small dense UNSAT formulas
/// (e.g., clique graphs: 180 vars, 3160 clauses), the Kissat-style
/// `REDUCE_DB_INT * sqrt(reductions)` scheduling can grow the interval
/// large enough to cause clause DB bloat from ~900 to 10K+ clauses.
/// This bloat slows BCP by 2-3x (more watch entries per propagation).
pub(super) const SMALL_FORMULA_REDUCE_CAP_THRESHOLD: usize = 10_000;

/// Multiplier for reduce_db interval cap on small NON-DENSE formulas (#8135).
/// Cap = max(SMALL_FORMULA_REDUCE_CAP_MULT * num_original_clauses, FIRST_REDUCE_DB).
///
/// The original #8135 cap (mult=2) was tuned for small DENSE clique graphs
/// (180v/3160c, density ~17), but it was mis-applied to small SPARSE formulas.
/// On sparse small UNSAT instances (e.g. 3f67f676, 1043v/3649c, density 3.5,
/// post-preproc ~987 orig clauses) mult=2 caps the reduce interval at ~1974
/// conflicts, forcing ~6800 reductions that delete+re-derive useful clauses and
/// pin the learned DB near ~8500 clauses -> 13.1M-conflict thrash / timeout.
///
/// Raising the non-dense multiplier to 8 lets the interval track the Kissat
/// sqrt(reductions) schedule up to 8x formula size, keeping a larger learned DB
/// (~21K clauses, 815 reductions) so 3f67f676 flips UNKNOWN->UNSAT @6.22M
/// conflicts / ~82s (dpr-trim + cake_lpr VERIFIED). Sweep {4,6,8,12,16,24,uncap}:
/// mult<=4 no flip; mult>=6 flips; wall plateaus ~80-83s for mult>=8; higher
/// mults only inflate the learned DB (worse BCP) without wall gains -> 8 is the
/// robustness sweet spot (38s margin, least DB inflation among flipping values).
///
/// This does NOT touch small DENSE formulas: they use SMALL_DENSE_REDUCE_CAP_MULT
/// below. It also does NOT touch any regression-floor instance: the cap only
/// engages for post-preproc num_original_clauses <= SMALL_FORMULA_REDUCE_CAP_THRESHOLD
/// (10_000); every floor member exceeds 10K clauses post-preproc (smallest are
/// 31e843c5=11383, 43fbacb2=48439, 6f354fbe=59598) -> byte-identical search.
///
/// A/B knob `AY_SMALL_REDUCE_CAP_MULT` overrides this in [0, 64]; 0 = uncapped.
/// Set =2 to restore the original #8135 behavior.
pub(super) const SMALL_FORMULA_REDUCE_CAP_MULT: u64 = 8;

/// Tighter interval cap for small dense Main formulas (#8135).
///
/// These instances already relax permanent glue-2 protection and use a denser
/// delete target. Keep the next reduce interval closer to the live original
/// formula size so low-glue learned clauses do not refill the watch lists
/// between reductions.
pub(super) const SMALL_DENSE_REDUCE_CAP_MULT: u64 = 1;
const _: () = assert!(SMALL_DENSE_REDUCE_CAP_MULT <= SMALL_FORMULA_REDUCE_CAP_MULT);

/// Maximum reduce_db interval (conflicts) for large formulas (#8655).
///
/// On deep BMC formulas (depth 100+, millions of clauses), even with
/// the Kissat-style `REDUCE_DB_INT * sqrt(reductions)` scheduling,
/// at reduction #100+ the interval reaches 10K conflicts. During that
/// interval, learned clauses accumulate rapidly from the structured
/// BMC encoding, bloating the clause DB and slowing BCP.
///
/// 5000 conflicts between reductions keeps the learned clause DB bounded
/// at ~5000 additional clauses per reduce cycle on deep BMC, while still
/// being generous enough for hard combinatorial instances requiring deep
/// learned clause accumulation.
pub(super) const LARGE_FORMULA_REDUCE_MAX_INTERVAL: u64 = 5_000;

/// Threshold for "large formula" reduce_db interval capping (#8655).
/// Formulas with > this many original clauses get a capped reduce_db
/// interval to prevent learned clause bloat during long SAT solves.
/// 100K clauses is well above most small/medium instances but catches
/// BMC-generated formulas at depth 50+ (typically 200K-2M clauses).
pub(super) const LARGE_FORMULA_REDUCE_CAP_THRESHOLD: usize = 100_000;

/// Default learned clause limit as a multiplier of original clause count (#8655).
///
/// When no explicit `max_learned_clauses` is set, the solver auto-computes
/// a cap for large formulas: `num_original_clauses * LEARNED_CLAUSE_CAP_MULT`.
/// This prevents unbounded learned clause growth on deep BMC formulas where
/// the solver generates millions of learned clauses before reaching the
/// satisfying assignment.
///
/// Kissat and CaDiCaL achieve similar behavior through aggressive tier-based
/// reduction. AY's reduction fires less frequently on large formulas (due to
/// the sqrt scaling), so an explicit cap is needed as a safety net.
///
/// Factor 3: the learned clause DB can grow to 3x the original formula size.
/// At that point, the aggressive reduction (75% deletion) brings it back to
/// ~0.75x, cycling between 0.75x and 3x. This matches CaDiCaL's effective
/// behavior on large industrial instances.
pub(super) const LEARNED_CLAUSE_CAP_MULT: usize = 3;

/// Tighter learned clause cap for very large formulas (>1M clauses, #8655/#8448).
///
/// On deep BMC formulas with >1M original clauses, even a 3x cap allows
/// the learned clause DB to grow by millions of clauses. Each learned clause adds
/// watch entries to 2 literals, bloating watch lists and slowing BCP. With
/// 1M original clauses, a 3x cap means up to 3M learned clauses, producing
/// 6M additional watch entries across the literal index.
///
/// Factor 2: learned clause DB grows to 2x the original formula size.
/// Tighter than the standard 3x cap to limit BCP degradation on formulas
/// where the original clause DB is already large. The reduction cycle
/// oscillates between 0.5x and 2x (vs 0.75x and 3x with the standard cap),
/// keeping the total watch list size closer to the original formula's.
///
/// Applied only when num_original_clauses > VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD.
pub(super) const VERY_LARGE_FORMULA_LEARNED_CAP_MULT: usize = 2;

/// Threshold for "very large formula" stable mode bias (#8655, #8448).
/// Formulas with > this many original clauses start directly in stable mode
/// (EVSIDS + target phases + reluctant doubling) instead of focused mode.
///
/// Deep BMC formulas (depth 50-200, typically 200K-2M clauses) are highly
/// structured and benefit most from stable-mode search:
/// - EVSIDS preserves variable ordering across restarts (critical for BMC
///   where decision variables have strong locality by unrolling depth).
/// - Target phases preserve satisfying polarities found during search.
/// - Reluctant doubling gives geometrically growing restart intervals,
///   allowing deeper search before restart.
///
/// Focused mode (VMTF + Glucose restarts) is designed for finding short
/// proofs quickly on random/crafted instances. On deep BMC, it causes
/// excessive restarts that destroy search progress.
///
/// #8448: Previously raised from 500K to 2M because the threshold caught
/// non-BMC SAT-COMP formulas (ecarev-110: 741K clauses). That regression
/// was caused by the combination of stable bias + stable LOCK + inprocessing
/// suppression. With lock=false and suppress=false (#8448), the solver can
/// still switch to focused mode when needed, so stable bias alone is safe.
///
/// #8655: Lowered to 500K for BMC performance. Sokoban HWMCC benchmarks at
/// depth 50-200 generate 200K-1M clauses. At the 2M threshold, these BMC
/// formulas spent their first phase in focused mode (Glucose EMA restarts),
/// which restarts every few hundred conflicts and destroys search progress
/// on structured unrollings. Starting in stable mode (bias without lock)
/// gives BMC a head start while preserving adaptability for non-BMC formulas.
///
/// #8448: Raised to 1M to avoid misclassifying non-BMC structured formulas
/// as BMC. ecarev-110 (741K clauses, cellular automata) regressed from 1.2s
/// to >30s because stable bias + slower VSIDS decay (0.97) is harmful for
/// formulas that benefit from focused-mode VMTF and aggressive restarts.
/// At 1M, Sokoban HWMCC at depth 100+ (>1M clauses) still gets stable bias,
/// while moderate-size structured formulas use the default mode alternation.
pub(super) const VERY_LARGE_FORMULA_STABLE_BIAS_THRESHOLD: usize = 1_000_000;

/// Lock stable mode for very large formulas (#8655).
///
/// DISABLED (#8448): Locking stable mode prevents the solver from
/// adapting to formula structure discovered during search. Even on
/// BMC-like formulas, focused-mode phases can discover useful conflict
/// patterns that improve subsequent stable-mode phases. The stable-bias
/// (starting in stable mode) gives BMC formulas a head start without
/// permanently committing.
///
/// Previously true for formulas >500K clauses, but this caused
/// regressions on SAT-COMP formulas (ecarev-110, shuffling-2) that
/// benefit from mode alternation.
pub(super) const VERY_LARGE_FORMULA_STABLE_LOCK: bool = false;

/// Suppress inprocessing during search for very large formulas (#8655).
///
/// DISABLED (#8448): Suppressing inprocessing entirely removes the
/// solver's ability to simplify learned clauses during long searches.
/// Even on large formulas, inprocessing passes (vivification, BVE,
/// probing) are budget-gated by the existing tick-proportional scheduling
/// which already scales effort down for large formulas. The budgets
/// provide sufficient overhead control without blanket suppression.
///
/// Previously true for formulas >500K clauses, but this caused
/// regressions on SAT-COMP formulas that need mid-search simplification
/// (e.g., ecarev-110 solved in 1.2s with inprocessing, times out without).
pub(super) const VERY_LARGE_FORMULA_SUPPRESS_INPROCESSING: bool = false;

/// VSIDS decay rate for stable mode on very large formulas (#8655).
///
/// Standard VSIDS decay (0.95) forgets 5% of scoring history per conflict.
/// On deep BMC formulas, variable importance is highly structured by
/// unrolling depth and changes slowly. A slower decay (0.99) preserves
/// more historical scoring information, maintaining the decision ordering
/// across long stable-mode runs.
///
/// CaDiCaL uses a fixed `scorefactor=950` (decay 0.95) for all modes.
/// Kissat does not vary decay per mode either, but Kissat's EVSIDS
/// implementation benefits from reluctant-doubling-only restarts that
/// give it thousands of conflicts per restart interval, during which
/// the scoring hierarchy stabilizes naturally. AY's stable EMA check
/// (#8448) can still fire restarts that perturb the hierarchy; the
/// slower decay compensates by making each perturbation smaller.
///
/// 0.99 = forget 1% per conflict (vs 5% at 0.95). After 100 conflicts,
/// old scores retain 36.6% of their weight (vs 0.59% at 0.95).
pub(super) const VERY_LARGE_FORMULA_VSIDS_DECAY: f64 = 0.99;

/// VSIDS decay rate for very large formulas below the deep-BMC tier (1M-2M clauses, #8655/#8448).
///
/// Intermediate between the default (0.95) and very-large (0.99). On
/// formulas in this range (moderate BMC depths, structured SAT-COMP
/// instances), the variable importance hierarchy is somewhat structured
/// but not as rigid as deep BMC with millions of clauses.
///
/// 0.97 = forget 3% per conflict. After 100 conflicts, old scores
/// retain 4.8% of their weight (vs 0.59% at 0.95 and 36.6% at 0.99).
/// This provides more scoring stability than the default without the
/// extreme memory of 0.99 that can trap the solver in a scoring rut.
pub(super) const LARGE_FORMULA_VSIDS_DECAY: f64 = 0.97;

/// Scale factor for initial stable phase length on large formulas (#8655).
///
/// For formulas with > LARGE_FORMULA_REDUCE_CAP_THRESHOLD (100K) clauses
/// but below the stable-bias threshold (1M), the initial stabilization
/// phase length (STABLE_PHASE_INIT = 1000 conflicts) is multiplied by
/// `log10(clauses)`. This gives:
///   100K clauses: 1000 * 5 = 5000 conflicts
///   300K clauses: 1000 * 5.5 = 5500 conflicts
///   1M clauses: stable bias kicks in (starts in stable mode directly)
///
/// This ensures the first focused-mode phase is long enough to establish
/// meaningful LBD EMA statistics before the first mode switch. On large
/// formulas, 1000 conflicts is barely enough to propagate through one
/// structural layer, providing no useful EMA signal.
///
/// CaDiCaL achieves this implicitly: its first phase is 1000 conflicts,
/// but subsequent phases use tick-based scheduling where ticks scale
/// with formula size. AY's first phase uses the same 1000-conflict
/// threshold, but the tick bootstrap happens AFTER the first phase ends,
/// so a short first phase produces a poor tick delta estimate that
/// propagates to all future phases.
pub(super) const LARGE_FORMULA_STABLE_PHASE_SCALE: bool = true;

// ─── Backtracking ────────────────────────────────────────────────────

/// Maximum levels to jump before using chronological backtracking
/// If jump_levels > CHRONO_LEVEL_LIMIT, use chronological backtracking instead
pub(super) const CHRONO_LEVEL_LIMIT: u32 = 100;

// ─── Vivification ────────────────────────────────────────────────────

/// Run vivification after this many conflicts (was 10000, reduced for BV #757).
/// Acts as a minimum spacing guard between vivification rounds; actual effort
/// is controlled by tick-proportional budgeting (VIVIFY_EFFORT_PERMILLE).
pub(super) const VIVIFY_INTERVAL: u64 = 2000;

/// Interval between irredundant vivification passes.
/// Set lower than the initial 10K to run irredundant vivification more
/// promptly, but higher than learned (2K) since irredundant vivification
/// uses standalone propagation which is slower per-clause.
pub(super) const VIVIFY_IRRED_INTERVAL: u64 = 5000;

/// Number of irredundant clauses to vivify per call.
/// Higher than learned budget (500) because irredundant clauses are
/// typically the bottleneck on structured instances.
pub(super) const VIVIFY_IRRED_CLAUSES_PER_CALL: usize = 1000;

/// Maximum adaptive multiplier for irredundant vivification interval.
/// Caps backoff at 64 * VIVIFY_IRRED_INTERVAL to avoid starvation.
pub(super) const VIVIFY_IRRED_MAX_DELAY_MULTIPLIER: u64 = 64;

/// Vivification effort as per-mille of search ticks since last vivification.
/// CaDiCaL: `vivifyeffort = 50` (options.hpp:258). Kissat: `vivifyeffort = 100`
/// (options.h:161). Kissat's 10% effort produces 88% vivification success on
/// small dense formulas like clique_n2_k10, vs AY's 11% with CaDiCaL's 5%.
/// Use Kissat's value (#8135): the additional 5% investment in vivification
/// pays for itself via reduced search effort (1.36 decisions/conflict vs 3.7).
pub(super) const VIVIFY_EFFORT_PERMILLE: u64 = 100;

/// Tier effort weights for splitting the vivification tick budget.
/// CaDiCaL vivify.cpp:1753-1764 defaults: tier1=4, tier2=2, tier3=1, irred=3.
/// Kissat options.h:165-167 defaults: tier1=3, tier2=3, tier3=1, irr=3.
/// Kissat's equal tier1/tier2 weight allocates more effort to mid-quality
/// learned clauses (2<LBD<=tier2_limit), which are more numerous and offer
/// more strengthening opportunities on industrial UNSAT instances (#8134).
/// Reference: Biere et al., "Revisiting Clause Vivification" (POS'25).
pub(super) const VIVIFY_TIER_WEIGHT_CORE: u64 = 3;
pub(super) const VIVIFY_TIER_WEIGHT_TIER2: u64 = 3;
pub(super) const VIVIFY_TIER_WEIGHT_OTHER: u64 = 1;
pub(super) const VIVIFY_TIER_WEIGHT_IRRED: u64 = 3;

/// Minimum vivification effort (ticks) per call.
/// CaDiCaL controls vivification effort via `vivifyeffort` (options.hpp:258,
/// per-mille efficiency) and per-tier options `vivifytier{1,2,3}eff`.
/// This constant serves a similar role to `elimmineff` (options.hpp:99) for
/// elimination: a minimum floor ensuring progress even when few search ticks
/// have accumulated (e.g. early in the search or on trivial instances).
/// Increased from 10K to 1M (#8362): on small dense formulas like clique
/// graphs (180 vars, 3160 clauses), 100K ticks is exhausted before
/// preprocessing vivification examines enough candidates. Kissat's effective
/// preprocessing vivification budget is ~1M ticks. CaDiCaL vivifymineff=100K
/// is too low for the preprocessing phase where full formula analysis pays off.
pub(super) const VIVIFY_MIN_EFFORT: u64 = 1_000_000;

/// Maximum number of preprocessing vivification convergence rounds.
/// Each round rebuilds literal occurrence scores and re-runs vivification.
/// Early termination when a round produces no strengthenings.
/// Kissat's effective preprocessing vivification loops until convergence;
/// reduced from 10 to 3 (#8448): on small dense formulas like Schur_161_5
/// (757 vars, 28K clauses), 10 rounds with 1M ticks each causes 9-11s
/// preprocessing despite a 2s wall-clock budget (passes blow the budget
/// individually). 3 rounds still achieves 51.8% strengthening on
/// clique_n2_k10 (180v, 3160c) while capping total vivification to 3M
/// ticks instead of 10M.
///
/// (#8448 Wave A Phase 1) Raised from 3 to 4 to match CaDiCaL's effective
/// per-cycle coverage: `reference/cadical/src/vivify.cpp` runs three
/// per-glue tier passes (`schedule_tier1/2/3`) plus one irredundant pass
/// under `opts.vivifyirred=1`, yielding 4 effective vivification passes
/// per preprocessing invocation. 4 rounds keeps strict parity while the
/// `VIVIFY_MIN_EFFORT` budget still prevents runaway on dense formulas.
pub(super) const PREPROCESS_VIVIFY_MAX_ROUNDS: usize = 4;

/// Maximum number of consecutive retries for a successfully vivified clause.
/// CaDiCaL vivify.cpp:1598-1608 (`opts.vivifyretry`, default 0): when a clause
/// is strengthened and still has >2 literals, push it back onto the schedule for
/// another attempt. This catches cascading simplifications that a single pass
/// misses. Increased from 1 to 3 (#8135): on small dense formulas like clique
/// graphs, cascading strengthening is critical. A single retry misses chains
/// where shortening clause A enables shortening clause B which enables further
/// shortening of clause A. CaDiCaL compensates via more frequent vivification
/// rounds; AY compensates via deeper per-clause retries.
pub(super) const VIVIFY_RETRY_LIMIT: u32 = 3;

/// Threshold (original clause count) for sqrt-scaled vivify tick threshold
/// capping (#8655). On BMC formulas with millions of clauses, the linear
/// `VIVIFY_TICK_THRESHOLD * active_clause_count` grows to billions of ticks,
/// preventing vivification from ever firing during search. Sqrt scaling
/// ensures vivification remains accessible: 1M clauses => sqrt(1M) = 1000,
/// threshold = 20 * 1000 = 20K ticks (vs linear 20M ticks).
pub(super) const VIVIFY_LARGE_FORMULA_SQRT_THRESHOLD: usize = 100_000;

/// Probe effort scaling factor for large structured formulas (#8655).
/// BMC formulas at depth 50+ produce dense binary implication graphs.
/// Scale probe effort to 2.5% for formulas above the large formula threshold,
/// matching Kissat's `probeeffort=100` scaling.
pub(super) const PROBE_LARGE_FORMULA_EFFORT_PERMILLE: u64 = 25;

// ─── Subsumption ─────────────────────────────────────────────────────

/// Run subsumption after this many conflicts.
/// CaDiCaL runs forward subsumption as part of elimination (not a separate pass).
/// Reduced from 20K to 10K (#8099): with incremental state maintenance and
/// adaptive tick-threshold scaling, the per-round overhead is lower, so
/// subsumption can fire more frequently. The adaptive backoff (1.5x growth on
/// progress, 2x on idle) still naturally reduces frequency on unproductive rounds.
/// On large formulas, the density guard and tick-threshold gating prevent waste.
pub(super) const SUBSUME_INTERVAL: u64 = 10_000;

/// Subsumption effort as per-mille of search propagations.
/// CaDiCaL: `subsumeeffort = 1000` (options.hpp:218).
pub(super) const SUBSUME_EFFORT_PER_MILLE: u64 = 1_000;

/// Maximum subsumption check limit per call.
/// CaDiCaL: `subsumemaxeff = 1e8` (options.hpp:220).
pub(super) const SUBSUME_MAX_EFFORT: u64 = 100_000_000;

/// Minimum subsumption check limit per call.
/// CaDiCaL: `subsumemineff = 0` (options.hpp:221).
pub(super) const SUBSUME_MIN_EFFORT: u64 = 0;

/// Speculative subsumption effort ceiling (#8099).
/// When subsumption fires as part of a speculative mini-round (e.g., between
/// BVE interleaving rounds or post-vivify), limit effort to this value to
/// bound latency. This is lower than the full subsumption effort so that
/// speculative rounds complete quickly and yield progress data for scheduling.
/// 1000 clause inspections is ~0.1ms on typical formulas.
pub(super) const SUBSUME_SPECULATIVE_EFFORT: u64 = 1_000;

/// Maximum subsumption scheduling interval (conflicts).
/// With 1.5x growth from 10k: 10k, 15k, 22.5k, 33.75k, 50.6k, 75.9k, ...
/// Caps at 80k to prevent starvation on long runs while reducing overhead on
/// structured instances. Halved from 160K proportionally with the base
/// interval reduction from 20K to 10K (#8099).
pub(super) const SUBSUME_MAX_INTERVAL: u64 = 80_000;

/// Maximum subsumption interval when rounds make no database progress.
/// On hard structured formulas, no-op rounds are often net-negative; allow
/// a longer cooldown before retrying subsumption. Halved from 320K
/// proportionally with the base interval reduction (#8099).
pub(super) const SUBSUME_MAX_IDLE_INTERVAL: u64 = 160_000;

/// Active-clause threshold for large-sparse no-progress subsumption cooldown.
///
/// Large sparse Main-track instances can sit below the global expensive-pass
/// skip gates while still paying an O(clauses) candidate setup cost for
/// subsumption. Once a round on this shape produces no deletions or
/// strengthenings, retry less frequently and let CDCL search spend the budget.
pub(super) const SUBSUME_LARGE_SPARSE_MIN_ACTIVE_CLAUSES: usize = 500_000;

/// Maximum active-clause / active-variable density for the large-sparse
/// cooldown. Kept integral to make the hot scheduling predicate allocation-free.
pub(super) const SUBSUME_LARGE_SPARSE_MAX_DENSITY: usize = 20;

/// Maximum no-progress subsumption interval for large sparse or explicitly
/// skipped expensive formulas.
pub(super) const SUBSUME_LARGE_MAX_IDLE_INTERVAL: u64 = 500_000;

// ─── Probing ─────────────────────────────────────────────────────────

/// Run failed literal probing after this many conflicts (was 15000, reduced for BV #757)
/// Note: 100 was too aggressive; 1000 is 15x more frequent but avoids dominating solve time
pub(super) const PROBE_INTERVAL: u64 = 1000;

// ─── Backbone Computation ───────────────────────────────────────────

/// Backbone inprocessing interval (in conflicts).
/// CaDiCaL runs backbone interleaved with probing (backbone.cpp:622).
/// Same interval as probing since backbone is a probing-like technique.
pub(super) const BACKBONE_INTERVAL: u64 = 2000;

/// Maximum backbone interval under growing backoff.
/// Keeps unproductive restart-level backbone passes from stretching indefinitely.
pub(super) const BACKBONE_MAX_INTERVAL: u64 = 64_000;

/// Maximum number of backbone rounds (phases) before backbone is permanently disabled.
/// CaDiCaL: `backbonerounds = 100` scaled by phase count, capped at
/// `backbonemaxrounds = 1000` (options.hpp:30-31). AY uses a simpler flat
/// limit matching CaDiCaL's `backbonemaxrounds` default.
pub(super) const BACKBONE_MAX_ROUNDS: u32 = 1_000;

/// Maximum number of consecutive backbone invocations that find zero new
/// backbone literals before backbone is permanently disabled (#8150).
/// When backbone probing repeatedly fails to discover new fixed literals,
/// further attempts are unlikely to succeed and waste CPU on bounded CDCL
/// probes. CaDiCaL handles this implicitly via candidates running out;
/// AY's CDCL-based backbone re-scans all variables each round, so an
/// explicit stall limit is necessary.
/// Value 2: after 2 consecutive empty rounds with growing backoff (1.5x),
/// cumulative wasted effort is bounded at ~3.5x the base interval.
/// Reduced from 3 (#8448): on EDP3-11000 (91K vars, 680K clauses),
/// 3 unproductive backbone rounds cost 550ms — enough to push the
/// solve from 14.5s to 15.3s (over the 15s target). With 2 rounds
/// the wasted effort is ~370ms, saving the critical margin.
/// FmlaEquivChain also wastes 2.8s on backbone with only 1 unit found
/// across 3 rounds. Two rounds still give backbone a chance to find
/// low-hanging fruit; three rounds just burns time on formulas where
/// backbone has no structural leverage.
///
/// (#8448 Wave A Phase 1) Raised from 2 to 3 to match CaDiCaL's latitude.
/// CaDiCaL's `backbonerounds=100` (`reference/cadical/src/options.hpp:31`)
/// allows far more rounds before giving up; its stall semantics are
/// governed by the `backboneeffort` ticks budget rather than consecutive
/// empty rounds. AY still uses the stall-count semantic but restores the
/// pre-#8448 tolerance of 3 consecutive empty rounds so formulas that
/// need two warmup rounds before finding backbone units are not cut off.
/// The wall-clock cap per call still protects against pathological cost.
pub(super) const BACKBONE_STALL_LIMIT: u32 = 3;

/// Maximum consecutive HTR rounds that produce zero resolvents before
/// permanently disabling HTR for the instance (#8448).
/// On EDP3 (91K vars, 680K clauses), 3 HTR rounds with 0 resolvents
/// cost 554ms. Unlike backbone which has a 200ms wall-clock cap per
/// call, HTR has no per-call limit. Set to 1 (more aggressive than
/// BACKBONE_STALL_LIMIT=2): HTR gets one chance to find resolvents;
/// if the first inprocessing round finds nothing, subsequent rounds
/// are very unlikely to find anything because the formula structure
/// hasn't changed enough between rounds to create new ternary
/// resolution opportunities.
pub(super) const HTR_STALL_LIMIT: u32 = 1;

// ─── Bounded Variable Elimination ────────────────────────────────────

/// BVE inprocessing base interval (in conflicts).
/// CaDiCaL uses `elimint=2000` scaled by clause/variable ratio and
/// growing linearly with each phase: `elimint * (phases + 1) * scale()`.
/// Use 2000 to match CaDiCaL's base frequency more closely on SAT workloads.
pub(super) const BVE_INTERVAL_BASE: u64 = 2_000;

/// Maximum number of variable eliminations per BVE call.
/// CaDiCaL uses a resolution-count limit instead of a fixed count.
/// We use a generous per-call cap; the growth bound and occurrence
/// limit handle actual pruning.
pub(super) const MAX_BVE_ELIMINATIONS: usize = 100_000;

/// Maximum variables to attempt elimination per inprocessing BVE round (#8099).
/// Instead of iterating all candidates, partial BVE caps per-round attempts to
/// the N cheapest variables (lowest occurrence count). This bounds per-round
/// wall-clock time while still making progress across rounds.
/// CaDiCaL achieves similar behavior via effort-limited rounds; AY adds an
/// explicit candidate cap for more predictable per-round latency.
/// Only applies during inprocessing (not preprocessing fastelim).
///
/// Increased from 500 to 5000 (#7998): the resolution effort budget already
/// bounds per-round work matching CaDiCaL's behavior. The previous 500 cap
/// was too restrictive — many candidates fail the growth bound check quickly
/// (no resolution work), but the cap counted them toward the limit. This left
/// profitable eliminations on the table, reducing search space shrinkage.
/// On medium formulas (10K-50K vars), 500 candidates covers only 1-5% of
/// variables per round, while CaDiCaL processes all candidates within budget.
pub(super) const BVE_PARTIAL_CANDIDATES_PER_ROUND: usize = 5_000;

/// Per-call elimination cap for preprocessing fastelim.
/// CaDiCaL's fastelim runs until the resolution budget is exhausted or
/// Maximum variable eliminations per fastelim call. With watch-free BVE
/// mode (watches disconnected during preprocessing), per-elimination
/// overhead is ~2x CaDiCaL's (down from 16x). CaDiCaL has no cap
/// (effort-limited only). Remove the artificial ceiling so preprocessing
/// can eliminate 30-50% of variables on BVE-dominated formulas.
pub(super) const FASTELIM_MAX_ELIMINATIONS: usize = 100_000;

/// Maximum number of BVE rounds per inprocessing call.
/// Kissat: eliminaterounds=2. AY grows the growth_bound between inner
/// rounds (Kissat-style progressive bound, eliminate.c:339-372), so 3
/// rounds lets the bound progress from 0 to 2 within a single BVE phase.
/// This is critical for structured formulas like clique graphs where many
/// variables are only profitably eliminable at bound >= 1 (#8135).
pub(super) const BVE_ROUNDS: usize = 3;

/// Maximum number of BVE rounds during preprocessing fastelim.
/// CaDiCaL: fastelimrounds=4 (options.hpp:131). With watch-free BVE mode,
/// per-round overhead is low enough to afford 4 rounds with interleaved
/// subsumption. Variables exposed by earlier rounds are picked up by later
/// rounds, matching CaDiCaL's multi-round fastelim behavior.
pub(super) const PREPROCESS_BVE_ROUNDS: usize = 4;

/// Resolution effort as per-mille of search propagations.
/// CaDiCaL: `elimeffort = 1000` (options.hpp:93).
pub(super) const BVE_EFFORT_PER_MILLE: u64 = 1_000;

/// Suppress inprocessing BVE when irredundant clause count exceeds this
/// factor times the baseline recorded after the last BVE phase (#8135).
/// On clique_n2_k10, inprocessing BVE inflates irredundant clauses from
/// 1409 to 148K+ in repeated rounds with zero useful eliminations. This
/// guard prevents BVE from re-firing when a previous phase inflated the DB.
pub(super) const BVE_GROWTH_INHIBIT_FACTOR: usize = 2;

/// Minimum resolution effort (resolutions) for inprocessing.
/// CaDiCaL: `elimmineff = 1e7` (options.hpp:99).
pub(super) const BVE_MIN_EFFORT: u64 = 10_000_000;

/// Resolution effort for preprocessing fastelim.
/// With watch-free BVE mode (Phase 1 of BVE perf design), per-resolution
/// overhead is ~2x CaDiCaL's (down from 16x). Match CaDiCaL's minimum
/// effort budget. CaDiCaL: `elimmineff = 1e7` (options.hpp:99).
pub(super) const FASTELIM_EFFORT: u64 = 10_000_000;

/// Clause count threshold for scaling down fastelim effort (#8136).
pub(super) const FASTELIM_SCALE_CLAUSE_THRESHOLD: u64 = 1_000_000;

/// Minimum scaled fastelim effort after clause-count scaling (#8136).
pub(super) const FASTELIM_MIN_SCALED_EFFORT: u64 = 2_000_000;

/// Wall-clock time limit (seconds) for preprocessing BVE rounds (#8136, #8448).
/// Reduced from 3s to 2s. Each call to bve() starts its own timer that
/// includes the O(clauses) occ-list rebuild. On large formulas (4.7M clauses),
/// the rebuild alone costs ~1s, so the effective elimination time per pass
/// is only (FASTELIM_WALL_CLOCK_LIMIT_SECS - rebuild_cost). With max_rounds=1
/// for >3M clause formulas, the round-level guard never fires; only the
/// intra-round check (every 64 eliminations) enforces this limit.
pub(super) const FASTELIM_WALL_CLOCK_LIMIT_SECS: u64 = 2;

// ---------------------------------------------------------------------------
// Sparse-band DEEP preprocess-BVE lever (kill-switched, default ON since
// 2026-07-10 wf_55735963; AY_AB_BVE_SPARSE_DEEP=0 disables).
//
// Scoped to the sparse-band large-formula unlock (density<=12,
// num_vars>BVE_SPARSE_DEEP_MIN_VARS, non-LRAT Default route) or the
// post-collapse composition (see bve_sparse_deep_active). On the prize
// huge-sparse instances (e.g. 1.69M
// vars/5.96M clauses, density 3.5) the default fastelim path stops after
// eliminating ~2.5% of variables because a single bve() call dies on the 2s
// FASTELIM_WALL_CLOCK_LIMIT_SECS guard (the DOMINANT limiter — measured
// exit_wall=1, zero gate rejections), with the per-round resolution effort
// (~3.38M) as the second-order limiter, and max_rounds=1 for >3M-clause
// formulas suppressing the propagate/subsume cascade. These constants raise
// the wall, effort, and round count *only* for that scoped band so BVE can
// approach kissat-style dense elimination. Cost stays bounded by
// BVE_SPARSE_DEEP_PREPROCESS_BUDGET_SECS and the deep wall; the default
// competition config (env unset, 150K var cap) never engages this path.
// ---------------------------------------------------------------------------

/// Minimum var count for the DEEP lever. Below this, formulas fit the default
/// sparse band (<=150K vars) where the non-deep unlock already performs well
/// and deep would only waste time; deep targets the huge formulas that enter
/// only when the operator raises --sat-bve-sparse-max-vars above the default.
///
/// DO NOT LOWER THIS TO CHASE MEDIUM SAT LOSSES — measured negative
/// (wf_13a96c15, replicating wf_eab7d219 / wf_e2bdf6e1). Lowering the floor
/// via AY_BVE_SPARSE_DEEP_MIN_VARS to engage the deep re-elimination cascade
/// on the medium sparse SAT losses 5dbe7b31 (77K vars) and cdd89d1b (24K
/// vars) flips NOTHING: 5dbe UNKNOWN 1005->1024 elim (+19), cdd UNKNOWN
/// 7227->7227 (byte-identical, +0), both still UNKNOWN at 120s while kissat
/// solves them SAT. The blocker is yield-per-attempt, NOT round count or the
/// floor: AY already re-attempts vars at kissat-comparable-or-higher rates
/// (1.77-3.38 try-attempts/var vs kissat 2.49) but eliminates at ~1/14th the
/// yield (0.7% vs 9.7%). The deep cascade infra is provably inert on medium
/// formulas — see the inter-round propagate note in inprocessing/bve/body.rs
/// (it sits after the `candidates_exhausted` break, and medium formulas drain
/// their schedule in round 0, so it never fires; where it does run, in
/// inprocessing rounds, pending_units is 0 so it is a no-op). kissat's
/// dominant removal on these is upstream substitution (~32%) + units (~58%),
/// NOT BVE re-elimination (its smallest channel, 24%); pursuing these losses
/// means enabling the substitution/congruence collapse (bve_post_collapse)
/// for sub-200K formulas — a SEPARATE lever, not this floor. The
/// AY_BVE_SPARSE_DEEP_MIN_VARS override remains for VALIDATION of the deep
/// reconstruction/proof path only, not as a competition tuning knob.
pub(super) const BVE_SPARSE_DEEP_MIN_VARS: usize = 150_000;

/// Per-bve()-call wall-clock limit (seconds) for the DEEP lever. Replaces the
/// 2s FASTELIM_WALL_CLOCK_LIMIT_SECS at the round-level and intra-round guards
/// so a single fastelim pass can sweep far more of the candidate pool.
pub(super) const BVE_SPARSE_DEEP_WALL_SECS: u64 = 8;

/// Per-bve()-call elimination cap for the DEEP lever (raises the 100K
/// FASTELIM_MAX_ELIMINATIONS ceiling so deep can accumulate past it).
pub(super) const BVE_SPARSE_DEEP_MAX_ELIMINATIONS: usize = 1_500_000;

/// Cumulative preprocess-BVE wall budget (seconds) for the DEEP lever, used by
/// the config-level Pass-1 / gate-pass admission checks (which measure from the
/// run_preprocess_bve-level timer, spanning Pass 0 + Pass 1). Allows Pass 1
/// (bound 16) to start after Pass 0 (quick-elim) already spent up to the deep
/// per-call wall.
pub(super) const BVE_SPARSE_DEEP_TOTAL_WALL_SECS: u64 = 16;

/// Total preprocessing budget (seconds) for the DEEP band. Overrides the
/// FormulaClass::Large 2s budget so `preprocess_timed_out()` does not cut the
/// deep BVE short. For num_vars>200K formulas the shared expensive passes are
/// already skipped, so this budget is effectively spent only on BVE.
///
/// PROOF-ROUTE ROOT CAUSE (measured 2026-07-10, wf_55735963 + the
/// wf_0552d0f0 measurement round): with DRAT emission active (`--proof`),
/// the deep collapse+BVE path is NOT routed away — `bve_sparse_deep_active()`
/// has no proof predicate and the pipeline RUNS — but it is TRUNCATED
/// mid-flight, because this budget is WALL-CLOCK while DRAT step-tracking
/// inflates the per-step cost of the collapse+BVE work ~4x. On df813fe7
/// (521K vars; unknown->UNSAT@80s with 188,557 eliminations in the no-proof
/// scoreboard config) a --proof run reaches only cong_rounds=1,
/// equivs=60,923, bve_elim=4,473 before the deadline fires and the solve
/// ends unknown@120s. The deep-path flips are therefore not yet
/// proof-carrying; SAT-COMP requires UNSAT proofs, so closing this gap is
/// campaign-relevant.
///
/// The same wall-clock-vs-proof-overhead mechanism binds IN-BAND flips too:
/// 70da0b78 (68K vars, unsat 1.8s no-proof via 32K BVE elims + 24K equivs)
/// ran >180s unknown under --proof in the wf_55735963 G4 check — there the
/// binding constant is FASTELIM_WALL_CLOCK_LIMIT_SECS (2s wall) rather than
/// this budget. 96dea345 (pure congruence, 17.8s no-proof) likewise.
///
/// PROOF-ROUTE UNLOCK (wf_0c7d84e9, 2026-07-10): the budget is now scaled by
/// `Solver::bve_wall_budget_scale()` (PROOF_WALL_BUDGET_SCALE = 4x when
/// `self.proof_manager.is_some()`, matching the measured DRAT step-tracking
/// overhead) at every wall-clock consumer: the deep preprocess budget raise,
/// the post-collapse deadline extensions, the Pass-1 admission wall, and the
/// per-call/intra-round fastelim wall in bve/body.rs. Sound by construction —
/// budgets schedule work, never truth; verdicts stay guarded by DRAT
/// verification itself. Behavior-neutral for non-proof runs (scale == 1).
/// Gate-verified in wf_0c7d84e9 alongside the proof_ladder rung-watch fix
/// (external dpr-trim/cake_lpr chain on the collapse flips).
///
/// SECOND proof-route blocker — RESOLVED (wf_0c7d84e9, 2026-07-10): the
/// wf_55735963 G4 dpr-trim rejection on f0bafebd ("RAT check on proof pivot
/// failed: [51477] 1163 -2820", line 26774) was root-caused to congruence
/// XOR-ladder rungs attached with BINARY watches (proof_ladder.rs
/// insert_ladder_rung) — a deleted rung husk kept its binary watch, vivify
/// propagated a proof-less level-0 unit through it, and
/// collect_level0_garbage baked that phantom unit into strengthened clauses
/// the checker rejects. Fixed emission-side (watch by length), pinned by a
/// debug_assert in attach_clause_watches, and externally re-verified
/// (dpr-trim + cake_lpr) on f0bafebd, braun10/12 and the collapse flips.
/// The AUTO default (variant.rs subst_auto_collapse_enabled) is back to
/// registry truth: ON under DRAT, fail-closed under LRAT only.
pub(super) const BVE_SPARSE_DEEP_PREPROCESS_BUDGET_SECS: u64 = 20;

/// Wall-clock budget multiplier for the preprocess-BVE walls when DRAT proof
/// emission is active (`Solver::bve_wall_budget_scale`). DRAT step-tracking
/// inflates the per-step cost of the collapse+BVE work ~4x (measured
/// wf_55735963/wf_0552d0f0: df813fe7 reaches 188,557 eliminations no-proof
/// but only 4,473 under --proof inside the same wall; 70da0b78 binds the
/// same way on FASTELIM_WALL_CLOCK_LIMIT_SECS). Scaling the WALLS by the
/// measured overhead keeps the WORK admitted per pass roughly equal between
/// proof and non-proof runs — a scheduling change only, never a soundness
/// one, and exactly neutral (scale 1) when no proof is being emitted.
pub(super) const PROOF_WALL_BUDGET_SCALE: u64 = 4;

/// Max BVE rounds for the DEEP lever, overriding the 1/2 round cap for
/// >1M-clause formulas so the inter-round subsume + occ-refresh cascade (which
/// exposes the bulk of kissat's eliminable variables) can fire.
pub(super) const BVE_SPARSE_DEEP_ROUNDS: usize = 4;

/// Per-round resolution effort for the DEEP lever = active_vars * this factor,
/// clamped to [FASTELIM_EFFORT, BVE_SPARSE_DEEP_EFFORT_CAP]. Sized toward
/// kissat parity (~15M resolutions/round on the prize instance) so the
/// second-order budget_exhausted limiter stops throttling once the wall lifts.
pub(super) const BVE_SPARSE_DEEP_EFFORT_PER_VAR: u64 = 16;

/// Upper clamp on the DEEP per-round resolution effort.
pub(super) const BVE_SPARSE_DEEP_EFFORT_CAP: u64 = 48_000_000;

/// Wall-clock time limit (milliseconds) for inprocessing BVE per-call (#8078).
pub(super) const BVE_INPROCESSING_WALL_LIMIT_MS: u64 = 200;

/// Skip preprocessing BVE above this active clause count + high density (#8136).
pub(super) const PREPROCESS_BVE_SKIP_CLAUSE_THRESHOLD: usize = 2_000_000;

/// Minimum clause/variable density to trigger preprocessing BVE skip (#8136).
pub(super) const PREPROCESS_BVE_SKIP_DENSITY: f64 = 20.0;

/// Density-only BVE skip threshold for small dense formulas.
/// On formulas like stable-300 (300 vars, 17540 clauses, density 58.5),
/// BVE produces more resolvents than it eliminates because the high
/// clause-per-variable ratio means every elimination generates O(density^2)
/// resolvents. The existing density guard (PREPROCESS_BVE_SKIP_DENSITY=20)
/// requires >2M clauses to fire. This threshold catches small dense formulas
/// where BVE is equally counterproductive. CaDiCaL handles this implicitly
/// via per-variable cost estimation, but AY's BVE still grows the clause DB
/// at these density levels.
pub(super) const BVE_HIGH_DENSITY_SKIP: f64 = 50.0;

// BW subsumption history (#8179, #8448, #8466):
// Previously gated by BW_SUBSUME_ENABLED=false due to DRAT proof ordering
// bugs (false UNSAT on ecarev-110). Now gated by !has_proof_output in
// bve/body.rs — the solver-soundness path (no proof) is correct, only the
// proof emission path has the ordering bug. See bve/body.rs backward
// subsumption block for the current gate.

/// Maximum cascade rounds for backward subsumption after BVE (#8367, #8448).
/// CaDiCaL backward.cpp:202 re-enqueues strengthened clauses for another
/// backward pass. AY implements this via iterative rounds: each round runs
/// batched backward subsumption, applies results, then uses strengthened
/// clauses as sources for the next round.
///
/// (#8448) Reduced from 4 to 1. The initial backward subsumption round
/// captures the primary benefit; subsequent cascade rounds have diminishing
/// returns on formulas where clause overlap is sparse. On ecarev-110
/// (741K clauses, 3140 eliminations), 4 cascade rounds inflated BVE from
/// ~1.5s to ~4s, pushing total solve time past 15s.
///
/// (#8448 Wave A Phase 1) Restored to 4 to match CaDiCaL's backward
/// subsumption cascade depth (`reference/cadical/src/backward.cpp:202`
/// re-enqueues strengthened clauses until the schedule is empty; 4 is
/// the empirical convergence depth on typical formulas). The ecarev-110
/// pathology that motivated the drop to 1 is now gated by the outer
/// `!has_proof_output` check in `bve/body.rs` and the batched cascade
/// budget (`BW_CASCADE_MAX_ROUNDS as usize * initial_queue_len`), which
/// keeps per-round work bounded. Cascade depth itself is pure perf.
pub(super) const BW_CASCADE_MAX_ROUNDS: u32 = 4;

/// Maximum resolution effort (resolutions).
/// CaDiCaL: `elimmaxeff = 2e9` (options.hpp:98).
pub(super) const BVE_MAX_EFFORT: u64 = 2_000_000_000;

/// Maximum interleaved elimination phase rounds (BVE → subsume → BCE → CCE).
/// CaDiCaL runs up to `elimrounds=2` BVE rounds with interleaved
/// subsumption, BCE, and CCE between them (elim.cpp:1060-1098). Each round
/// creates new elimination candidates: BVE produces resolvents that
/// subsumption can simplify, BCE/CCE remove blocked/covered clauses that
/// reduce occurrence counts, and those removals enable further BVE.
/// The loop exits when no technique produces new candidates.
///
/// Set to 3 (vs CaDiCaL's `elimrounds=2`): on formulas like FmlaEquivChain
/// (54K vars, 438K clauses), the BVE+subsume cascade needs a third round to
/// reach fixpoint. Subsumption between rounds 1→2 creates new BVE candidates
/// that a third round exploits, extracting ~1000 additional eliminations per
/// inprocessing call and reducing the total number of inprocessing calls
/// needed. The loop still exits early when no candidates are produced, so
/// the third round is free on formulas that converge in 2 rounds (#8134).
pub(super) const ELIM_INTERLEAVE_ROUNDS: usize = 3;

// ─── Blocked Clause Elimination ──────────────────────────────────────

/// Run BCE after this many conflicts.
/// Reduced from 25K to 12K (#8099): BCE is a lightweight pass that benefits
/// from more frequent firing. The tick-threshold gate (#8148) prevents
/// redundant calls when search ticks haven't advanced enough.
pub(super) const BCE_INTERVAL: u64 = 12_000;

/// Maximum number of blocked clause eliminations per call
pub(super) const MAX_BCE_ELIMINATIONS: usize = 200;

/// BCE effort as per-mille of search ticks delta (#8148).
/// CaDiCaL runs BCE inside the BVE elimination loop (block.cpp) so it
/// shares the BVE effort budget. AY runs BCE standalone, so it needs its
/// own tick-proportional budget. 10 per-mille = 1% of search ticks since
/// the last BCE call.
pub(super) const BCE_EFFORT_PER_MILLE: u64 = 10;

/// Minimum BCE effort (clause checks) per call.
/// Ensures BCE does meaningful work even when called shortly after the
/// previous invocation (small tick delta).
pub(super) const BCE_MIN_EFFORT: usize = 50;

/// Maximum BCE effort (clause checks) per call.
/// Prevents BCE from consuming unbounded time on instances with very
/// high tick deltas. 100K checks is generous for practical clause DBs.
pub(super) const BCE_MAX_EFFORT: usize = 100_000;

// ─── Covered Clause Elimination (CCE) ────────────────────────────────

/// Run CCE after this many conflicts. Same interval as BCE.
/// CaDiCaL defaults `opts.cover = false`, so CCE only runs when explicitly
/// enabled. Uses the same reconstruction stack format as BCE.
pub(super) const CCE_INTERVAL: u64 = 25000;

/// CCE effort as per-mille of search propagations.
/// CaDiCaL: `covereffort = 4` (options.hpp). 4 per-mille = 0.4%.
pub(super) const CCE_EFFORT_PER_MILLE: u64 = 4;

/// Minimum CCE effort (clause scans) per call.
/// CaDiCaL: `covermineff = 0` (options.hpp).
pub(super) const CCE_MIN_EFFORT: u64 = 0;

/// Maximum CCE effort (clause scans) per call.
/// CaDiCaL: `covermaxeff = 1e8` (options.hpp).
pub(super) const CCE_MAX_EFFORT: u64 = 100_000_000;

// ─── Conditioning (GBCE) ─────────────────────────────────────────────

/// Run conditioning (GBCE) after this many conflicts
pub(super) const CONDITION_INTERVAL: u64 = 10000;

/// Maximum number of conditioned clause eliminations per call
pub(super) const MAX_CONDITION_ELIMINATIONS: usize = 100_000;

// ─── Congruence Closure ──────────────────────────────────────────────

/// Run congruence closure (gate-based equivalence detection) after this many conflicts.
/// CaDiCaL effective rate: ~once per 587 conflicts (15 rounds in 8K conflicts).
/// Previous value 10000 was 17x too infrequent. CaDiCaL: `congruence.cpp`.
pub(super) const CONGRUENCE_INTERVAL: u64 = 2000;

/// Maximum congruence scheduling interval after exponential backoff.
/// CaDiCaL uses exponential backoff: each fruitless call doubles the delay.
/// On shuffling-2 (4.9M clauses), congruence was running every 2K conflicts
/// on a 63K-conflict solve, causing ~31 × 1.5s = 46s of wasted work (#7135).
/// With 2× growth from 2K: 2K → 4K → 8K → 16K → 32K → 64K — only 5 calls.
pub(super) const CONGRUENCE_MAX_INTERVAL: u64 = 64_000;

// ─── Decompose (SCC) ─────────────────────────────────────────────────

/// Run decompose (SCC equivalent literal substitution) after this many conflicts
pub(super) const DECOMPOSE_INTERVAL: u64 = 10000;

/// Maximum decompose scheduling interval after growing backoff.
/// Unproductive decompose calls (no equivalences found) grow the interval 1.5×.
/// Productive calls reset to base. CaDiCaL: decompose uses Delay struct.
/// With 1.5× growth from 10K: 10K → 15K → 22K → 33K → 50K → 75K → 100K.
pub(super) const DECOMPOSE_MAX_INTERVAL: u64 = 100_000;

// ─── Factorization ───────────────────────────────────────────────────

/// Run factorization after this many conflicts.
/// CaDiCaL runs factoring after BVE; we fire on the same schedule.
pub(super) const FACTOR_INTERVAL: u64 = 10000;

/// Maximum factor scheduling interval after growing backoff.
/// Unproductive factor calls (0 factored clauses) grow the interval 1.5×.
/// Productive calls reset to base. CaDiCaL: factor uses Delay struct.
pub(super) const FACTOR_MAX_INTERVAL: u64 = 100_000;

/// Delay factorization until enough elimination rounds have run.
/// CaDiCaL option parity: `factordelay = 4` (options.hpp).
pub(super) const FACTOR_DELAY: u64 = 4;

/// Factor effort as per-mille of search ticks since last factor call.
/// CaDiCaL: `factoreffort = 50` (options.hpp:122). 50 per-mille = 5%.
pub(super) const FACTOR_EFFORT_PERMILLE: u64 = 50;

/// Initial factor effort bonus (ticks) for inprocessing.
/// CaDiCaL: `factoriniticks = 300` (options.hpp:123) in millions.
/// CaDiCaL ticks include cache-line overhead (~13x per scan vs AY's
/// 1-tick-per-clause-access), so 300M CaDiCaL ≈ 23M AY-equivalent.
/// During inprocessing the proportional budget dominates; this bonus
/// only matters for the first call after search starts.
///
/// #14-factor-cost: ticks are charged HONESTLY (one per clause visit and per
/// occ-list element visit), so this budget genuinely binds.
///
/// #rank6 recalibration: EMPIRICAL measurement on main-track 82851650
/// (474k clauses, density 103, the dense-ternary flagship the
/// AY_AB_FACTOR_DENSE unlock targets) with the incremental PQ driver
/// (single occ build + schedule, phase-2-merged find_next_factor,
/// incremental occ maintenance): the FULL productive factoring — schedule
/// drained to completion, 204 factors, converts a timeout into
/// s UNSATISFIABLE in ~3s wall — consumes 230.8M honest ticks
/// (budget=600M consumed=230_805_525 completed=true). 500M ≈ measured
/// need x2 margin. The former 3-pass driver needed ~450M honest ticks
/// (phase-2 rescans double-charged the same discovery) and 47s wall for
/// 219 factors on the same instance.
pub(super) const FACTOR_INIT_TICKS: u64 = 500_000_000;

/// Maximum factor effort per call.
/// #rank6 recalibration: 1B ≈ 4.3x the measured full-factoring need on the
/// 82851650 flagship (230.8M honest ticks — see FACTOR_INIT_TICKS). The
/// proportional inprocessing budget (5% of search ticks) only reaches this
/// cap after 20B search ticks, so it bounds pathological accumulation
/// without clipping productive calls. Was 2B, calibrated to the former
/// 3-pass driver whose honest tick need (~450M) was ~2x the incremental
/// driver's.
pub(super) const FACTOR_MAX_EFFORT: u64 = 1_000_000_000;

/// First-call factor init budget for the DENSE band (density >=
/// [`FACTOR_DENSE_MIN_DENSITY`]), replacing [`FACTOR_INIT_TICKS`]'s 500M on
/// the first (`factor_rounds == 0`) call only. Kill-switched via
/// `--sat-no-factor-dense-init` (restores 500M) and A/B-tunable via
/// `AY_FACTOR_DENSE_INIT_TICKS` — see
/// `config_preprocess_policy::factor_dense_init_ticks`.
///
/// #factor-dense-init measurement (46355da78571, 4608 vars, 825 728 clauses,
/// density 179.2, UNSAT): the full productive factoring on this dense band
/// drains the schedule to completion at 591M honest ticks → 318 factorings
/// (kissat parity: 318) → timeout becomes s UNSATISFIABLE at 5155 conflicts
/// (kissat 5263) in ~2.8s. The former 500M init truncated the schedule
/// mid-drain at 76 factorings (12% of discovery) → unbounded search /
/// timeout. 1B (== [`FACTOR_MAX_EFFORT`], the sanctioned per-call ceiling)
/// lets the dense first call drain instead of clipping; the schedule stops
/// itself at the natural drain point (591M here) so the extra budget is
/// consumed only where productive. Also 8x on a2fe3213 (density 171, SAT
/// 75.5s→9.3s, 1.09M→81.8K conflicts). SCOPED to the dense band because
/// sub-90 factoring drains well under 500M (nothing to raise) and the
/// moderate-density band is search-fragile (see FACTOR_DENSE_MIN_DENSITY).
pub(super) const FACTOR_DENSE_INIT_TICKS: u64 = 1_000_000_000;

/// Upper residual-size bound (active clauses at the first factor call) for the
/// dense-band init raise [`FACTOR_DENSE_INIT_TICKS`]. The raise targets the
/// SMALL dense highly-factorable class (extension variables compress it):
/// 46355da (825 728 clauses, factor 318), a2fe3213 (1 262 871, factor 320),
/// 82851650 (474 496, factor 326). Above ~3M clauses factoring is marginal
/// (the O(clauses) occ-list build alone costs 10+ seconds — see the >3M
/// residual guards in solve/inprocessing_elimination.rs) and the extra budget
/// only perturbs search: on 0ec8c5e9 (21 161 364 clauses, 58 983 vars, density
/// 359, factor 3) the raise flipped a boundary SAT@88s into a 120s timeout
/// with the SAME 3 factors — pure search perturbation, zero factoring gain.
/// Capping at 3M keeps every measured win (all < 1.3M, ≥2.4x margin) and
/// excludes 0ec8c5e9 (7x over) and the density-264 cluster (f6a085f3 /
/// 6ff70a3a ≈ 11M, which don't solve at any budget). A/B-tunable via
/// `AY_FACTOR_DENSE_INIT_MAX_CLAUSES`.
pub(super) const FACTOR_DENSE_INIT_MAX_CLAUSES: usize = 3_000_000;

// ─── SBVA (Structured Bounded Variable Addition) ────────────────────

/// Run SBVA after this many conflicts.
/// SBVA runs after factorization; same schedule class as factor.
/// Lowered from 15K to 10K (#8099): with reduced per-round overhead,
/// SBVA benefits from running in sync with factor (both at 10K).
pub(super) const SBVA_INTERVAL: u64 = 10_000;

/// Maximum SBVA scheduling interval after growing backoff.
/// Lowered from 150K to 100K proportionally with the base interval
/// reduction from 15K to 10K (#8099).
pub(super) const SBVA_MAX_INTERVAL: u64 = 100_000;

/// SBVA effort as per-mille of search ticks since last SBVA call.
/// Conservative: 30 per-mille = 3% (less than factor's 5%, since SBVA
/// has higher per-candidate cost from subset intersection).
pub(super) const SBVA_EFFORT_PERMILLE: u64 = 30;

/// Initial SBVA effort bonus for the first call.
pub(super) const SBVA_INIT_TICKS: u64 = 200_000_000;

/// Maximum SBVA effort per call.
pub(super) const SBVA_MAX_EFFORT: u64 = 1_000_000_000;

// ─── Transitive Reduction ────────────────────────────────────────────

/// Run transitive reduction after this many conflicts.
/// Lowered from 15K to 10K (#8099): transred is O(binary_clauses) and
/// relatively lightweight. With reduced per-round overhead, more frequent
/// transred catches redundant binary implications sooner.
pub(super) const TRANSRED_INTERVAL: u64 = 10_000;

/// Transred effort as per-mille of search propagations since last transred.
/// CaDiCaL: `transredeffort = 100` (options.hpp:250). 100 per-mille = 10%.
/// CaDiCaL transred uniquely uses propagations (not ticks) for effort.
pub(super) const TRANSRED_EFFORT_PERMILLE: u64 = 100;

/// Maximum transred effort (propagations).
/// CaDiCaL: `transredmaxeff = 1e8` (options.hpp:251).
pub(super) const TRANSRED_MAX_EFFORT: u64 = 100_000_000;

/// Minimum transred effort (propagations).
/// CaDiCaL: `transredmineff = 0` (options.hpp:252).
pub(super) const TRANSRED_MIN_EFFORT: u64 = 0;

// ─── Hyper-Ternary Resolution ────────────────────────────────────────

/// Run HTR after this many conflicts.
/// Coupled with decompose (CaDiCaL pattern: decompose → ternary → decompose).
/// Matches DECOMPOSE_INTERVAL so both fire in the same inprocessing pass.
pub(super) const HTR_INTERVAL: u64 = 10000;

/// Maximum number of resolvents per HTR call.
/// CaDiCaL uses `ternarymaxadd=1000` (10x clause count); we use a fixed cap
/// that's generous enough for structured instances without blowup on random.
pub(super) const MAX_HTR_RESOLVENTS: usize = 2000;

// ─── SAT Sweeping ────────────────────────────────────────────────────

/// Run SAT sweeping after this many conflicts.
/// Set to 0 so sweep fires in the first inprocessing round (#9215).
/// CaDiCaL runs sweep in the first inprobe round unconditionally with
/// tick-based effort limits. The previous value (35000) delayed sweep
/// past ~35K conflicts, missing the critical early-sweep opportunity
/// on formulas like shuffling-2 where Kissat solves 1824 vars in the
/// first sweep pass and then finds SAT within ~784 conflicts.
pub(super) const SWEEP_INTERVAL: u64 = 0;

/// Maximum sweep scheduling interval after growing backoff.
/// Unproductive sweep calls (no rewrites) double the interval.
/// Productive calls reset to base. CaDiCaL: sweep uses Delay struct.
pub(super) const SWEEP_MAX_INTERVAL: u64 = 200_000;

/// Minimum conflict-count backoff floor for unproductive sweep rounds (#8448).
///
/// When SWEEP_INTERVAL = 0, the growing backoff `0 * 2 = 0` never grows,
/// causing sweep to fire every inprocessing round even when producing 0
/// rewrites. This floor ensures the first unproductive round backs off to
/// at least this many conflicts before the next attempt.
///
/// On stable-300 (300 vars, 3K clauses), sweep runs 6 rounds with 0 rewrites
/// totaling 1729ms — over 10% of the 15s budget. With this floor, sweep
/// backs off to 50K -> 100K -> 200K conflicts, reducing unproductive rounds
/// from 6 to 1-2 and saving ~1.4s of search time.
pub(super) const SWEEP_UNPRODUCTIVE_BACKOFF_FLOOR: u64 = 50_000;

/// Skip expensive equivalence preprocessing passes above this variable count.
/// Raised from 100K to 200K: asconhash benchmarks (158K vars) need
/// congruence/decompose/sweep during preprocessing to solve at 20s. CaDiCaL
/// has no variable-count gate for preprocessing.
pub(super) const PREPROCESS_EXPENSIVE_MAX_VARS: usize = 200_000;

/// Skip expensive equivalence inprocessing passes above this clause count.
/// On large residuals (>3M clauses), the O(clauses) SETUP cost of entering
/// techniques (building occurrence lists, sorting watches, SCC traversal)
/// exceeds the tick-proportional effort budget. CaDiCaL handles this via
/// per-technique threshold gates (if budget < thresh × clauses, skip), but
/// AY's setup costs are not metered against tick budgets.
///
/// Lowered from 5M to 3M (#8084): shuffling-2 (4.7M clauses) was spending
/// 21.6s on preprocessing + 33.7s on inprocessing with 5M threshold despite
/// techniques finding almost nothing (decompose: 444 subs on 4.7M clauses).
/// At 3M: catches shuffling-2 (4.7M), 2dlx_ca (4.3M), 6g_6col (8.5M).
/// Kissat solves shuffling-2 in 2.9s with zero pre/inprocessing overhead.
pub(super) const PREPROCESS_EXPENSIVE_MAX_CLAUSES: usize = 3_000_000;

/// Clause threshold for congruence + decompose during preprocessing and
/// inprocessing. Aligned with PREPROCESS_EXPENSIVE_MAX_CLAUSES (3M).
///
/// Lowered from 5M to 3M (#8084): on shuffling-2 (4.7M clauses), congruence
/// finds 0 substitutions and decompose finds 444 equivalences (0.009%),
/// but together cost 3-8s per round. The density guard catches the worst
/// cases, but this threshold ensures we don't run these O(clauses) passes
/// on any formula above 3M clauses.
/// (#8448) Lowered from 5M to 3M. On shuffling-2 (4.7M clauses, 138K vars),
/// congruence takes ~2s but AY's CDCL search solves the formula in 1.6s
/// without ANY preprocessing. Congruence on >3M clause formulas costs more
/// time than it saves: the O(clauses) setup + gate extraction dominates,
/// and BVE still runs on the formulas where congruence is skipped. CaDiCaL's
/// congruence is ~1.3s on shuffling-2 but AY's is ~2s — not competitive
/// enough to justify the time spent.
pub(super) const CONGRUENCE_MAX_CLAUSES: usize = 3_000_000;

/// Raised congruence caps under --sat-no-subst-auto (#15, 2026-07-03). The
/// clause-driven XOR extraction made congruence cheap enough (15ms/70da) to
/// afford on the large ternary-dominant substitution instances the winner
/// (Kissat) cracks in seconds but AY was skipping (full-400: 07cea7 783k,
/// df813 521k, 9d7caee 1.7M vars). The AUTO density probe bails cheaply when
/// a big instance is NOT substitution-heavy, so the raised cap only pays off
/// where it wins. Upper bound keeps truly enormous formulas skipping.
pub(super) const AUTO_CONGRUENCE_MAX_VARS: usize = 2_000_000;
pub(super) const AUTO_CONGRUENCE_MAX_CLAUSES: usize = 8_000_000;

/// Giant-band AUTO congruence probe caps (giant-3M loss fix, 2026-07,
/// target 5ceb95f5; `AY_AB_SUBST_AUTO_GIANT`, default ON, NON-PROOF solves
/// only — see `VariantConfig::subst_auto_giant_band_active`).
///
/// The 2M/8M AUTO caps forfeited the AND-gate circuit giants sitting just
/// above them: 5ceb95f5 (3.11M vars / 8.55M clauses, parsed density 2.75)
/// and ac388757 (3.42M / 9.2M) are massive substitution instances — kissat's
/// congruence closure matches 1.31M AND gates and substitutes 43% of the
/// vars at t≈2-5s (SAT@82.8s), while AY skipped the probe entirely and
/// searched the raw 8.5M-clause formula to UNKNOWN@120s. With the caps
/// raised to 4M/10M the AUTO probe finds 1,312,822 equivalences (density
/// 0.4263), decompose substitutes to a 1.77M-var/4.5M-clause residual, and
/// search solves in 73K conflicts: measured SAT@62.0s (5ceb95f5, beats
/// kissat) and SAT@58.6s/51.8s (ac388757) at the 120s scoreboard protocol,
/// models independently validated against the original CNFs.
///
/// SCOPE — why a separate constant pair instead of raising 2M/8M:
///   1. NON-PROOF only: under DRAT the congruence proof ladder RUP-probes
///      per edge at ~10.4K edges/s — 1.31M edges is >115s of proof work, so
///      the raised band would burn the whole budget emitting a proof and
///      never flip (measured 312K/1.31M edges certified in a 30s A/B).
///      Proof solves keep the 2M/8M band bit-for-bit; AUTO already
///      fail-closes under LRAT. Future work: kissat-style direct
///      resolution-chain emission would make the band proof-affordable.
///   2. The decompose re-run bail stays keyed to 8M via the decoupled
///      `AUTO_DECOMPOSE_RERUN_MAX_CLAUSES` below — the bail is a drag bound
///      on O(total_literals) inprocessing re-runs (0ec8c5e9 regression fix)
///      and must not widen with the probe band.
///
/// Adversarial band sweep (all 5 sparse main2025 instances the raise
/// admits): the 3 non-substitution members (533017e0, 89002102, fe9b9a35,
/// probe density 0.0–0.0022 < 0.05) bail cheaply and stay UNKNOWN — the
/// probe tax is the designed ~2-5s drag bound; the 2 dense members (parsed
/// density 74.6/109.7) never arm (density-20 disarm). Zero regressions;
/// the regression floor is structurally out-of-band (all members are below
/// the 2M/8M caps, where behavior is bit-for-bit unchanged).
pub(super) const AUTO_CONGRUENCE_GIANT_MAX_VARS: usize = 4_000_000;
pub(super) const AUTO_CONGRUENCE_GIANT_MAX_CLAUSES: usize = 10_000_000;

/// Preprocess budget for AUTO-armed giants in the raised band (giant-3M
/// fix — see `AUTO_CONGRUENCE_GIANT_MAX_VARS`). The 2s `Large` class budget
/// is consumed by the full level-0 GC alone at 8.5M clauses (~2.1s
/// measured), making probe entry a load-dependent coin flip (one A/B arm
/// got through at 1.9s, one aborted at 2126ms). Measured need on 5ceb95f5:
/// GC ~2s + gate extraction ~0.5s + closure ~3s + decompose/fixpoint
/// (run-6 preprocess_ms=10,833) — 12s covers it with margin and is still
/// 10% of the 120s budget. Applies ONLY when the giant band is armed AND
/// the instance is inside the raised band (above 2M/8M, within 4M/10M) AND
/// not dense-disarmed — everything else keeps its class budget bit-for-bit.
pub(super) const AUTO_GIANT_PREPROCESS_BUDGET_SECS: u64 = 12;

/// Clause cap for `auto_capped_giant_skips_decompose_rerun` — decoupled
/// from `AUTO_CONGRUENCE_MAX_CLAUSES` by the giant-3M fix so the raised
/// probe band cannot widen the inprocessing re-run drag bound. Historical
/// value (8M) preserved bit-for-bit: the bail exists to stop
/// O(total_literals) decompose re-runs leaking onto >8M-clause arenas
/// (0ec8c5e9: 2,760ms / 4 runs on a 21M-clause arena, a lost 46s-margin
/// SAT), and that economics argument is about arena size, not probe
/// eligibility. Post-collapse residuals of the giant-band flips sit at
/// ~4.5M active clauses — below this bail, so their inprocessing re-runs
/// proceed exactly as in the flip measurements.
pub(super) const AUTO_DECOMPOSE_RERUN_MAX_CLAUSES: usize = 8_000_000;

/// Post-collapse BVE eligibility cap (--sat-no-bve-post-collapse, default ON
/// since 2026-07-10 wf_55735963; =0 kill-switch).
///
/// With --sat-no-subst-auto the congruence+decompose collapse substitutes away
/// hundreds of thousands of variables on the large substitution-heavy prize
/// instances (ebbda8d9 723K vars: ~200K equivs; 07cea7a6 783K: ~275K; df813fe7
/// 521K: ~170K), but every BVE eligibility gate keys on the ORIGINAL
/// `num_vars` (> PREPROCESS_EXPENSIVE_MAX_VARS = 200K), so BVE never sees the
/// collapsed residual. When the knob is ON, eligibility is RE-derived from the
/// live lifecycle counts (Active = num_vars - fixed - eliminated -
/// substituted) after the collapse and compared against this cap instead.
///
/// WHY 600K (raised from 450K, sparse-prize completion round 2026-07-11):
/// the measured post-collapse actives sit at ~350-520K. The FIRST
/// preprocess-time collapse round on ebbda8d9 re-derives to exactly 413,231
/// active (723,395 - 201,508 substituted - fixed) and df813fe7 to ~351K —
/// both admitted at 450K. The 450K cap was set when AY's measured BVE
/// throughput was ~20-30K elims/s, making a >450K residual un-dentable in
/// competition budget. With BVE_FAST_INNER default-ON the fast-inner profile
/// measured 237-291K elims/s on this class, so the 07cea7a6 residual
/// (783,192 orig vars, 275,256 collapse equivs, ~508K active — refused at
/// 450K, kissat unsat@11s) is ~2s of elimination work. 600K admits the
/// 07cea7a6 class with margin while still excluding residuals where even
/// fast-inner economics cannot dent (>600K active is >2.5s of pure
/// elimination before resolvent/GC overhead). The cap also bounds
/// reconstruction-stack growth from eliminated-clause witnesses; the fastelim
/// wall guards and BVE_SPARSE_DEEP_MAX_ELIMINATIONS bound the per-run work
/// independently of this eligibility cap. Env-tunable via
/// AY_BVE_POST_COLLAPSE_MAX_VARS for A/B ranging (=450000 restores the
/// pre-round default; used as the lever-1 kill for attribution).
pub(super) const BVE_POST_COLLAPSE_MAX_VARS: usize = 600_000;

/// Minimum factor-collapse ratio for the post-factor BVE clause-reopen
/// (`AY_AB_BVE_POST_FACTOR`, measured-infra, DEFAULT OFF —
/// `bve_post_factor_reopens`). The reopen only arms when factoring shrank the
/// active-clause count by at least this ratio (original / residual), so a
/// marginal collapse cannot open expensive BVE on a still-large residual.
///
/// WHY 8.0 (and why the whole lever is default-OFF): measured-negative on the
/// density-264 huge-binary cluster (f6a085f3 / 6ff70a3a) — see
/// `bve_post_factor_reopens` and `factor_max_effort`. With the factor drain
/// knobs the reopen FIRES correctly (f6 collapses 11.1M → ~371K active,
/// ratio ~30, density 3.3, kissat-parity 70,961 factors) and re-enables BVE
/// on the residual, but AY's BVE eliminates a structural ceiling of ~1,306
/// vars vs kissat's 104,496, so the formula never closes and the solve stays
/// `s UNKNOWN` at the 120s budget (and still UNKNOWN with a 200s BVE budget +
/// gate passes unlocked — the gap is structural, not budget). The reopen is
/// the correct, proven mechanism (direct clause-axis analogue of
/// `bve_post_collapse_reopens`) but is nowhere near sufficient here, so it
/// ships opt-in only. 8.0 is a conservative floor: every measured collapse of
/// interest is >20x, and the residual-under-cap guard already bounds cost.
pub(super) const BVE_POST_FACTOR_MIN_COLLAPSE_RATIO: f64 = 8.0;

// ─── Preprocessing Effort Budgets ────────────────────────────────────

/// Maximum propagations for probing during preprocessing (before search).
/// CaDiCaL uses preprocessinit=2M as base. Since we have no search ticks
/// during preprocessing, this is a fixed budget per preprocessing round.
/// Raised from 2M to 10M (#8466): Kissat's effort-based probing uses
/// a significantly higher propagation budget. 10M propagations allows
/// thorough failed-literal detection on medium formulas while still
/// preventing hangs on large instances.
/// On shuffling-2 (138K vars), unbounded probing caused >20s hangs (#6926).
pub(super) const PREPROCESS_PROBE_MAX_PROPAGATIONS: u64 = 10_000_000;

// ─── Between-Solve Incremental Reduction (#8435) ────────────────────

/// Minimum lifetime conflicts between between-solve reduction passes.
///
/// IC3/PDR engines make thousands of short incremental SAT queries. Each
/// query learns a few clauses but never reaches the 300-conflict threshold
/// for `reduce_db` to fire. This constant controls how often the solver
/// runs a lightweight between-solve reduction to prune accumulated learned
/// clauses. 500 conflicts is ~50-100 typical IC3 queries.
///
/// Reference: GipSAT (rIC3) uses activity-based clause cleanup on every
/// solve call. CaDiCaL's incremental mode has no explicit between-solve
/// cleanup (it relies on long-running solves where reduce_db fires
/// naturally). AY needs explicit between-solve cleanup because IC3 queries
/// are too short for in-solve reduction.
pub(super) const BETWEEN_SOLVE_REDUCE_CONFLICT_INTERVAL: u64 = 500;

/// Learned clause count multiplier for between-solve reduction trigger.
///
/// Between-solve reduction fires when:
///   learned_clauses > BETWEEN_SOLVE_LEARNED_FACTOR * num_original_clauses
///
/// A factor of 3 means the clause DB must grow to 3x the original formula
/// size before triggering cleanup. This is conservative — it avoids
/// cleaning up useful learned clauses from early solves while preventing
/// unbounded growth from thousands of IC3 queries.
pub(super) const BETWEEN_SOLVE_LEARNED_FACTOR: usize = 3;

/// Fraction of learned clauses to delete during between-solve reduction.
///
/// More aggressive than normal reduce_db (75%) because between-solve
/// reduction targets low-quality (high-LBD) clauses that accumulated
/// across many short solves. These clauses had minimal search context
/// when learned and are unlikely to be useful in future queries.
pub(super) const BETWEEN_SOLVE_REDUCE_FRACTION: usize = 50;

/// How often (in incremental solve count) to decay `used` flags on learned
/// clauses between solves. CaDiCaL decrements `used` on every reduce_db pass;
/// in IC3 workloads reduce_db rarely fires, so we decay periodically between
/// solves to prevent stale clauses from retaining permanent protection (#8435).
pub(super) const BETWEEN_SOLVE_USED_DECAY_INTERVAL: u64 = 100;

/// Hard cap on IC3 learned clauses as a multiplier of irredundant count (#8672).
///
/// When learned_count > IC3_MAX_LEARNED_FACTOR * irredundant_count, the
/// solver runs a targeted reduction to bring learned clauses below the cap.
/// This is tighter than IC3_GC_LEARNED_FACTOR (10x) which only triggers the
/// conservative between-solve GC. The hard cap prevents OOM on long-running
/// IC3/PDR workloads with 10K+ queries.
///
/// Factor 5: allows the learned DB to grow to 5x the original formula size
/// before triggering reduction. At 5x, the solver has accumulated enough
/// context from prior queries to be useful, but not so much that BCP
/// performance degrades significantly from watch list bloat.
pub(super) const IC3_MAX_LEARNED_FACTOR: usize = 5;

/// Minimum learned clause cap for IC3 mode (#8672).
///
/// Ensures the hard cap is never below 2000 clauses, even for very small
/// formulas where irredundant_count * IC3_MAX_LEARNED_FACTOR would produce
/// a cap that's too tight (e.g., 10 irredundant * 5 = 50 — too few to
/// retain useful learned clauses from IC3 queries).
pub(super) const IC3_MIN_LEARNED_CAP: usize = 2000;

/// How often (in incremental solve count) to check the IC3 learned cap (#8672).
///
/// The cap check iterates all active learned clauses, which is O(learned_count).
/// Checking every 50 solves amortizes the cost: on a typical IC3 workload
/// learning 5-50 clauses per query, the cap check runs every 250-2500 new
/// clauses, keeping overhead well under 1% of total solve time.
pub(super) const IC3_LEARNED_CAP_CHECK_INTERVAL: u64 = 50;

/// Learned clause count multiplier for IC3 conservative between-solve GC.
///
/// The conservative GC (ic3_between_solve_gc) fires when learned_count
/// exceeds IC3_GC_LEARNED_FACTOR * irredundant_count AND the solver has
/// completed IC3_GC_MIN_SOLVES queries. Only targets high-LBD (>6) unused
/// clauses and deletes IC3_GC_FRACTION% of them. This is looser than the
/// hard cap (IC3_MAX_LEARNED_FACTOR=5x) and fires less aggressively.
pub(super) const IC3_GC_LEARNED_FACTOR: usize = 10;
pub(super) const IC3_GC_FRACTION: usize = 25;
pub(super) const IC3_GC_MIN_LBD: u32 = 6;
pub(super) const IC3_GC_MIN_SOLVES: u64 = 500;

/// Arena memory pressure threshold for IC3 mode (#8673).
///
/// When the arena's total word count (len) exceeds this multiple of the
/// initial formula size (irredundant words at IC3 mode entry), a memory
/// pressure reduce fires. This catches unbounded growth that the count-based
/// cap misses — e.g., many medium-length learned clauses that individually
/// stay under the clause count cap but collectively consume significant memory.
///
/// At 8x, an initial formula using 100K words (400KB) triggers at 800K words
/// (3.2MB). At 2M words (8MB) initial, triggers at 16M words (64MB).
/// This is conservative enough to allow useful clause accumulation while
/// preventing OOM on deep IC3 runs (10K+ queries).
pub(super) const IC3_MEMORY_PRESSURE_ARENA_FACTOR: usize = 8;

/// Minimum arena word count before memory pressure checks kick in (#8673).
///
/// Below this threshold, the arena is small enough that memory pressure
/// reduction would be premature. 50K words = 200KB. Prevents the memory
/// pressure path from firing on tiny formulas where 8x growth is only
/// a few hundred KB.
pub(super) const IC3_MEMORY_PRESSURE_MIN_ARENA_WORDS: usize = 50_000;

/// How often (in incremental solve count) to check memory pressure (#8673).
///
/// The memory pressure check involves reading arena.len() and comparing
/// against the threshold. This is O(1) but we still amortize it across
/// queries. Every 25 solves checks quickly without measurable overhead.
pub(super) const IC3_MEMORY_PRESSURE_CHECK_INTERVAL: u64 = 25;

/// Fraction (percent) of eligible learned clauses to delete during a
/// memory pressure reduce (#8673). More aggressive than the normal cap
/// enforcement (which targets 75% of cap). Memory pressure deletes 50%
/// of eligible candidates to rapidly free arena space.
pub(super) const IC3_MEMORY_PRESSURE_DELETE_FRACTION: usize = 50;

/// How often (in incremental solve count) to rescale VSIDS activities.
/// After many incremental solves, VSIDS scores can inflate. Periodic
/// rescaling prevents numerical issues and preserves relative ordering (#8435).
pub(super) const INCREMENTAL_VSIDS_RESCALE_INTERVAL: u64 = 200;

/// Minimum number of incremental solves before first reduce_db scheduling
/// adjustment. Below this threshold, the solver uses default FIRST_REDUCE_DB
/// (300 conflicts). Above it, the solver lowers the reduce_db threshold to
/// fire sooner during short IC3 queries.
pub(super) const INCREMENTAL_REDUCE_DB_RAMP: u64 = 10;

/// Lowered first-reduce threshold for incremental mode after ramp-up.
///
/// After INCREMENTAL_REDUCE_DB_RAMP solves, the solver lowers next_reduce_db
/// from FIRST_REDUCE_DB (300) to this value so that reduce_db fires within
/// short IC3 queries. 50 conflicts is reachable in ~80% of typical IC3
/// queries (which range from 5-200 conflicts).
pub(super) const INCREMENTAL_FIRST_REDUCE_DB: u64 = 50;

// ─── Unified Inprocessing (inprobe) ──────────────────────────────────

/// Wall-clock limit for the entire inprocessing round (#8448).
///
/// Caps the total time spent in `run_restart_inprocessing` per round.
/// When the round has consumed more than this many milliseconds,
/// expensive techniques (BVE, sweep, backbone bounded-CDCL) are
/// skipped for the remainder of the round. Lightweight techniques
/// (decompose, congruence, deduplication) are not gated.
///
/// CaDiCaL achieves similar behavior via tick-proportional effort
/// limits on each technique. AY's technique-level budgets are
/// sometimes inaccurate (e.g., sweep's kitten sub-solver has its
/// own tick system that doesn't correspond to AY search ticks),
/// so this wall-clock cap provides a top-level safety net.
///
/// Value: 2000ms. On a 15s SAT-COMP timeout, this allows at most
/// ~13% of solve time per inprocessing round. With 4-5 rounds
/// typical, total inprocessing is bounded to ~40-50% of solve time.
/// The remaining 50-60% is guaranteed for search.
///
/// PROVEN NONDETERMINISM SOURCE (remeasure3 SAT-churn attribution,
/// 2026-07, main 8b40f19a): because this budget is WALL-CLOCK ms (checked
/// at inprocessing_schedule.rs and at the BVE entry in
/// inprocessing_elimination.rs), machine-load jitter shifts WHICH passes
/// fit inside a round, and on trajectory-sensitive SAT instances the
/// diverged simplification cascades into completely different searches.
/// Measured: three byte-identical default-config runs of f406e2b8
/// (1.2M clauses, parsed density 6.5) gave SAT@29.4s, SAT@32.4s (355,976
/// conflicts), and UNKNOWN@120s (2,146,536 conflicts). This retroactively
/// explains the board-to-board walks of f25a1df8 (115.9→81.9→30.4→UNK)
/// and f406e2b8 (109→TO→34.6→UNK): NOT attributable to binary changes.
/// Consequences: (a) treat single-run scoreboard flips on such instances
/// as noise — require 2-of-3 before claiming a churn regression; (b) the
/// hardening direction is to replace these ms deadlines with
/// tick/propagation-count budgets (CaDiCaL-style) so runs are
/// reproducible — a separate measured project, NOT a quiet constant swap
/// (any budget change reshapes the round schedule everywhere).
pub(super) const INPROCESSING_ROUND_WALL_LIMIT_MS: u64 = 2000;

/// Base interval for the unified inprocessing round timer.
/// CaDiCaL default: `inprobeint = 100` (options.hpp:141).
/// Actual interval grows logarithmically: `10 * INPROBE_INTERVAL * log10(phase + 9)`.
pub(super) const INPROBE_INTERVAL: u64 = 100;

/// Upper bound on the size-scaled incremental inprocessing re-fire interval
/// (#maxsat-inproc-throttle). Even on very large formulas we never let the
/// interval exceed this many conflicts, so simplification never fully stalls.
pub(super) const INCREMENTAL_INPROBE_INTERVAL_CAP: u64 = 20_000;

/// Extra cooldown for official LRAT inprocessing rounds that run proof-safe
/// passes but produce no simplification at all.
///
/// Main/LRAT hard-tail profiles can spend repeated windows in vivify/probe/
/// subsume/backbone/HTR with zero clause or root-literal yield while proof-
/// incomplete transforms remain correctly disabled. This multiplier preserves
/// productive rounds and non-proof search, but gives zero-yield proof rounds
/// more CDCL time before retrying the same safe pass set.
pub(super) const LRAT_ZERO_YIELD_INPROBE_COOLDOWN_SCALE: f64 = 4.0;

/// Default-off rescue interval used when LRAT proof mode has BVE/factor due by
/// scheduler gates but correctly clamped off. The rescue only advances the
/// LRAT-safe probe/inprobe cadence; it does not enable destructive transforms.
pub(super) const LRAT_PROOF_CLAMP_PROBE_RESCUE_INTERVAL: u64 = PROBE_INTERVAL / 2;

/// Default-off #9084 cooldown for backbone after a low-simplification round is
/// treated as productive only by the yield-rescue experiment. This leaves the
/// inprobe rescue cadence intact while bounding extra shared-backbone work.
pub(super) const YIELD_RESCUE_BACKBONE_COOLDOWN_INTERVAL: u64 = BACKBONE_INTERVAL * 4;

/// Default-off #9084 bounded-CDCL backbone backoff trigger. A zero-decompose-
/// yield round whose bounded backbone costs at least this many milliseconds per
/// yielded/root unit delays only the next bounded-CDCL backbone opportunity.
pub(super) const BOUNDED_BACKBONE_ZERO_DECOMPOSE_BACKOFF_MIN_MS_PER_UNIT: u64 = 600;

// ─── Variable Reorder ────────────────────────────────────────────────

/// Run clause-weighted variable reorder after this many conflicts.
/// Kissat default: `reorderint` (options.hpp). Lowered from 20K to 10K
/// (#8099): reorder is lightweight (O(vars + irredundant_clauses)) and
/// non-destructive (no clause modifications). More frequent reordering
/// improves variable selection responsiveness to evolving clause structure.
pub(super) const REORDER_INTERVAL: u64 = 10_000;

/// Maximum reorder scheduling interval after growing backoff.
pub(super) const REORDER_MAX_INTERVAL: u64 = 200_000;

// ─── Rephasing ───────────────────────────────────────────────────────

/// Rephase interval base (conflicts).
/// CaDiCaL: `rephaseint = 1000` (options.hpp:189).
/// CaDiCaL schedule: arithmetic, delta = rephaseint * (total + 1).
/// AY schedule: Kissat NLOG3N, delta = REPHASE_INITIAL * nlog3n(count).
/// NLOG3N grows sub-quadratically (n * log10(n+9)^3), keeping rephases
/// more frequent than linear on long runs. See `rephase.rs:86-92`.
pub(super) const REPHASE_INITIAL: u64 = 1000;

// ─── Lookahead Scheduling ───────────────────────────────────────────

/// Minimum total conflicts before lookahead is eligible to run.
/// The EMA statistics need warmup before the LBD ratio test is meaningful.
/// Reference: CaDiCaL gates lookahead behind `lookaheadmineff` (options.hpp).
pub(super) const LOOKAHEAD_MIN_CONFLICTS: u64 = 10_000;

/// Minimum conflicts between consecutive lookahead rounds (cooldown).
/// Lookahead is O(vars * BCP_depth) per round — too frequent is costly.
/// Grows with each round via reschedule_growing in lookahead_schedule.rs.
pub(super) const LOOKAHEAD_INTERVAL: u64 = 10_000;

/// LBD EMA ratio threshold for triggering lookahead.
/// Lookahead fires when `lbd_ema_fast > threshold * lbd_ema_slow`,
/// indicating the solver is learning poor-quality clauses (stuck).
/// 2.0 means the fast EMA must be 2x the slow EMA — a strong signal.
pub(super) const LOOKAHEAD_LBD_THRESHOLD: f64 = 2.0;

/// Maximum propagations per lookahead round (effort budget).
///
/// Without a budget, lookahead probes every unassigned variable at
/// O(vars * BCP_depth) per round. On FmlaEquivChain (35K+ active vars),
/// this costs 3+ seconds per round, dominating total solve time.
///
/// CaDiCaL gates lookahead behind effort limits (lookaheadmaxeff). AY
/// uses a propagation budget: once cumulative propagations during a round
/// exceed this limit, the round stops and returns the best variable found
/// so far. The budget is proportional to search propagations to scale
/// with formula size.
///
/// 2M propagations is ~200-400ms on typical hardware, keeping per-round
/// cost bounded while still scanning enough variables for a meaningful
/// splitting decision.
pub(super) const LOOKAHEAD_MAX_PROPAGATIONS: u64 = 2_000_000;

/// Maximum wall-clock time (milliseconds) per lookahead round.
///
/// Complements the propagation budget with a hard wall-clock limit.
/// On formulas where per-propagation cost varies widely (e.g., long
/// watched clauses), the propagation budget alone may not bound time
/// tightly enough. 500ms keeps each round fast while providing fallback
/// safety.
pub(super) const LOOKAHEAD_WALL_LIMIT_MS: u64 = 500;

// ─── Walk/Local Search ───────────────────────────────────────────────

/// Default walk tick limit per round (effort budget).
/// Used only for startup walk before any search ticks have accumulated.
/// Matches WALK_MIN_EFFORT (Kissat's global mineffort floor of 10M ticks)
/// so that startup walk has the same budget as the minimum rephase walk.
/// Reference: Kissat `options.h:80` — `mineffort = 10` (10M ticks).
pub(super) const WALK_DEFAULT_LIMIT: u64 = 10_000_000;

// ─── Formula Classification (#8150) ─────────────────────────────────

/// Coarse formula size classification for adjusting inprocessing effort.
///
/// Replaces ad-hoc size comparisons scattered across scheduling code with
/// a structured classification. Techniques can dispatch on the class to
/// scale effort budgets without adding per-technique threshold constants.
///
/// Thresholds match the existing ad-hoc gates:
/// - Small: < 10K variables AND < 100K clauses
/// - Medium: < 200K variables AND < 3M clauses (PREPROCESS_EXPENSIVE_MAX_*)
/// - Large: everything above
///
/// Reference: Kissat classify.c uses binary clause fraction (bigbigfraction=990)
/// for a different kind of classification. This classification is purely
/// size-based and orthogonal to Kissat's binary-fraction metric.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FormulaClass {
    /// < 10K variables, < 100K clauses. Inprocessing is cheap; use generous
    /// effort budgets. Backbone probes all variables.
    Small,
    /// < 200K variables, < 3M clauses. Standard inprocessing budgets apply.
    Medium,
    /// >= 200K variables or >= 3M clauses. Expensive passes are gated or
    /// > skipped. Backbone uses reduced conflict budget.
    Large,
}

impl FormulaClass {
    /// Classify based on active variable and clause counts.
    pub(super) fn classify(num_vars: usize, active_clauses: usize) -> Self {
        if num_vars >= PREPROCESS_EXPENSIVE_MAX_VARS
            || active_clauses >= PREPROCESS_EXPENSIVE_MAX_CLAUSES
        {
            Self::Large
        } else if num_vars < 10_000 && active_clauses < 100_000 {
            Self::Small
        } else {
            Self::Medium
        }
    }

    /// Backbone conflict budget scaled by formula class.
    ///
    /// Small formulas: probe up to all variables (generous budget).
    /// Medium formulas: cap of 2000 (#8361). CaDiCaL's backbone uses
    ///   lightweight binary-clause propagation (~10x cheaper per probe
    ///   than AY's bounded CDCL approach), so tighter budgets match.
    /// Large formulas: reduced cap of 1000 to limit overhead.
    pub(super) fn backbone_conflict_budget(self, num_vars: usize) -> u64 {
        let cap = match self {
            Self::Small => 10_000,
            Self::Medium => 2_000,
            Self::Large => 1_000,
        };
        (num_vars as u64).min(cap)
    }
}

// ── Bucket-queue VSIDS for IC3 domain-restricted queries (#8476) ─────

/// Maximum domain size for bucket-queue activation.
///
/// When `set_domain` is called with at most this many variables, the
/// O(1) amortized bucket queue is used instead of the O(log n) heap.
/// The threshold avoids bucket overhead on larger domain sizes where
/// the heap's locality advantages dominate.
///
/// 64 variables covers typical IC3 queries (5-50 vars) with headroom.
pub(super) const BUCKET_QUEUE_MAX_DOMAIN_SIZE: usize = 64;

/// Restarts within one domain epoch before the bucket queue hands
/// variable selection back to the exact EVSIDS heap.
///
/// The bucket queue buys O(1) selection by rounding activity order to
/// factor-of-two classes — the right trade for the short queries domain
/// mode targets (typical IC3-profile queries finish in 0-5 conflicts,
/// usually without restarting at all; see `set_ic3_mode`). Restarts are
/// hardness evidence the solver already produces for free: by the eighth
/// restart the Luby scheduler has finished its entire opening cascade
/// (1,1,2,1,1,2,4) and is escalating into long runs, which puts the query
/// in the hard tail (~1% of IC3 queries, 100+ conflicts) where the heap's
/// exact activity ordering out-decides the bucket's coarse classes.
/// Switching at 8 keeps the bucket's win on the short-query bulk while
/// capping how long a hard query runs on approximate ordering.
///
/// Consumed by `Solver::bucket_queue_on_restart` (`restart.rs`).
pub(super) const BUCKET_QUEUE_RESTART_THRESHOLD: u32 = 8;

/// Default IC3 formula-size breakpoint for domain-restricted BCP (#8802).
///
/// Domain BCP pays bitmap and watcher-filter overhead. On small IC3/PDR
/// queries, full BCP is usually cheaper even though it scans more clauses.
/// `set_ic3_mode()` uses this default unless callers override it with
/// `Solver::set_domain_bcp_min_vars`.
pub(super) const IC3_DOMAIN_BCP_MIN_VARS_DEFAULT: usize = 50;
