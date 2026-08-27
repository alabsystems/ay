// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parallel portfolio solver
//!
//! Runs multiple solver configurations in parallel and returns the first result.
//! This is the standard approach for robust SAT solving - different heuristics
//! work better on different problem classes.
//!
//! ## Strategies
//!
//! The portfolio includes diverse strategies:
//! - VSIDS with Luby restarts (classic MiniSat-style)
//! - VSIDS with Glucose restarts (LBD-based)
//! - Aggressive inprocessing (safe baseline techniques with diversified search)
//! - Conservative (minimal preprocessing, stable search)
//! - Probe-focused (emphasis on failed literal probing)
//! - BVE-focused (emphasis on variable elimination)
//!
//! ## Instance-Aware Selection
//!
//! When a formula is available, `PortfolioSolver::new_adaptive` extracts
//! static syntactic features (SATzilla-style) and selects strategies based
//! on the instance's structural class. See [`crate::features`].
//!
//! ## Usage
//!
//! ```text
//! use ay_sat::portfolio::{PortfolioSolver, Strategy};
//!
//! let solver = PortfolioSolver::new();
//! let formula: DimacsFormula = ...;
//! let result = solver.solve(&formula);
//! ```

use crate::dimacs::DimacsFormula;
use crate::features::{InstanceClass, SatFeatures};
use crate::literal::Literal;
use crate::proof::ProofOutput;
use crate::solver::{SatResult, Solver};
use parking_lot::Mutex;
use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::thread;

mod strategy_configs;

use strategy_configs::{bve_focused_config, conservative_config, probe_focused_config};

const PORTFOLIO_SHARE_MAX_LBD: u32 = 3;
const PORTFOLIO_SHARE_MAX_CLAUSE_LEN: usize = 32;
const PORTFOLIO_SHARE_MAX_STORED: usize = 4096;
const PORTFOLIO_SHARE_IMPORT_BATCH: usize = 32;

/// Cross-worker learned-clause sharing is DISABLED for soundness (task #14).
///
/// The share bus exchanges learned clauses using each worker's **internal**
/// variable indices, but portfolio workers independently remap their variable
/// spaces during a solve, so the same internal index does not denote the same
/// variable across workers:
///
///   * Fresh extension variables introduced by SBVA and factoring
///     (`Solver::new_var_internal`) grow `num_vars` past the original count,
///     and each worker's fresh variables are its own — worker A's index `k`
///     and worker B's index `k` are different variables.
///   * Level-0 variable **compaction** (`Solver::compact`, gated to run only
///     in non-proof mode — exactly when sharing is active) renumbers *active*
///     variables to a contiguous range, so even original variables acquire
///     worker-local internal indices.
///
/// Importing a sibling's learned clause under such a divergent mapping can add
/// a clause the original formula does **not** entail; at decision level 0 that
/// can derive a spurious empty clause → a FALSE `UNSAT` on a satisfiable
/// instance (observed under `--no-proof --parallel` on bit-blasted, XOR-rich
/// CNF). Until sharing is re-expressed over the stable *external* namespace,
/// restricted to original user variables, it stays off so every worker refutes
/// the ORIGINAL formula independently and any `UNSAT` it reports is a complete,
/// sound refutation. (Proof mode already disabled sharing.)
const PORTFOLIO_CLAUSE_SHARING_ENABLED: bool = false;

#[derive(Debug, Clone)]
struct SharedPortfolioClause {
    seq: u64,
    origin_worker: usize,
    literals: Vec<Literal>,
}

#[derive(Debug, Default)]
struct ClauseShareState {
    next_seq: u64,
    clauses: VecDeque<SharedPortfolioClause>,
}

#[derive(Debug)]
struct ClauseShareBus {
    inner: Mutex<ClauseShareState>,
    max_lbd: u32,
    max_clause_len: usize,
    max_stored: usize,
    import_batch: usize,
}

impl Default for ClauseShareBus {
    fn default() -> Self {
        Self {
            inner: Mutex::new(ClauseShareState::default()),
            max_lbd: PORTFOLIO_SHARE_MAX_LBD,
            max_clause_len: PORTFOLIO_SHARE_MAX_CLAUSE_LEN,
            max_stored: PORTFOLIO_SHARE_MAX_STORED,
            import_batch: PORTFOLIO_SHARE_IMPORT_BATCH,
        }
    }
}

impl ClauseShareBus {
    fn export(&self, origin_worker: usize, literals: &[Literal], lbd: u32) -> bool {
        if lbd == 0 || lbd > self.max_lbd {
            return false;
        }
        let Some(literals) = normalize_shared_clause(literals, self.max_clause_len) else {
            return false;
        };

        let mut guard = self.inner.lock();
        let seq = guard.next_seq;
        guard.next_seq = guard.next_seq.saturating_add(1);
        guard.clauses.push_back(SharedPortfolioClause {
            seq,
            origin_worker,
            literals,
        });
        while guard.clauses.len() > self.max_stored {
            guard.clauses.pop_front();
        }
        true
    }

    fn import_batch(&self, worker_id: usize, last_seen_seq: &mut u64) -> Vec<Vec<Literal>> {
        let guard = self.inner.lock();
        let mut imported = Vec::new();
        let mut seen = *last_seen_seq;

        for clause in guard.clauses.iter() {
            if clause.seq < seen {
                continue;
            }
            seen = clause.seq.saturating_add(1);
            if clause.origin_worker == worker_id {
                continue;
            }
            imported.push(clause.literals.clone());
            if imported.len() >= self.import_batch {
                break;
            }
        }

        *last_seen_seq = seen;
        imported
    }
}

fn normalize_shared_clause(literals: &[Literal], max_clause_len: usize) -> Option<Vec<Literal>> {
    if literals.is_empty() || literals.len() > max_clause_len {
        return None;
    }

    let mut normalized = literals.to_vec();
    normalized.sort_by_key(|lit| lit.raw());
    normalized.dedup();

    if normalized.len() > max_clause_len {
        return None;
    }

    for pair in normalized.windows(2) {
        if pair[0].variable() == pair[1].variable() {
            return None;
        }
    }

    Some(normalized)
}

/// Configuration for a solver instance.
///
/// Internal -- technique toggles are backed by `InprocessingFeatureProfile`
/// for full alignment with single-solver profiles (#8149). Non-profile
/// settings (restarts, chrono, initial_phase, MAB) remain as separate fields.
///
/// Extended fields (restart_base, stable_phase_init, random_var_freq,
/// stable_only, chrono_reuse_trail) enable portfolio diversification for
/// threads beyond the base 6 strategies (#8584).
#[derive(Debug, Clone)]
pub(crate) struct SolverConfig {
    /// Feature profile controlling all inprocessing technique toggles.
    pub(crate) features: crate::InprocessingFeatureProfile,
    pub(crate) glucose_restarts: bool,
    pub(crate) chrono_enabled: bool,
    pub(crate) initial_phase: Option<bool>,
    /// Enable UCB1 multi-armed bandit branch-heuristic selection (EVSIDS/VMTF/CHB).
    pub(crate) branch_selector_ucb1: bool,
    pub(crate) seed: u64,
    /// Override Luby restart base interval (None = solver default).
    pub(crate) restart_base: Option<u64>,
    /// Override initial stabilization phase length in conflicts.
    pub(crate) stable_phase_init: Option<u64>,
    /// Random variable selection frequency (Z3-style, 0.0-1.0).
    pub(crate) random_var_freq: Option<f64>,
    /// Force stable-only search mode (EVSIDS + reluctant doubling).
    pub(crate) stable_only: bool,
    /// Enable trail reuse in chronological backtracking.
    pub(crate) chrono_reuse_trail: bool,
    /// Equal-effort stable-mode budgeting (the `equiticks` config). Feeds the
    /// starved target-phase machinery more stable airtime; a per-instance-good
    /// config that flips a class of model-finding SAT losses (b3d3680b,
    /// 59fc779f, cbd09330, 6cd9571b, 0a8a4c28, ab02c7ef) + 3ef7fa06 UNSAT but
    /// is net-negative as a global default — its correct home is a portfolio
    /// arm, where the independent-thread first-success guarantee means it can
    /// only add solves, never regress the default arm.
    pub(crate) mode_equiticks: bool,
    /// Enable the equiticks stable-phase progress gate (defers a still-converging
    /// stable phase past the halved equal-effort budget, up to the default
    /// schedule hardcap). Only meaningful with `mode_equiticks`. Strengthens the
    /// Equiticks arm: captures 3ef7fa06 (UNSAT, cert-verified) + 4c3001f8 (SAT).
    pub(crate) mode_eqt_progress: bool,
}

/// Default feature profile for portfolio strategies.
/// BCE, conditioning, symmetry, CCE default OFF to match CaDiCaL (#8190).
/// BVE, decompose, and congruence are opt-in until reconstruction is sound
/// across the default SAT path. Specialized strategies re-enable selectively
/// for diversity.
fn portfolio_default_features() -> crate::InprocessingFeatureProfile {
    crate::InprocessingFeatureProfile {
        preprocess: true,
        walk: true,
        warmup: true,
        shrink: true,
        hbr: true,
        vivify: true,
        subsume: true,
        probe: true,
        bve: false,
        bce: false,
        condition: false,
        factor: true,
        sbva: true,
        htr: true,
        gate: true,
        sweep: true,
        transred: true,
        congruence: false,
        decompose: false,
        backbone: true,
        symmetry: false,
        reorder: true,
        cce: false,
    }
}

impl Default for SolverConfig {
    fn default() -> Self {
        Self {
            features: portfolio_default_features(),
            glucose_restarts: true,
            chrono_enabled: true,
            initial_phase: None,
            branch_selector_ucb1: false,
            seed: 0,
            restart_base: None,
            stable_phase_init: None,
            random_var_freq: None,
            stable_only: false,
            chrono_reuse_trail: true,
            mode_equiticks: false,
            mode_eqt_progress: false,
        }
    }
}

/// Predefined solver strategies for portfolio solving
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Strategy {
    /// Classic VSIDS with Luby restarts (MiniSat-style)
    VsidsLuby,
    /// VSIDS with Glucose-style EMA restarts
    VsidsGlucose,
    /// Aggressive inprocessing with safe baseline techniques and diversified search
    AggressiveInprocessing,
    /// Conservative search (minimal preprocessing)
    Conservative,
    /// Focus on failed literal probing
    ProbeFocused,
    /// Focus on variable elimination
    BveFocused,
    /// Equal-effort stable-mode budgeting (equiticks): feeds the target-phase
    /// machinery more stable airtime, flipping a class of model-finding SAT
    /// losses. Net-negative as a global default, but strictly additive here.
    Equiticks,
}

impl Strategy {
    /// Convert strategy to solver configuration.
    ///
    /// All technique toggles go through the `InprocessingFeatureProfile`
    /// so portfolio and single-solver profiles stay aligned (#8149).
    pub(crate) fn to_config(self) -> SolverConfig {
        let all = portfolio_default_features();
        match self {
            // Default safe inprocessing profile (Luby restarts variant).
            Self::VsidsLuby => SolverConfig {
                features: all,
                glucose_restarts: false,
                seed: 0,
                ..Default::default()
            },
            Self::VsidsGlucose => SolverConfig {
                features: all,
                seed: 1,
                ..Default::default()
            },
            Self::AggressiveInprocessing => SolverConfig {
                features: all,
                // Enable UCB1 MAB branch selection (EVSIDS/VMTF/CHB) for
                // portfolio diversity. The MAB adaptively explores CHB which
                // may benefit structured/BMC instances. This is the only
                // portfolio strategy that runs CHB (#8091).
                branch_selector_ucb1: true,
                seed: 2,
                ..Default::default()
            },
            // Minimal: all inprocessing disabled
            Self::Conservative => conservative_config(),
            // Probing emphasis: subsumption + probing + HBR only
            Self::ProbeFocused => probe_focused_config(),
            // BVE emphasis: elimination + gate + conditioning
            Self::BveFocused => bve_focused_config(),
            // Equiticks: full default inprocessing + equal-effort stable-mode
            // budgeting (more stable airtime feeds the target-phase machinery).
            // Captures the model-finding SAT losses the default variant misses;
            // strictly additive as an independent portfolio arm.
            Self::Equiticks => SolverConfig {
                features: portfolio_default_features(),
                mode_equiticks: true,
                mode_eqt_progress: true,
                seed: 6,
                ..Default::default()
            },
        }
    }

    /// Get all predefined strategies
    pub(crate) fn all() -> Vec<Self> {
        vec![
            Self::VsidsLuby,
            Self::VsidsGlucose,
            Self::AggressiveInprocessing,
            Self::Conservative,
            Self::ProbeFocused,
            Self::BveFocused,
            Self::Equiticks,
        ]
    }

    /// Get the recommended subset of strategies for a given thread count.
    ///
    /// This is the legacy selection path that ignores instance structure.
    /// Prefer `recommended_for_instance` when the formula is available.
    ///
    /// Returns at most 6 base strategies. Threads beyond 6 get diverse
    /// extended configs generated by `strategies_to_configs()` (#8584).
    pub(crate) fn recommended(num_threads: usize) -> Vec<Self> {
        match num_threads {
            1 => vec![Self::VsidsGlucose],
            2 => vec![Self::VsidsGlucose, Self::VsidsLuby],
            3 => vec![
                Self::VsidsGlucose,
                Self::VsidsLuby,
                Self::AggressiveInprocessing,
            ],
            4 => vec![
                Self::VsidsGlucose,
                Self::VsidsLuby,
                Self::AggressiveInprocessing,
                Self::Conservative,
            ],
            // 5+ threads: return all 6 base strategies.
            // Extension to num_threads is handled by strategies_to_configs().
            _ => Self::all(),
        }
    }

    /// Select strategies based on instance features and thread count.
    ///
    /// Uses static syntactic features (SATzilla-style) to classify the
    /// instance and prioritize the strategies most likely to perform well.
    ///
    /// This is Phase 1a of the learned algorithm selection design
    /// (the development design notes): simple routing
    /// based on cheap static features, no ML inference.
    ///
    /// Strategy prioritization per instance class:
    /// - **Random3Sat**: BVE-focused first (elimination is critical at
    ///   high density), then aggressive inprocessing, then Glucose.
    /// - **Structured**: Aggressive inprocessing (gate extraction,
    ///   congruence, sweeping), then BVE-focused, then probe-focused.
    /// - **Industrial**: VsidsGlucose (robust default), then conservative
    ///   (avoids expensive inprocessing on huge formulas), then BVE.
    /// - **Small**: VsidsGlucose (fast on small instances), then Luby.
    pub(crate) fn recommended_for_instance(
        num_threads: usize,
        features: &SatFeatures,
    ) -> Vec<Self> {
        let class = InstanceClass::classify(features);
        let prioritized = match class {
            InstanceClass::Random3Sat | InstanceClass::RandomKSat => vec![
                Self::BveFocused,
                Self::AggressiveInprocessing,
                Self::VsidsGlucose,
                Self::VsidsLuby,
                Self::ProbeFocused,
                Self::Conservative,
            ],
            InstanceClass::Structured => vec![
                Self::AggressiveInprocessing,
                Self::BveFocused,
                Self::ProbeFocused,
                Self::VsidsGlucose,
                Self::VsidsLuby,
                Self::Conservative,
            ],
            InstanceClass::Industrial => vec![
                Self::VsidsGlucose,
                Self::Conservative,
                Self::BveFocused,
                Self::VsidsLuby,
                Self::AggressiveInprocessing,
                Self::ProbeFocused,
            ],
            InstanceClass::Small => vec![
                Self::VsidsGlucose,
                Self::VsidsLuby,
                Self::AggressiveInprocessing,
                Self::Conservative,
                Self::ProbeFocused,
                Self::BveFocused,
            ],
            // Unknown: use the same balanced strategy as Structured (safest default).
            InstanceClass::Unknown => vec![
                Self::AggressiveInprocessing,
                Self::BveFocused,
                Self::ProbeFocused,
                Self::VsidsGlucose,
                Self::VsidsLuby,
                Self::Conservative,
            ],
        };

        let mut result = prioritized;
        // Equiticks arm appended last (7th): captures the model-finding SAT
        // losses the other strategies miss. Additive by construction — only
        // engaged when num_threads >= 7, so it never displaces a base strategy,
        // and the portfolio's first-success means it can only add solves.
        result.push(Self::Equiticks);
        // Truncate to min(num_threads, len) base strategies.
        // Threads beyond the base list get diverse extended configs via
        // strategies_to_configs() (#8584).
        result.truncate(num_threads.min(result.len()).max(1));
        result
    }
}

/// Result from a portfolio solver thread
#[derive(Debug)]
struct ThreadResult {
    /// The solve result
    result: SatResult,
    /// Raw forward LRAT proof bytes from the winning thread (#8428).
    /// Present only when proof_mode is true and the result is UNSAT.
    /// The forward LRAT proof is complete (unlike backward reconstruction
    /// which may miss clauses derived during BCP at level 0).
    raw_proof_bytes: Option<Vec<u8>>,
}

/// Parallel portfolio SAT solver
///
/// Runs multiple solver configurations in parallel and returns the first result.
pub struct PortfolioSolver {
    /// Number of threads to use
    num_threads: usize,
    /// Solver configurations (one per thread)
    configs: Vec<SolverConfig>,
    /// Cached instance features, extracted once in `new_adaptive()` and reused
    /// in `solve()` to avoid redundant O(total_literals) extraction (#8149).
    cached_features: Option<(SatFeatures, InstanceClass)>,
    /// When true, each solver thread enables LRAT so backward proof
    /// reconstruction produces a usable `ProofCertificate` on UNSAT (#8428).
    proof_mode: bool,
    /// Optional external cancellation flag (e.g. the CLI wall-clock watchdog).
    /// When set, every worker's stop condition also observes it, so the
    /// portfolio honours a global timeout even when no worker has finished.
    /// Without this the portfolio could only stop when a worker won or gave
    /// up, so a slow-but-productive worker had no deadline (#parallel-bv).
    external_cancel: Option<Arc<AtomicBool>>,
}

impl PortfolioSolver {
    /// Create a new portfolio solver with the specified number of threads.
    ///
    /// Uses recommended strategies for the thread count (legacy, no instance features).
    pub fn new(num_threads: usize) -> Self {
        let num_threads = num_threads.max(1);
        let strategies = Strategy::recommended(num_threads);
        let configs = strategies_to_configs(strategies, num_threads);

        Self {
            num_threads,
            configs,
            cached_features: None,
            proof_mode: false,
            external_cancel: None,
        }
    }

    /// Create a portfolio solver with instance-aware strategy selection.
    ///
    /// Extracts static features from the formula in O(total_literals) time
    /// and selects strategies best suited for the instance's structural class.
    /// Features are cached and reused in `solve()` to avoid double extraction
    /// (#8149).
    ///
    /// This is the main entry point for the learned algorithm selection
    /// pipeline (Phase 1a: static features + simple routing).
    pub fn new_adaptive(num_threads: usize, formula: &DimacsFormula) -> Self {
        let num_threads = num_threads.max(1);
        let features = SatFeatures::extract(formula.num_vars, &formula.clauses);
        let class = InstanceClass::classify(&features);
        let strategies = Strategy::recommended_for_instance(num_threads, &features);
        let configs = strategies_to_configs(strategies, num_threads);

        Self {
            num_threads,
            configs,
            cached_features: Some((features, class)),
            proof_mode: false,
            external_cancel: None,
        }
    }

    /// Enable proof mode: each solver thread will track LRAT clause IDs
    /// so backward proof reconstruction produces a materializable
    /// `ProofCertificate` on UNSAT results (#8428).
    ///
    /// Must be called before [`solve()`](Self::solve). Without this,
    /// UNSAT results carry an empty certificate.
    pub fn set_proof_mode(&mut self, enabled: bool) {
        self.proof_mode = enabled;
    }

    /// Install an external cancellation flag (e.g. the CLI wall-clock
    /// watchdog's interrupt handle). Every worker's stop condition observes it,
    /// so the portfolio honours a global timeout / interrupt even when no
    /// worker has produced a definitive result. Must be called before
    /// [`solve()`](Self::solve).
    pub fn set_external_cancel(&mut self, flag: Arc<AtomicBool>) {
        self.external_cancel = Some(flag);
    }

    /// Solve a CNF formula in parallel
    ///
    /// Returns the first result found by any thread.
    pub fn solve(&self, formula: &DimacsFormula) -> SatResult {
        let (result, _) = self.solve_inner(formula);
        result
    }

    /// Solve a CNF formula in parallel, returning both the result and
    /// optional raw forward LRAT proof bytes (#8428).
    ///
    /// When `proof_mode` is enabled and the result is UNSAT, the second
    /// element contains the complete forward LRAT proof from the winning
    /// solver thread. This is more complete than the backward-reconstructed
    /// `ProofCertificate` inside `SatResult::Unsat`, which may miss clauses
    /// derived during BCP at decision level 0.
    ///
    /// Callers that need a proof file should use these raw bytes (or convert
    /// them to DRAT by stripping clause IDs/hints) instead of materializing
    /// from the `ProofCertificate`.
    pub fn solve_with_proof_bytes(&self, formula: &DimacsFormula) -> (SatResult, Option<Vec<u8>>) {
        self.solve_inner(formula)
    }

    /// Inner implementation shared by `solve` and `solve_with_proof_bytes`.
    fn solve_inner(&self, formula: &DimacsFormula) -> (SatResult, Option<Vec<u8>>) {
        // Reuse cached features from new_adaptive() or extract fresh (#8149).
        let (features, class) = match &self.cached_features {
            Some((f, c)) => (f.clone(), *c),
            None => {
                let f = SatFeatures::extract(formula.num_vars, &formula.clauses);
                let c = InstanceClass::classify(&f);
                (f, c)
            }
        };

        if self.num_threads == 1 || self.configs.len() == 1 {
            // Single-threaded: just run normally
            let config = self.configs.first().cloned().unwrap_or_default();
            let mut solver = create_solver_from_config(
                formula.num_vars,
                formula.clauses.len(),
                &config,
                self.proof_mode,
            );
            apply_adaptive_adjustments(&mut solver, &features, &class);
            // Honour a global timeout/interrupt in the single-thread fast path.
            if let Some(ext) = &self.external_cancel {
                solver.set_interrupt(Arc::clone(ext));
            }
            for clause in &formula.clauses {
                solver.add_clause(clause.clone());
            }
            let solve_result = solver.solve().into_inner();
            let proof_bytes = extract_proof_bytes(&mut solver, &solve_result, self.proof_mode);
            return (solve_result, proof_bytes);
        }

        // Multi-threaded portfolio
        let terminate = Arc::new(AtomicBool::new(false));
        let result: Arc<Mutex<Option<ThreadResult>>> = Arc::new(Mutex::new(None));
        let proof_mode = self.proof_mode;
        // Cross-worker clause sharing is off for soundness — see
        // `PORTFOLIO_CLAUSE_SHARING_ENABLED`. Proof mode also keeps runs
        // isolated (no cross-thread proof stitching yet).
        let share_bus = if proof_mode || !PORTFOLIO_CLAUSE_SHARING_ENABLED {
            None
        } else {
            Some(Arc::new(ClauseShareBus::default()))
        };
        // A worker that imported cross-worker shared clauses may have refuted a
        // *contaminated* formula, so its UNSAT is not a trustworthy refutation
        // of the ORIGINAL formula. Track whether sharing was active so the join
        // can fail-closed on such an UNSAT (task #14).
        let clause_sharing_active = share_bus.is_some();
        // External (wall-clock/interrupt) cancellation, observed by every worker
        // in addition to the portfolio-internal `terminate` so a global timeout
        // stops the whole portfolio even when no worker has finished.
        let external_cancel = self.external_cancel.clone();

        thread::scope(|scope| {
            let handles: Vec<_> = self
                .configs
                .clone()
                .into_iter()
                .enumerate()
                .map(|(worker_id, config)| {
                    let formula_clauses = &formula.clauses;
                    let num_vars = formula.num_vars;
                    let num_clauses = formula.clauses.len();
                    let features_ref = &features;
                    let terminate = Arc::clone(&terminate);
                    let result: Arc<Mutex<Option<ThreadResult>>> = Arc::clone(&result);
                    let share_bus = share_bus.clone();
                    let external_cancel = external_cancel.clone();

                    scope.spawn(move || {
                        // Create solver with this configuration
                        let mut solver = create_portfolio_worker_solver(
                            num_vars,
                            num_clauses,
                            &config,
                            proof_mode,
                            Arc::clone(&terminate),
                        );
                        apply_adaptive_adjustments(&mut solver, features_ref, &class);
                        if let Some(bus) = share_bus {
                            let export_bus = Arc::clone(&bus);
                            let import_bus = Arc::clone(&bus);
                            let mut last_seen_seq = 0_u64;
                            solver.set_portfolio_clause_sharing(
                                Some(Box::new(move |literals, lbd| {
                                    let _ = export_bus.export(worker_id, literals, lbd);
                                })),
                                Some(Box::new(move || {
                                    import_bus.import_batch(worker_id, &mut last_seen_seq)
                                })),
                            );
                        }

                        // Add clauses
                        for clause in formula_clauses {
                            solver.add_clause(clause.clone());
                        }

                        // Stop when the portfolio winner has signalled, or when an
                        // external (wall-clock/interrupt) cancellation fires. The
                        // per-worker `terminate` clone stays live for the join
                        // below; `external_cancel` is moved into the closure.
                        let should_stop = {
                            let terminate = Arc::clone(&terminate);
                            move || {
                                terminate.load(Ordering::Relaxed)
                                    || external_cancel
                                        .as_ref()
                                        .is_some_and(|c| c.load(Ordering::Relaxed))
                            }
                        };
                        let solve_result = solver.solve_interruptible(should_stop).into_inner();

                        // Store the result unless a winner has already terminated us.
                        if !terminate.load(Ordering::Relaxed) {
                            // SOUNDNESS gate (task #14): never let an UNSAT verdict
                            // win the portfolio unless it is a complete, sound
                            // refutation of the ORIGINAL formula. A worker that ran
                            // with cross-worker clause sharing may have refuted a
                            // *contaminated* clause database (see
                            // `PORTFOLIO_CLAUSE_SHARING_ENABLED`), so without a
                            // machine-checkable proof its UNSAT is not trustworthy.
                            // Proof mode (independent, proof-carrying workers) and the
                            // sharing-disabled default both yield trustworthy
                            // refutations. A SAT result is always trustworthy: its
                            // model is verified against the original formula by
                            // the solver's always-on model gate before this point. An untrusted
                            // UNSAT is dropped (not emitted, does not stop siblings)
                            // so the portfolio fails closed to another worker's sound
                            // result or to `Unknown` — never to a wrong `UNSAT`.
                            let trustworthy = portfolio_result_is_trustworthy(
                                &solve_result,
                                proof_mode,
                                clause_sharing_active,
                            );
                            if trustworthy {
                                // COMPLETENESS (#parallel-bv): only a *definitive*
                                // result (SAT/UNSAT) may win the portfolio and stop
                                // the other workers. A worker that gave up (`Unknown`
                                // — e.g. a proof-mode technique bailed) must NOT
                                // terminate the portfolio: siblings may still be
                                // productively searching and about to prove
                                // SAT/UNSAT. It was this "first result, even
                                // `Unknown`, wins and stops everyone" behaviour that
                                // made proof-mode `--parallel` give up in a few
                                // seconds and solve only the easiest instances. An
                                // `Unknown` is recorded only as a fallback, and a
                                // later definitive result supersedes it.
                                let is_definitive = portfolio_result_is_definitive(&solve_result);
                                // Extract raw proof bytes before the solver is dropped (#8428).
                                let raw_proof_bytes =
                                    extract_proof_bytes(&mut solver, &solve_result, proof_mode);
                                let mut guard = result.lock();
                                let store = portfolio_should_store(
                                    guard.as_ref().map(|r| &r.result),
                                    &solve_result,
                                );
                                if store {
                                    *guard = Some(ThreadResult {
                                        result: solve_result,
                                        raw_proof_bytes,
                                    });
                                    if is_definitive {
                                        // Signal other workers to stop.
                                        terminate.store(true, Ordering::Relaxed);
                                    }
                                }
                            }
                        }
                    })
                })
                .collect();

            // Wait for all threads to finish.
            for handle in handles {
                let _: Result<(), _> = handle.join();
            }
        });

        // Extract result
        let guard = result.lock();
        match guard.as_ref() {
            Some(r) => (r.result.clone(), r.raw_proof_bytes.clone()),
            None => (SatResult::Unknown, None), // All threads were interrupted
        }
    }

    /// Set explicit configurations for tests.
    #[cfg(test)]
    fn with_configs(mut self, configs: Vec<SolverConfig>) -> Self {
        self.configs = configs;
        self.num_threads = self.configs.len().max(1);
        self.cached_features = None;
        // proof_mode is preserved from the outer constructor.
        self
    }
}

/// Convert a list of strategies to solver configs with sequential seeds.
///
/// When `num_threads` exceeds the number of base strategies, generates
/// diverse extended configurations for the additional threads (#8584).
/// Each extended config uses a meaningfully different combination of
/// inprocessing features, restart policy, branching heuristic, and
/// search parameters to maximize portfolio diversity.
fn strategies_to_configs(strategies: Vec<Strategy>, num_threads: usize) -> Vec<SolverConfig> {
    let mut configs: Vec<SolverConfig> = strategies
        .into_iter()
        .enumerate()
        .map(|(i, s)| {
            let mut config = s.to_config();
            config.seed = i as u64;
            config
        })
        .collect();

    // Generate diverse extended configs for threads beyond the base set.
    if num_threads > configs.len() {
        let extended = generate_extended_configs(num_threads, configs.len());
        configs.extend(extended);
    }

    configs
}

/// Number of distinct extended strategy templates (#8584).
const NUM_EXTENDED_TEMPLATES: usize = 9;

/// Generate diverse solver configurations for threads beyond the base 6.
///
/// Each template targets a different search strategy to maximize the
/// probability that at least one thread finds a solution quickly.
/// Templates are cycled with incrementing seeds for threads > 15.
///
/// Reference: CaDiCaL portfolio mode uses similar diversification across
/// restart policy, phase saving, and preprocessing aggressiveness.
fn generate_extended_configs(num_threads: usize, base_count: usize) -> Vec<SolverConfig> {
    let mut extended = Vec::with_capacity(num_threads - base_count);

    for thread_idx in base_count..num_threads {
        let template_idx = (thread_idx - base_count) % NUM_EXTENDED_TEMPLATES;
        let mut config = extended_template(template_idx);
        config.seed = thread_idx as u64;
        extended.push(config);
    }

    extended
}

/// Generate a single extended configuration template by index.
///
/// Nine diverse templates covering different search strategy axes:
/// - Vivification-heavy (idx 0)
/// - Stable-only search with long Luby restarts (idx 1)
/// - CHB branching via MAB with negative phase (idx 2)
/// - Heavy elimination (BVE + BCE + CCE + conditioning) (idx 3)
/// - Random exploration (5% random decisions) (idx 4)
/// - Long restarts with broad safe defaults (idx 5)
/// - Minimal inprocessing for fast BCP (idx 6)
/// - Sweep + congruence focused (idx 7)
/// - High random exploration + broad safe defaults (idx 8)
fn extended_template(idx: usize) -> SolverConfig {
    let defaults = portfolio_default_features();
    match idx {
        // Template 0: Vivification-heavy — clause strengthening emphasis
        0 => SolverConfig {
            features: crate::InprocessingFeatureProfile {
                preprocess: true,
                walk: true,
                warmup: true,
                shrink: true,
                hbr: true,
                vivify: true,
                subsume: true,
                probe: true,
                bve: false,
                bce: false,
                condition: false,
                decompose: false,
                factor: false,
                sbva: false,
                transred: true,
                htr: false,
                gate: false,
                congruence: true,
                sweep: false,
                backbone: true,
                symmetry: false,
                reorder: true,
                cce: false,
            },
            glucose_restarts: true,
            chrono_enabled: true,
            ..Default::default()
        },
        // Template 1: Stable-only search — force stable mode with long Luby
        1 => SolverConfig {
            features: defaults,
            glucose_restarts: false,
            chrono_enabled: true,
            stable_only: true,
            restart_base: Some(250),
            ..Default::default()
        },
        // Template 2: CHB branching via MAB — different variable selection
        2 => SolverConfig {
            features: defaults,
            glucose_restarts: true,
            chrono_enabled: false,
            initial_phase: Some(false),
            branch_selector_ucb1: true,
            ..Default::default()
        },
        // Template 3: Heavy elimination — BVE + BCE + CCE + conditioning
        3 => SolverConfig {
            features: crate::InprocessingFeatureProfile {
                preprocess: true,
                walk: true,
                warmup: true,
                shrink: true,
                hbr: false,
                vivify: false,
                subsume: true,
                probe: false,
                bve: true,
                bce: true,
                condition: true,
                decompose: false,
                factor: true,
                sbva: true,
                transred: false,
                htr: false,
                gate: true,
                congruence: false,
                sweep: false,
                backbone: false,
                symmetry: true,
                reorder: true,
                cce: true,
            },
            glucose_restarts: false,
            chrono_enabled: true,
            initial_phase: Some(true),
            ..Default::default()
        },
        // Template 4: Random exploration — 5% random variable decisions
        4 => SolverConfig {
            features: defaults,
            glucose_restarts: true,
            chrono_enabled: true,
            random_var_freq: Some(0.05),
            ..Default::default()
        },
        // Template 5: Long restarts with broad safe defaults
        5 => SolverConfig {
            features: crate::InprocessingFeatureProfile {
                bce: true,
                condition: true,
                symmetry: true,
                cce: true,
                ..defaults
            },
            glucose_restarts: false,
            chrono_enabled: false,
            restart_base: Some(500),
            stable_phase_init: Some(5000),
            ..Default::default()
        },
        // Template 6: Minimal inprocessing — fast BCP throughput
        6 => SolverConfig {
            features: crate::InprocessingFeatureProfile {
                preprocess: true,
                walk: true,
                warmup: true,
                shrink: true,
                hbr: false,
                vivify: false,
                subsume: false,
                probe: false,
                bve: false,
                bce: false,
                condition: false,
                decompose: false,
                factor: false,
                sbva: false,
                transred: false,
                htr: false,
                gate: false,
                congruence: false,
                sweep: false,
                backbone: false,
                symmetry: false,
                reorder: false,
                cce: false,
            },
            glucose_restarts: true,
            chrono_enabled: false,
            initial_phase: Some(false),
            ..Default::default()
        },
        // Template 7: Sweep + congruence focused — structural simplification
        7 => SolverConfig {
            features: crate::InprocessingFeatureProfile {
                preprocess: true,
                walk: true,
                warmup: true,
                shrink: true,
                hbr: false,
                vivify: false,
                subsume: false,
                probe: false,
                bve: false,
                bce: false,
                condition: false,
                decompose: true,
                factor: false,
                sbva: false,
                transred: false,
                htr: false,
                gate: true,
                congruence: true,
                sweep: true,
                backbone: false,
                symmetry: false,
                reorder: true,
                cce: false,
            },
            glucose_restarts: false,
            chrono_enabled: true,
            restart_base: Some(150),
            ..Default::default()
        },
        // Template 8: High random exploration + broad safe defaults
        8 => SolverConfig {
            features: crate::InprocessingFeatureProfile {
                bce: true,
                condition: true,
                symmetry: true,
                cce: true,
                ..defaults
            },
            glucose_restarts: true,
            chrono_enabled: true,
            random_var_freq: Some(0.10),
            stable_phase_init: Some(2000),
            ..Default::default()
        },
        // Safety: cycle back (should not reach here due to modulo)
        _ => unreachable!("template index must be < NUM_EXTENDED_TEMPLATES"),
    }
}

/// Apply feature-driven adaptive adjustments to a solver.
///
/// This applies the same threshold rules that the DIMACS single-thread path uses
/// (conditioning ratio gate, random k-SAT symmetry, industrial reorder, etc.),
/// ensuring portfolio threads also benefit from instance-aware technique gating.
///
/// Uses the unified `apply_feature_profile()` method to write back ALL profile
/// fields (#8149), eliminating the field-by-field duplication that previously
/// silently dropped adjustments.
fn apply_adaptive_adjustments(solver: &mut Solver, features: &SatFeatures, class: &InstanceClass) {
    let mut profile = solver.inprocessing_feature_profile();
    crate::adaptive::adjust_features_for_instance(features, class, &mut profile);
    solver.apply_feature_profile(&profile);
}

/// Create a solver for one portfolio worker and wire the shared cancellation
/// flag into both preprocessing/inprocessing and the CDCL search loop.
fn create_portfolio_worker_solver(
    num_vars: usize,
    num_clauses: usize,
    config: &SolverConfig,
    proof_mode: bool,
    terminate: Arc<AtomicBool>,
) -> Solver {
    let mut solver = create_solver_from_config(num_vars, num_clauses, config, proof_mode);
    solver.set_interrupt(terminate);
    solver
}

/// Create a solver instance from a configuration.
///
/// When `proof_mode` is true, creates the solver with an in-memory LRAT
/// proof writer so the forward proof is captured during solving (#8428).
/// Using LRAT (not DRAT) enables full clause ID tracking and backward
/// proof reconstruction, and the forward LRAT bytes serve as the complete
/// proof output for both LRAT and DRAT formats (DRAT is derived by
/// stripping clause IDs and hints from the LRAT output).
/// The caller extracts the proof bytes after solving via [`extract_proof_bytes`].
fn create_solver_from_config(
    num_vars: usize,
    num_clauses: usize,
    config: &SolverConfig,
    proof_mode: bool,
) -> Solver {
    let mut solver = if proof_mode {
        // Use an in-memory LRAT writer so the full forward proof (including
        // clauses derived during BCP at level 0) is captured. LRAT enables
        // clause ID tracking and inprocessing proof-overrides (e.g., disabling
        // sweep). The forward LRAT bytes are extracted from the winning thread
        // after solving and used for the proof file output (#8428).
        let proof_output = ProofOutput::lrat_text(Vec::<u8>::new(), num_clauses as u64);
        Solver::with_proof_output(num_vars, proof_output)
    } else {
        Solver::new(num_vars)
    };

    // Apply the full feature profile via the unified setter (#8149).
    solver.apply_feature_profile(&config.features);
    solver.set_glucose_restarts(config.glucose_restarts);
    solver.set_chrono_enabled(config.chrono_enabled);

    // Set initial phase if specified
    if let Some(phase) = config.initial_phase {
        solver.set_initial_phase(phase);
    }

    // Enable MAB branch selection if requested (portfolio diversity).
    solver.set_branch_selector_ucb1(config.branch_selector_ucb1);

    // Set random seed for variable selection tie-breaking
    solver.set_random_seed(config.seed);

    // Extended diversification fields (#8584)
    if let Some(base) = config.restart_base {
        solver.set_restart_base(base);
    }
    if let Some(init) = config.stable_phase_init {
        solver.set_stable_phase_init(init);
    }
    if let Some(freq) = config.random_var_freq {
        solver.set_random_var_freq(freq);
    }
    if config.stable_only {
        solver.set_stable_only(true);
    }
    solver.set_chrono_reuse_trail(config.chrono_reuse_trail);
    if config.mode_equiticks {
        solver.set_mode_equiticks(true);
    }
    if config.mode_eqt_progress {
        solver.set_eqt_progress_default();
    }

    solver
}

/// Whether a portfolio worker's result may be emitted as the portfolio's
/// answer (task #14 soundness gate).
///
/// `Sat` and `Unknown` are always safe to surface: a `Sat` model is verified
/// against the original formula by the solver's model gate before it reaches the
/// join, and `Unknown` asserts nothing. An `Unsat` is only a **complete, sound
/// refutation of the ORIGINAL formula** when the worker's clause database was
/// not contaminated by (potentially unsound) cross-worker clause sharing — i.e.
/// when sharing was inactive — or when the worker carries a machine-checkable
/// proof (`proof_mode`, which also implies sharing was inactive). An untrusted
/// `Unsat` must be dropped so the portfolio can fail closed to another worker's
/// sound result or to `Unknown`, never to a wrong `UNSAT`.
#[inline]
fn portfolio_result_is_trustworthy(
    result: &SatResult,
    proof_mode: bool,
    clause_sharing_active: bool,
) -> bool {
    match result {
        SatResult::Unsat(_) => proof_mode || !clause_sharing_active,
        SatResult::Sat(_) | SatResult::Unknown => true,
    }
}

/// A *definitive* portfolio result is one that answers the instance: `Sat` or
/// `Unsat`. Only a definitive result may win the portfolio and stop the other
/// workers; `Unknown` (a worker gave up) never does.
#[inline]
fn portfolio_result_is_definitive(result: &SatResult) -> bool {
    matches!(result, SatResult::Sat(_) | SatResult::Unsat(_))
}

/// Decide whether an incoming trustworthy worker result should replace the
/// currently stored portfolio result.
///
/// Completeness rule (#parallel-bv): a definitive (`Sat`/`Unsat`) result fills
/// an empty slot or supersedes a stored `Unknown` fallback; an `Unknown` only
/// fills an empty slot; a definitive result is never overwritten. Together with
/// "only a definitive result stops the other workers", this stops a single
/// worker's early `Unknown` from ending the whole portfolio while siblings are
/// still productively searching.
#[inline]
fn portfolio_should_store(existing: Option<&SatResult>, incoming: &SatResult) -> bool {
    match existing {
        None => true,
        Some(existing) => portfolio_result_is_definitive(incoming) && existing.is_unknown(),
    }
}

/// Extract raw forward LRAT proof bytes from a solver after solving (#8428).
///
/// Returns `Some(bytes)` when `proof_mode` is true and the result is UNSAT.
/// The solver's proof writer is consumed (taken) by this call.
fn extract_proof_bytes(
    solver: &mut Solver,
    result: &SatResult,
    proof_mode: bool,
) -> Option<Vec<u8>> {
    if !proof_mode || !result.is_unsat() {
        return None;
    }
    let proof_output = solver.take_proof_writer()?;
    match proof_output.into_vec() {
        Ok(bytes) => Some(bytes),
        Err(e) => {
            tracing::warn!("failed to extract proof bytes from portfolio thread: {e}");
            None
        }
    }
}

#[cfg(test)]
#[path = "portfolio_tests.rs"]
mod tests;
