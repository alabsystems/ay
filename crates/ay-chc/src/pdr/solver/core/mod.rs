// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core PDR utilities and initialization.
//!
//! Classification functions are in `classify`, cache operations in `cache_ops`.

mod cache_ops;
mod classify;
mod formula_analysis;
mod lemma_mgmt;
mod scc;

// Re-export public free functions so callers can use `core::filter_to_canonical_vars`
// and `core::ensure_prop_solver_split` without path changes.
pub(in crate::pdr::solver) use classify::{ensure_prop_solver_split, filter_to_canonical_vars};

use crate::pdr::implication_cache::ImplicationCache;
use classify::{
    clause_has_ite, clause_is_bitvector_only, clause_is_integer_arithmetic, clause_is_pure_lia,
};

use super::{
    build_canonical_predicate_vars, build_predicate_users, build_push_cache_deps, caches,
    compute_reachable_predicates, fs, tarjan_scc, Arc, ChcExpr, ChcOp, ChcParser, ChcProblem,
    ChcResult, ChcSort, ChcVar, ConvergenceMonitor, ConvexClosure, Frame, FxHashMap, FxHashSet,
    Lemma, ObligationQueue, Path, PdrConfig, PdrResult, PdrSolver, PdrTelemetry, PredicateId,
    PriorityPob, ProofObligation, ReachFact, ReachFactId, ReachFactStore, ReachabilityState,
    RestartState, SmtResult, SmtValue, TracingState, VerificationCounters,
};
use ay_jit::expr_eval::ExprLike;

fn canonical_model_from_head_args(
    canonical_vars: &[ChcVar],
    head_args: &[ChcExpr],
    model: &FxHashMap<String, SmtValue>,
) -> Option<FxHashMap<String, SmtValue>> {
    if canonical_vars.len() != head_args.len() {
        return None;
    }

    let mut canonical_model = FxHashMap::default();
    for (canonical_var, head_arg) in canonical_vars.iter().zip(head_args) {
        let value = crate::expr::evaluate_expr(head_arg, model)?;
        canonical_model.insert(canonical_var.name.clone(), value);
    }
    Some(canonical_model)
}

/// Frame-state epoch for blocking-countermodel cache invalidation (#pdr-chain).
///
/// Monotone fingerprint of all frame lemma sets: changes whenever any lemma is
/// added to or removed from any frame. Cached blocking countermodels are only
/// valid while the frames they were validated against are unchanged.
pub(in crate::pdr::solver) fn frames_lemma_epoch(frames: &[Frame]) -> u64 {
    frames
        .iter()
        .map(|frame| frame.total_lemma_revision())
        .sum()
}

pub(in crate::pdr::solver) fn record_validated_blocking_countermodel_from_head_args(
    implication_cache: &mut ImplicationCache,
    frame_epoch: u64,
    canonical_vars: Option<&[ChcVar]>,
    pred: PredicateId,
    level: usize,
    head_args: &[ChcExpr],
    model: &FxHashMap<String, SmtValue>,
    blocking_formula: &ChcExpr,
) {
    implication_cache.note_frame_epoch(frame_epoch);
    let Some(canonical_vars) = canonical_vars else {
        implication_cache.record_blocking_countermodel(pred.index(), level, model);
        return;
    };
    let Some(canonical_model) = canonical_model_from_head_args(canonical_vars, head_args, model)
    else {
        implication_cache.record_blocking_countermodel(pred.index(), level, model);
        return;
    };

    if !blocking_formula.is_jit_compilable()
        || !matches!(
            crate::expr::evaluate_expr(blocking_formula, &canonical_model),
            Some(SmtValue::Bool(true))
        )
    {
        implication_cache.record_blocking_countermodel(pred.index(), level, &canonical_model);
        return;
    }

    implication_cache.record_blocking_countermodel_with_native_helper_validation(
        pred.index(),
        level,
        &canonical_model,
        blocking_formula,
    );
}

impl PdrSolver {
    /// Frame-state epoch for blocking-countermodel cache invalidation
    /// (#pdr-chain). See [`frames_lemma_epoch`].
    pub(in crate::pdr::solver) fn frames_lemma_epoch(&self) -> u64 {
        frames_lemma_epoch(&self.frames)
    }

    /// Get cumulative frame constraint for a predicate at level k.
    /// This includes all lemmas from frames 1..=k (PDR frames are monotonic).
    ///
    /// Results are cached per (level, pred) and invalidated when any frame's
    /// lemma revision for this predicate changes (#2763).
    pub(in crate::pdr::solver) fn cumulative_frame_constraint(
        &self,
        level: usize,
        pred: PredicateId,
    ) -> Option<ChcExpr> {
        let num_frames = level.min(self.frames.len() - 1);

        // Compute revision fingerprint: sum of per-frame revisions for this predicate.
        // If any frame adds a lemma for pred, the sum changes → cache miss.
        let revision_sum: u64 = (1..=num_frames)
            .map(|lvl| self.frames[lvl].predicate_lemma_revision(pred))
            .sum();

        // Check cache
        let key = (level, pred);
        if let Some((cached_rev, cached_formula)) =
            self.caches.cumulative_constraint_cache.borrow().get(&key)
        {
            if *cached_rev == revision_sum {
                return Some(cached_formula.clone());
            }
        }

        // Cache miss: recompute
        let mut all_lemmas: Vec<&Lemma> = Vec::with_capacity(num_frames * 4);
        for lvl in 1..=num_frames {
            all_lemmas.extend(
                self.frames[lvl]
                    .lemmas
                    .iter()
                    .filter(|l| l.predicate == pred)
                    // Skip Bool(false) lemmas: they poison and_all via short-circuit,
                    // producing a trivially-false invariant that fails entry-clause
                    // verification (#3121).
                    .filter(|l| !matches!(l.formula, ChcExpr::Bool(false))),
            );
        }

        if all_lemmas.is_empty() {
            None
        } else {
            // Deduplicate by formula hash to avoid repeated `to_string()` allocation (#1037).
            // Collision safety: bucket by hash then confirm structural equality.
            let mut seen: FxHashMap<u64, Vec<&ChcExpr>> = FxHashMap::default();
            let unique: Vec<_> = all_lemmas
                .into_iter()
                .filter(|lemma| {
                    let bucket = seen.entry(lemma.formula_hash).or_default();
                    if bucket.contains(&&lemma.formula) {
                        false
                    } else {
                        bucket.push(&lemma.formula);
                        true
                    }
                })
                .collect();

            if unique.is_empty() {
                None
            } else {
                // Build flat conjunction (#2508: avoid deep right-skewed And trees)
                let formula = ChcExpr::and_all(unique.into_iter().map(|l| l.formula.clone()));
                self.insert_cumulative_constraint_cache_entry(key, (revision_sum, formula.clone()));
                Some(formula)
            }
        }
    }
    /// Check if the solver should stop (cancelled by portfolio, solve_timeout exceeded,
    /// reach-fact store saturation, global TermStore memory exceeded #2769,
    /// or per-engine term memory budget exceeded #8600).
    #[inline]
    pub(in crate::pdr) fn is_cancelled(&self) -> bool {
        self.config
            .cancellation_token
            .as_ref()
            .is_some_and(crate::cancellation::CancellationToken::is_cancelled)
            || self
                .config
                .external_cancellation_token
                .as_ref()
                .is_some_and(crate::cancellation::CancellationToken::is_cancelled)
            || self
                .solve_deadline
                .is_some_and(|d| ay_core::time::Instant::now() >= d)
            || self.reachability.reach_facts_saturated
            // No-progress circuit breaker: the SMT layer has observed this solve
            // spinning on the same unassignable evaluable-position free-variable
            // set (re-issuing the identical fail-closed Unknown; see
            // `SmtContext::sat_or_unknown`). Treat it as a cooperative
            // cancellation so every engine loop that already polls `is_cancelled`
            // (main loop, obligation `strengthen`, predecessor reachability, …)
            // bails to Unknown promptly instead of grinding to the wall-clock
            // watchdog SIGKILL. Sound: only ever degrades the verdict to Unknown.
            || crate::smt::no_progress_breaker_tripped()
            || ay_core::TermStore::global_memory_exceeded()
            || self.smt.term_memory_exceeded()
    }

    /// Parse a CHC input string and run PDR.
    ///
    /// `pub(crate)` — external callers should use [`AdaptivePortfolio::solve()`]
    /// which returns [`VerifiedChcResult`]. Part of #5747: structural verification invariant.
    pub(crate) fn solve_from_str(input: &str, mut config: PdrConfig) -> ChcResult<PdrResult> {
        let problem = ChcParser::parse(input)?;

        // Try case-split for unconstrained constant arguments.
        // This handles benchmarks like dillig12_m where an argument is constant
        // throughout execution but unconstrained at init, and used as a mode flag
        // in ITE guards (compared against some constant).
        if config.tla_trace_path.is_none() {
            let case_split_start = ay_core::time::Instant::now();
            if let Some(case_split_result) = Self::try_case_split_solve(&problem, config.clone()) {
                return Ok(case_split_result);
            }
            let Some(fallback_config) =
                Self::case_split_fallback_config(config, case_split_start.elapsed())
            else {
                return Ok(PdrResult::Unknown);
            };
            config = fallback_config;
        }

        let trace_path = config.tla_trace_path.clone();
        let mut solver = Self::new(problem, config);
        if let Some(path) = trace_path.as_deref() {
            solver.enable_tla_trace_from_path(path);
        }
        Ok(solver.solve())
    }

    /// Solve a pre-parsed problem with case-split optimization.
    ///
    /// This is the main entry point for solving CHC problems where the
    /// problem has already been parsed. It includes case-split for
    /// unconstrained constant arguments.
    pub(crate) fn solve_problem(problem: &ChcProblem, mut config: PdrConfig) -> PdrResult {
        // Try case-split for unconstrained constant arguments.
        // Skip when running under a cancellation token (portfolio engine) since
        // the Adaptive strategy already runs case-split as Stage 0 (#5399).
        // Redundant case-splits consume the portfolio timeout before the main
        // solver reaches kernel discovery. Also skip under trace mode so the
        // top-level PDR run owns a single coherent JSONL file instead of
        // per-branch solvers recreating it.
        if config.cancellation_token.is_none() && config.tla_trace_path.is_none() {
            let case_split_start = ay_core::time::Instant::now();
            if let Some(case_split_result) = Self::try_case_split_solve(problem, config.clone()) {
                return case_split_result;
            }
            let Some(fallback_config) =
                Self::case_split_fallback_config(config, case_split_start.elapsed())
            else {
                return PdrResult::Unknown;
            };
            config = fallback_config;
        }

        let trace_path = config.tla_trace_path.clone();
        let mut solver = Self::new(problem.clone(), config);
        if let Some(path) = trace_path.as_deref() {
            solver.enable_tla_trace_from_path(path);
        }
        solver.solve()
    }

    pub(in crate::pdr::solver) fn case_split_fallback_config(
        mut config: PdrConfig,
        elapsed: std::time::Duration,
    ) -> Option<PdrConfig> {
        if let Some(timeout) = config.solve_timeout {
            let remaining = timeout.checked_sub(elapsed)?;
            if remaining.is_zero() {
                return None;
            }
            config.solve_timeout = Some(remaining);
        }
        Some(config)
    }

    /// Parse a CHC file and run PDR.
    ///
    /// `pub(crate)` — external callers should use [`AdaptivePortfolio::solve()`]
    /// which returns [`VerifiedChcResult`]. Part of #5747: structural verification invariant.
    pub(crate) fn solve_from_file(
        path: impl AsRef<Path>,
        config: PdrConfig,
    ) -> ChcResult<PdrResult> {
        let input = fs::read_to_string(path)?;
        Self::solve_from_str(&input, config)
    }

    /// Create a new PDR solver
    pub(crate) fn new(mut problem: ChcProblem, config: PdrConfig) -> Self {
        // Expand nullary fail predicates first (CHC-COMP pattern)
        // This transforms `fail => false` queries into direct queries
        if !config.preserve_original_clauses {
            problem.expand_nullary_fail_queries(config.verbose);
        }
        let model_problem = problem.clone();

        // #6047: Try full scalarization (including BV-indexed arrays) first.
        // If the result has reasonable arity (≤64 params per predicate), keep it.
        // Otherwise fall back to Int-only scalarization to avoid arity explosion
        // (model-checker-consumer harnesses: 68 → 191 params with full BV scalarization, #6163).
        // Gated on pre-scalarization array sort check (#6366).
        let has_array_sorts_before = problem.predicates().iter().any(|p| {
            p.arg_sorts
                .iter()
                .any(|s| matches!(s, ChcSort::Array(_, _)))
        });
        let mut array_scalarization_maps = Vec::new();
        if has_array_sorts_before
            && !config.disable_array_scalarization
            && !config.preserve_original_clauses
        {
            let max_arity = problem
                .predicates()
                .iter()
                .map(|p| p.arg_sorts.len())
                .max()
                .unwrap_or(0);
            let mut scalarized = problem.clone();
            if config.array_scalarization_keep_const_keys_with_symbolic_accesses {
                scalarized.rewrite_clause_local_constant_aliases_for_array_scalarization();
            }
            let scalarized_map =
                if config.array_scalarization_keep_const_keys_with_symbolic_accesses {
                    scalarized.try_scalarize_const_array_selects_allow_symbolic_keys_with_map(
                        &config.array_scalarization_extra_indices,
                    )
                } else if config.array_scalarization_extra_indices.is_empty() {
                    scalarized.try_scalarize_const_array_selects_with_map()
                } else {
                    scalarized.try_scalarize_const_array_selects_with_extra_indices_with_map(
                        &config.array_scalarization_extra_indices,
                    )
                };
            let new_max_arity = scalarized
                .predicates()
                .iter()
                .map(|p| p.arg_sorts.len())
                .max()
                .unwrap_or(0);
            if new_max_arity <= 64 || new_max_arity <= max_arity * 3 {
                problem = scalarized;
                if let Some(map) = scalarized_map {
                    array_scalarization_maps.push(map);
                }
            } else {
                // Full scalarization causes arity explosion; try property-directed
                // scalarization instead. This only scalarizes at constant indices
                // found in query clauses (typically 1-5 indices for model-checker-consumer harnesses),
                // adding minimal parameters while enabling PDR to check array
                // properties without bit-blasting overhead. Part of #6047.
                if let Some(map) = problem.try_scalarize_property_directed_with_map() {
                    array_scalarization_maps.push(map);
                }
                // Also apply Int-only scalarization for any remaining Int-indexed arrays.
                if let Some(map) = problem.try_scalarize_int_indexed_const_array_selects_with_map()
                {
                    array_scalarization_maps.push(map);
                }
            }
        }

        // #6366: Detect whether the POST-scalarization problem still has array sorts.
        // Must be checked after scalarization because successful scalarization removes
        // array sorts from predicate signatures (e.g., Array Int Bool → scalar Int params).
        // This flag gates all array-specific overhead in the hot blocking loop.
        let uses_arrays = problem.predicates().iter().any(|p| {
            p.arg_sorts
                .iter()
                .any(|s| matches!(s, ChcSort::Array(_, _)))
        });
        // #8660: Count the maximum number of Array-sorted parameters across all predicates.
        // This enables more aggressive optimization when there are many array params
        // (e.g., tighter per-query timeouts, more aggressive generalization).
        let max_array_params: usize = problem
            .predicates()
            .iter()
            .map(|p| {
                p.arg_sorts
                    .iter()
                    .filter(|s| matches!(s, ChcSort::Array(_, _)))
                    .count()
            })
            .max()
            .unwrap_or(0);
        // #8660: Extract property-relevant array indices from query clauses.
        // Only indices that appear in the property need to be tracked in blocking cubes.
        let property_array_indices = if uses_arrays {
            let pai = Self::extract_property_array_indices(&problem);
            if config.verbose {
                safe_eprintln!(
                    "PDR: uses_arrays = true, max_array_params = {}, property_uses_arrays = {}, property_indices_for {} predicates (#8660)",
                    max_array_params,
                    pai.property_uses_arrays,
                    pai.indices.len()
                );
                for (pred, param_indices) in &pai.indices {
                    for (param_pos, indices) in param_indices {
                        safe_eprintln!(
                            "PDR:   pred {} param {} -> {} property indices",
                            pred.index(),
                            param_pos,
                            indices.len()
                        );
                    }
                }
            }
            pai
        } else {
            if config.verbose && uses_arrays {
                safe_eprintln!(
                    "PDR: uses_arrays = true, max_array_params = {} (#8660)",
                    max_array_params
                );
            }
            super::blocking::PropertyArrayIndices::default()
        };

        // OR splitting is enabled by default to eliminate disjunctive constraints that
        // can force expensive SMT case-splitting during verification (e.g. three_dots_moving_2).
        if !config.preserve_original_clauses {
            problem.try_split_ors_in_clauses(8, config.verbose);
        }
        let problem_has_ite = problem.clauses().iter().any(clause_has_ite);
        let problem_is_integer_arithmetic_before_ite_split =
            problem.clauses().iter().all(clause_is_integer_arithmetic);
        // ITE splitting: generous limit for single-predicate problems; conservative
        // re-enable for multi-predicate integer-arithmetic problems where ITEs keep
        // the clause surface off the pure-LIA fast path (e.g. s_multipl_24, #1362).
        // Non-integer problems still skip splitting to avoid clause churn on BV/array paths.
        let num_predicates = problem.predicates().len();
        if config.preserve_original_clauses {
            // Validation witnesses are keyed by the original clauses. Keep the
            // clause vector intact instead of applying solve-time case splits.
        } else if num_predicates <= 1 {
            problem.try_split_ites_in_clauses(32, config.verbose);
        } else if problem_has_ite && problem_is_integer_arithmetic_before_ite_split {
            problem.try_split_ites_in_clauses(8, config.verbose);
        } else if config.verbose {
            safe_eprintln!(
                "CHC: skipping ite-splitting for multi-predicate problem ({} predicates)",
                num_predicates
            );
        }
        // #1362: Snapshot error clause constraints BEFORE mod/div elimination.
        let original_error_constraints: FxHashMap<usize, ChcExpr> = problem
            .clauses()
            .iter()
            .enumerate()
            .filter(|(_, c)| matches!(c.head, crate::ClauseHead::False))
            .filter_map(|(i, c)| c.body.constraint.as_ref().map(|cst| (i, cst.clone())))
            .collect();
        if config.verbose && !original_error_constraints.is_empty() {
            safe_eprintln!(
                "PDR: Snapshot {} original error clause constraints before mod/div elimination (#1362)",
                original_error_constraints.len()
            );
        }
        // #7410 D2: eliminate_mod_in_constraints DISABLED.
        // A/B test at commit 494cf19ac showed +9 SAT benchmarks (33→42/55) with
        // 0 regressions when disabled. The auxiliary quotient/remainder variables
        // from Euclidean decomposition make PDR lemma discovery harder. The SMT
        // solver's LIA theory handles (mod x k) natively for constant k, and
        // expr_is_integer_arithmetic() already classifies mod/div as pure LIA.

        // #6480/#6358: Detect whether the normalized clause surface is pure LIA
        // (no ITE/mod/div) before trusting incremental SAT results. Parser
        // normalization can move arithmetic ITEs out of the residual body
        // constraint and into predicate arguments, so scanning only
        // `clause.body.constraint` is insufficient for benchmarks like
        // `half_true_modif_m`.
        let problem_is_pure_lia_raw = problem.clauses().iter().all(clause_is_pure_lia);
        let problem_is_integer_arithmetic =
            problem.clauses().iter().all(clause_is_integer_arithmetic);
        // #7048: Integer arithmetic problems (ITE + mod/div over ints) are
        // effectively pure LIA: the SMT solver handles mod/div natively.
        // Promote to pure LIA to enable full incremental SAT trust and
        // standard generalization (no BV-specific overhead).
        let problem_is_pure_lia = problem_is_pure_lia_raw || problem_is_integer_arithmetic;
        // #8205: Detect BV-only problems for incremental PDR gating.
        // BV-only problems are safe for incremental PDR: the #6583 regression
        // was LIA-specific (theory lemma scope issues). Also check predicate
        // sorts to ensure no Int/Real parameters slip through.
        let problem_is_bitvector_only = problem.clauses().iter().all(clause_is_bitvector_only)
            && problem.predicates().iter().all(|p| {
                p.arg_sorts
                    .iter()
                    .all(|s| matches!(s, ChcSort::Bool | ChcSort::BitVec(_)))
            });
        if config.verbose {
            safe_eprintln!(
                "PDR: problem_is_pure_lia = {} (raw={}, int_arith={}, gates incremental SAT trust, #6480/#7048)",
                problem_is_pure_lia, problem_is_pure_lia_raw, problem_is_integer_arithmetic
            );
            safe_eprintln!(
                "PDR: problem_is_bitvector_only = {} (gates incremental PDR for BV, #8205)",
                problem_is_bitvector_only
            );
        }

        let predicate_vars = build_canonical_predicate_vars(&problem);
        let push_cache_deps = build_push_cache_deps(&problem);
        let predicate_users = build_predicate_users(&problem);
        // Build cache of predicates that have fact clauses (computed once)
        let predicates_with_facts: FxHashSet<PredicateId> = problem
            .facts()
            .filter_map(|f| f.head.predicate_id())
            .collect();
        // Compute predicates reachable from init via transitions (#1419)
        let reachable_predicates = compute_reachable_predicates(&problem, &predicates_with_facts);
        // Compute SCC info for cyclic predicate handling
        let scc_info = tarjan_scc(&problem);
        if config.verbose {
            for scc in &scc_info.sccs {
                if scc.is_cyclic && scc.predicates.len() > 1 {
                    safe_eprintln!(
                        "PDR: Detected cyclic SCC with {} predicates: {:?}",
                        scc.predicates.len(),
                        scc.predicates.iter().map(|p| p.index()).collect::<Vec<_>>()
                    );
                }
            }
        }
        // Extract restart threshold before moving config
        let restart_threshold_init = config.restart_initial_threshold;
        let mut smt = problem.make_smt_context();
        smt.set_verbose(config.verbose);
        // Spacer-mode engine (inc-12): route per-pob checks executor-first,
        // skipping the internal-loop slice that punts ~23% on wide-Bool
        // transition-system queries. Per-solver policy — other engines and
        // validation contexts keep the internal-first default.
        smt.set_executor_first_check_sat(config.executor_first_check_sat);
        let problem_size_hint = super::convergence_monitor::ProblemSizeHint::from_problem(&problem);
        Self {
            problem,
            model_problem,
            array_scalarization_maps,
            config,
            caches: caches::PdrCacheStore::new(
                predicate_vars,
                push_cache_deps,
                predicate_users,
                predicates_with_facts,
                reachable_predicates,
            ),
            // Start with F_0 (init) and F_1 (true).
            frames: vec![Frame::new(), Frame::new()],
            obligations: ObligationQueue::default(),
            iterations: 0,
            smt,
            array_clause_sessions: caches::LruSolverMap::new(caches::MAX_ARRAY_SESSIONS),
            array_skolem_state: super::blocking::ArraySkolemState::default(),
            mbp: crate::mbp::Mbp::new(),
            reachability: ReachabilityState::new(),
            verification: VerificationCounters::default(),
            convex_closure_engine: ConvexClosure::new(),
            scc_info,
            // Restart state (#1270)
            restart: RestartState::new(restart_threshold_init),
            // TLA2 trace state (#3301)
            tracing: TracingState::default(),
            // Solve deadline (set at start of solve() from config.solve_timeout)
            solve_deadline: None,
            // Total-startup-discovery deadline (set by run_startup_discovery, inc-12)
            startup_deadline: None,
            // Telemetry counters (#2450, #3301)
            telemetry: PdrTelemetry::default(),
            // Convergence monitor for stagnation detection
            convergence: ConvergenceMonitor::new(),
            generalization_escalation_level: 0,
            generalization_strategy: super::GeneralizationStrategy::Default,
            terminated_by_stagnation: false,
            lemma_quality: super::convergence_monitor::LemmaQualityMetrics::new(),
            problem_size_hint,
            // Per-predicate persistent solvers (#6358).
            // LRU-bounded; contexts created lazily on first query (#6554).
            prop_solvers: caches::LruSolverMap::new(caches::MAX_PROP_SOLVERS),
            // Problem feature flag (#6366): gates array-specific overhead.
            uses_arrays,
            // #8660: Maximum array params across all predicates.
            max_array_params,
            // #8660: Property-relevant array indices from query clauses.
            property_array_indices,
            // Problem feature flag (#6480): gates incremental SAT trust.
            problem_is_pure_lia,
            // Problem feature flag (#5970): relaxed gate for ITE/mod/div.
            problem_is_integer_arithmetic,
            // Problem feature flag (#8205): gates incremental PDR for BV workloads.
            problem_is_bitvector_only,
            // Cross-check budget (#5970): 5s total for executor cross-checks.
            cross_check_budget: std::time::Duration::from_secs(5),
            // Startup convergence flag (#5970).
            startup_converged: false,
            strict_validation_demotions: 0,
            startup_converged_frame1_len: None,
            houdini_pruned_frame1_len: None,
            // Counterexample-guided candidate-repair budget (#4751 L4).
            candidate_repair_rounds_used: 0,
            // Deferred entry-inductive retry queue (#5970).
            deferred_entry_invariants: Vec::new(),
            // Deferred self-inductive retry queue (menlo_park_term_simpl_2).
            deferred_self_inductive_invariants: Vec::new(),
            // Rejected-invariant cache (#7006): skip re-checking known failures.
            rejected_invariants: FxHashSet::default(),
            // Persistent executor backend (#7984): lazily initialized.
            executor_backend: None,
            original_error_constraints,
            // inc-9: bounded-BMC cex replay memo (deepest failed replay).
            failed_replay_depth: None,
        }
    }

    /// Get or create a per-predicate prop_solver with full lemma backfill (#6358).
    ///
    /// When a `PredicatePropSolver` is lazily created, it must contain ALL existing
    /// frame lemmas for that predicate. Without backfill, queries against a freshly
    /// created prop_solver would miss lemmas and return incorrect SAT results.
    ///
    /// This method:
    /// 1. Checks if a prop_solver already exists for `pred` (fast path)
    /// 2. If not, creates one and asserts every existing frame lemma for `pred`
    /// 3. Returns a mutable reference to the prop_solver
    ///
    /// All prop_solver access should go through this method to ensure correctness.
    ///
    /// NOTE: In contexts where `self.problem.clauses()` is borrowed (clause loop
    /// iterations), use `ensure_prop_solver_split` with explicit field borrows to
    /// avoid borrow conflicts.
    pub(in crate::pdr) fn ensure_prop_solver(
        &mut self,
        pred: PredicateId,
    ) -> &mut super::prop_solver::PredicatePropSolver {
        ensure_prop_solver_split(&mut self.prop_solvers, &self.frames, pred)
    }

    /// Get clause-guarded propagated lemmas as a conjunction, applied to clause head args.
    ///
    /// Returns `Bool(true)` if there are no clause-guarded lemmas for this (pred, clause)
    /// at the requested level.
    ///
    /// # Design (#2459 Phase 3, #2536 level-awareness)
    ///
    /// Z3 Spacer asserts `(rule_tag => renamed_lemma)` into the parent's solver,
    /// level-parameterized: a child lemma at level L is asserted at parent levels
    /// 1..next_level(L). AY iterates per-clause, so the tag guard is implicit.
    /// Level filtering ensures we only include lemmas valid at the requested level.
    ///
    /// A lemma with `max_level >= check_level` is included; others are skipped.
    /// Reference: z3/src/muz/spacer/spacer_context.cpp:1949-1954
    pub(in crate::pdr) fn clause_guarded_constraint(
        &self,
        pred: PredicateId,
        clause_index: usize,
        head_args: &[ChcExpr],
        check_level: usize,
    ) -> ChcExpr {
        let Some(guarded) = self.caches.clause_guarded_lemmas.get(&(pred, clause_index)) else {
            return ChcExpr::Bool(true);
        };
        if guarded.is_empty() {
            return ChcExpr::Bool(true);
        }
        let mut conjuncts = Vec::with_capacity(guarded.len());
        for (lemma, max_level) in guarded {
            // #2536: Only include lemmas valid at this level.
            // Matches Z3's level-parameterized assertion in updt_solver_with_lemmas.
            if *max_level < check_level {
                continue;
            }
            if let Some(applied) = self.apply_to_args(pred, lemma, head_args) {
                conjuncts.push(applied);
            }
        }
        if conjuncts.is_empty() {
            ChcExpr::Bool(true)
        } else {
            ChcExpr::and_all(conjuncts)
        }
    }

    /// Current number of queued obligations (heap + deque).
    fn obligation_queue_size(&self) -> usize {
        self.obligations.heap.len() + self.obligations.deque.len()
    }

    /// Maximum queue size: 2x max_obligations.
    /// Prevents unbounded memory growth from POB explosion (#2956 Finding 5).
    fn obligation_queue_cap(&self) -> usize {
        self.config.max_obligations.saturating_mul(2)
    }

    /// Push a proof obligation to the queue.
    /// Assigns a monotonic queue_id for deterministic tie-breaking.
    /// Drops the POB if the queue is at capacity and marks this strengthen
    /// attempt as incomplete (must degrade to Unknown).
    pub(in crate::pdr::solver) fn push_obligation(&mut self, mut pob: ProofObligation) {
        let cap = self.obligation_queue_cap();
        if self.obligation_queue_size() >= cap {
            // MAY pobs are best-effort auxiliary work (GSpacer global
            // guidance): dropping one keeps must-pob exploration complete,
            // so it must not set the overflow degradation flag.
            if pob.is_may() {
                return;
            }
            if self.config.verbose && !self.obligations.overflowed {
                safe_eprintln!(
                    "PDR: obligation queue overflow at cap {}; degrading result to Unknown",
                    cap
                );
            }
            self.obligations.overflowed = true;
            return;
        }
        pob.queue_id = self.obligations.next_id;
        self.obligations.next_id += 1;
        if self.config.use_level_priority {
            self.obligations.heap.push(PriorityPob(pob));
        } else {
            self.obligations.deque.push_back(pob);
        }
    }

    /// Push a proof obligation with high priority (for DFS: to front).
    /// Assigns a monotonic queue_id for deterministic tie-breaking.
    /// Drops the POB if the queue is at capacity and marks this strengthen
    /// attempt as incomplete (must degrade to Unknown).
    pub(in crate::pdr::solver) fn push_obligation_front(&mut self, mut pob: ProofObligation) {
        let cap = self.obligation_queue_cap();
        if self.obligation_queue_size() >= cap {
            // MAY pobs: drop silently without degrading (see push_obligation).
            if pob.is_may() {
                return;
            }
            if self.config.verbose && !self.obligations.overflowed {
                safe_eprintln!(
                    "PDR: obligation queue overflow at cap {}; degrading result to Unknown",
                    cap
                );
            }
            self.obligations.overflowed = true;
            return;
        }
        pob.queue_id = self.obligations.next_id;
        self.obligations.next_id += 1;
        if self.config.use_level_priority {
            // In level-priority mode, all POBs go to the heap (level determines order)
            self.obligations.heap.push(PriorityPob(pob));
        } else {
            self.obligations.deque.push_front(pob);
        }
    }

    /// Pop the next proof obligation
    pub(in crate::pdr::solver) fn pop_obligation(&mut self) -> Option<ProofObligation> {
        if self.config.use_level_priority {
            self.obligations.heap.pop().map(|p| p.0)
        } else {
            self.obligations.deque.pop_front()
        }
    }

    pub(in crate::pdr) fn canonical_vars(&self, pred: PredicateId) -> Option<&[ChcVar]> {
        self.caches.predicate_vars.get(&pred).map(Vec::as_slice)
    }

    // ========================================================================
    // SCC-based cyclic predicate strengthening
    // ========================================================================

    /// Translate a lemma from one predicate's canonical vars to another's.
    /// Returns None if predicates have different arities.
    ///
    /// ay uses canonical variables named `__p{pred_idx}_a{arg_idx}`. Translation
    /// builds a substitution from source vars to target vars.
    pub(in crate::pdr::solver) fn translate_lemma(
        &self,
        lemma: &ChcExpr,
        from_pred: PredicateId,
        to_pred: PredicateId,
    ) -> Option<ChcExpr> {
        let from_vars = self.canonical_vars(from_pred)?;
        let to_vars = self.canonical_vars(to_pred)?;

        if from_vars.len() != to_vars.len() {
            return None; // Different arity - can't translate
        }

        // Build substitution: __p{from}_a{i} -> __p{to}_a{i}
        let subst: Vec<(ChcVar, ChcExpr)> = from_vars
            .iter()
            .zip(to_vars.iter())
            .map(|(f, t)| (f.clone(), ChcExpr::var(t.clone())))
            .collect();

        Some(lemma.substitute(&subst))
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "../core_tests/mod.rs"]
mod tests;
