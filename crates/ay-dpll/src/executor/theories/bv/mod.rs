// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unified BV solve pipeline (eager bit-blasting) for all BV logics (#6691).
//!
//! All BV logic variants (QF_BV, QF_ABV, QF_UFBV, QF_AUFBV) and modes
//! (single-shot, incremental push/pop) enter through `solve_bv_core_inner`.
//! The `BvSolveConfig` parameterizes features (preprocessing, array axioms,
//! UF congruence, incremental state management) so the pipeline phases are
//! written once. Shared helpers (`propagate_bv_unknown_reason`,
//! `finalize_bv_unsat`, `finalize_bv_unknown`, `save_bv_unsat_proof_state`)
//! are used by both the fresh and persistent code paths.
//!
//! Model extraction lives in `bv_model.rs`, axiom generation in
//! `bv_axioms_array.rs` and `bv_axioms_euf.rs`.
//! Configuration in `bv_config.rs`.

use ay_core::time::Instant;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Condvar, Mutex};

// #8529: Use deterministic hash maps in all builds.
use ay_bv::{BvSolver, BvValidationError};
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, TermData};
use ay_core::{Sort, TermId, TermStore, Tseitin, TseitinResult};
use ay_sat::{
    AssumeResult, BranchHeuristic, ClauseTrace, Literal as SatLiteral, ProofOutput, SatResult,
    Solver as SatSolver, Variable as SatVariable,
};

use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::preprocess::{Preprocessor, VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT};

use super::super::Executor;
use super::bv_cnf_dump;
use super::bv_encoding;
use super::euf::ArrayAxiomMode;
use super::{debug_ite_conditions_enabled, debug_preprocessed_enabled};

// Re-export so existing `use super::bv::BvSolveConfig` paths continue to work.
pub(in crate::executor) use super::bv_config::BvSolveConfig;

struct BvSatDeadlineGuard(Option<(Arc<(Mutex<bool>, Condvar)>, std::thread::JoinHandle<()>)>);

impl Drop for BvSatDeadlineGuard {
    fn drop(&mut self) {
        if let Some((stop, handle)) = self.0.take() {
            let (lock, cvar) = &*stop;
            if let Ok(mut stopped) = lock.lock() {
                *stopped = true;
                cvar.notify_one();
            }
            let _ = handle.join();
        }
    }
}

fn install_bv_sat_interrupt(
    solver: &mut SatSolver,
    external_interrupt: Option<Arc<AtomicBool>>,
    solve_deadline: Option<Instant>,
) -> BvSatDeadlineGuard {
    let sat_deadline_interrupt_flag = solve_deadline.map(|_| {
        Arc::new(AtomicBool::new(
            external_interrupt
                .as_ref()
                .is_some_and(|flag| flag.load(Ordering::Relaxed)),
        ))
    });
    let sat_interrupt_flag = sat_deadline_interrupt_flag
        .clone()
        .or_else(|| external_interrupt.clone());
    if let Some(ref flag) = sat_interrupt_flag {
        solver.set_interrupt(flag.clone());
    }

    // Spawn a cancellable deadline timer thread if needed (#8554). The timer
    // writes only to the SAT-local deadline flag, never to the caller's API
    // interrupt flag (#8961).
    let deadline_guard = if let (Some(deadline), Some(flag)) =
        (solve_deadline, sat_deadline_interrupt_flag.as_ref())
    {
        let now = Instant::now();
        if now < deadline {
            #[cfg(not(target_arch = "wasm32"))]
            {
                let flag = flag.clone();
                let stop = Arc::new((Mutex::new(false), Condvar::new()));
                let stop_clone = Arc::clone(&stop);
                let remaining = deadline - now;
                let handle = std::thread::spawn(move || {
                    let (lock, cvar) = &*stop_clone;
                    let guard = lock.lock().expect("deadline timer mutex poisoned");
                    let (guard, _) = cvar
                        .wait_timeout_while(guard, remaining, |stopped| !*stopped)
                        .expect("deadline timer condvar wait failed");
                    if !*guard {
                        flag.store(true, Ordering::Relaxed);
                    }
                });
                Some((stop, handle))
            }
            // wasm32 has no threads: the deadline is still honored by the inline
            // `Instant::now() >= deadline` checks on the solve path (which use the
            // ay-core clock shim), so no timer thread is needed here.
            #[cfg(target_arch = "wasm32")]
            {
                let _ = flag;
                None
            }
        } else {
            flag.store(true, Ordering::Relaxed);
            None
        }
    } else {
        None
    };
    BvSatDeadlineGuard(deadline_guard)
}

const ABV_LARGE_STABLE_RESTART_MIN_VARS: usize = 500_000;
const ABV_LARGE_STABLE_RESTART_MIN_CLAUSES: usize = 1_000_000;
const ABV_LARGE_STABLE_RESTART_PHASE_CONFLICTS: u64 = 4_096;

/// Resolve the effective learned-clause-DB byte cap for this solve.
///
/// Precedence: the `AY_CLAUSE_DB_MB` env override (`0` = uncapped) wins, for
/// manual memory tuning of a pathological instance; else the explicit API/CLI
/// limit; else `None` (unbounded) — today's default behavior.
///
/// NOTE (measured): on the 20M-var model-checker-consumer `state_always_valid` instance a
/// 12 GiB learned-clause cap left peak RSS byte-identical (~41.9 GB) and solve
/// time unchanged — that instance's peak is the eager bit-blasted CNF + term
/// store, reached independent of learned-clause growth, so no learned-clause
/// cap moves it. The knob is retained for instances whose learned DB IS the
/// bottleneck; there is deliberately no size-based auto-default, so an
/// unvalidated instance class is never silently reconfigured.
fn resolve_clause_db_bytes_limit(explicit: Option<usize>, _total_vars: u32) -> Option<usize> {
    if let Some(raw) = std::env::var_os("AY_CLAUSE_DB_MB") {
        if let Some(mb) = raw.to_str().and_then(|s| s.trim().parse::<usize>().ok()) {
            return if mb == 0 {
                None
            } else {
                Some(mb.saturating_mul(1024 * 1024))
            };
        }
    }
    explicit
}

fn should_extend_large_abv_stable_restart_phase(
    total_vars: usize,
    total_clauses: usize,
    array_axioms: bool,
) -> bool {
    array_axioms
        && total_vars >= ABV_LARGE_STABLE_RESTART_MIN_VARS
        && total_clauses >= ABV_LARGE_STABLE_RESTART_MIN_CLAUSES
}

fn configure_ephemeral_bv_sat_solver(
    solver: &mut SatSolver,
    total_vars: usize,
    total_clauses: usize,
    array_axioms: bool,
) {
    let large_array_bitblast =
        should_extend_large_abv_stable_restart_phase(total_vars, total_clauses, array_axioms);
    // BV theory queries are one-shot bit-blasted SAT instances. SAT
    // preprocessing and restart-time inprocessing cannot amortize across
    // queries here; on large QF_ABV encodings, probing/vivification can spend
    // the whole timeout before the theory result is known.
    //
    // Experiment knob (#dt-array-fc-lazy): a huge Tseitin bit-blast (20M+ vars)
    // benefits from a ONE-SHOT bounded preprocessing pass that collapses
    // definitional vars (like z3's bit-blaster). `AY_BV_PREPROCESS=quick` runs
    // the CHEAP passes (BVE/subsumption) but skips the expensive HTR/probing
    // that motivated disabling preprocessing here (they are gated by
    // preprocessing_quick_mode and bounded by preprocess_timed_out()).
    // `=full` also runs the expensive passes. Default (unset) preserves the
    // no-preprocessing behavior exactly.
    match std::env::var("AY_BV_PREPROCESS").ok().as_deref() {
        Some("quick") => {
            solver.set_preprocess_enabled(true);
            solver.set_full_preprocessing(false);
        }
        Some("full") => {
            solver.set_preprocess_enabled(true);
            solver.set_full_preprocessing(true);
        }
        _ => {
            solver.set_preprocess_enabled(false);
        }
    }
    solver.disable_all_inprocessing();
    solver.set_congruence_enabled(false);
    solver.set_condition_enabled(false);
    solver.set_shrink_enabled(false);
    if !large_array_bitblast {
        solver.set_branch_heuristic(BranchHeuristic::Vmtf);
    }
    if total_vars > 50_000 {
        solver.set_reorder_enabled(false);
    }
    if large_array_bitblast {
        // Large array-BV bit-blasts can start in stable mode, hit the default
        // 1000-conflict phase boundary, and switch to focused mode before the
        // first reluctant stable restart at 1024 conflicts. Keep that initial
        // stable-biased phase long enough to exercise restart search on tails,
        // and keep legacy-coupled branching so stable mode uses EVSIDS.
        solver.set_stable_phase_init(ABV_LARGE_STABLE_RESTART_PHASE_CONFLICTS);
    }
}

#[cfg(test)]
mod deadline_interrupt_tests {
    use super::*;
    use ay_sat::BranchSelectorMode;

    #[test]
    fn bv_sat_deadline_does_not_poison_external_interrupt_8961() {
        let external_interrupt = Arc::new(AtomicBool::new(false));
        let mut solver = SatSolver::new(1);

        let _guard = install_bv_sat_interrupt(
            &mut solver,
            Some(external_interrupt.clone()),
            Some(Instant::now()),
        );

        assert!(
            !external_interrupt.load(Ordering::Relaxed),
            "BV SAT deadline timer must not set the reusable API interrupt flag"
        );
    }

    #[test]
    fn ephemeral_bv_sat_solver_disables_restart_inprocessing_11936() {
        let mut solver = SatSolver::new(100_000);
        configure_ephemeral_bv_sat_solver(&mut solver, 100_000, 100_000, false);
        let profile = solver.inprocessing_feature_profile();

        assert!(!profile.preprocess);
        assert!(!profile.shrink);
        assert!(!profile.probe);
        assert!(!profile.vivify);
        assert!(!profile.subsume);
        assert!(!profile.condition);
        assert!(!profile.congruence);
        assert!(!profile.reorder);
        assert_eq!(solver.active_branch_heuristic(), BranchHeuristic::Vmtf);
        assert_eq!(
            solver.branch_selector_mode(),
            BranchSelectorMode::Fixed(BranchHeuristic::Vmtf)
        );
    }

    #[test]
    fn large_abv_stable_restart_phase_requires_large_array_bitblast_8140() {
        assert!(should_extend_large_abv_stable_restart_phase(
            ABV_LARGE_STABLE_RESTART_MIN_VARS,
            ABV_LARGE_STABLE_RESTART_MIN_CLAUSES,
            true,
        ));
        assert!(!should_extend_large_abv_stable_restart_phase(
            ABV_LARGE_STABLE_RESTART_MIN_VARS - 1,
            ABV_LARGE_STABLE_RESTART_MIN_CLAUSES,
            true,
        ));
        assert!(!should_extend_large_abv_stable_restart_phase(
            ABV_LARGE_STABLE_RESTART_MIN_VARS,
            ABV_LARGE_STABLE_RESTART_MIN_CLAUSES - 1,
            true,
        ));
        assert!(!should_extend_large_abv_stable_restart_phase(
            ABV_LARGE_STABLE_RESTART_MIN_VARS,
            ABV_LARGE_STABLE_RESTART_MIN_CLAUSES,
            false,
        ));
    }

    #[test]
    fn large_abv_ephemeral_solver_keeps_stable_focused_branch_coupling_8140() {
        let mut solver = SatSolver::new(ABV_LARGE_STABLE_RESTART_MIN_VARS);

        configure_ephemeral_bv_sat_solver(
            &mut solver,
            ABV_LARGE_STABLE_RESTART_MIN_VARS,
            ABV_LARGE_STABLE_RESTART_MIN_CLAUSES,
            true,
        );

        assert_eq!(
            solver.branch_selector_mode(),
            BranchSelectorMode::LegacyCoupled
        );
    }
}

#[cfg(test)]
mod restored_coverage_tests {
    use super::*;

    #[test]
    fn restored_bv_coverage_uses_sources_not_positions_9732() {
        let original_a = TermId::new(1);
        let original_b = TermId::new(2);
        let coverage_covered = vec![true, false];
        let coverage_source_sets = vec![vec![original_b], vec![original_a]];
        let mut restored = HashSet::default();

        Executor::add_restored_bv_coverage_from_sources(
            &TermStore::new(),
            &mut restored,
            &coverage_covered,
            Some(&coverage_source_sets),
        );

        assert!(
            !restored.contains(&original_a),
            "same-length coverage must not delegate by original/root position"
        );
        assert!(
            restored.contains(&original_b),
            "covered produced root should delegate its recorded source"
        );
    }

    #[test]
    fn restored_bv_coverage_requires_all_split_roots_9732() {
        let original = TermId::new(1);
        let other = TermId::new(2);
        let coverage_covered = vec![true, false, true];
        let coverage_source_sets = vec![vec![original], vec![original], vec![other]];
        let mut restored = HashSet::default();

        Executor::add_restored_bv_coverage_from_sources(
            &TermStore::new(),
            &mut restored,
            &coverage_covered,
            Some(&coverage_source_sets),
        );

        assert!(
            !restored.contains(&original),
            "split original should delegate only when every produced root is covered"
        );
        assert!(restored.contains(&other));
    }

    #[test]
    fn restored_bv_coverage_all_covered_empty_source_is_not_blanket_9732() {
        let original_a = TermId::new(1);
        let original_b = TermId::new(2);
        let coverage_covered = vec![true, true];
        let coverage_source_sets = vec![vec![original_b], vec![]];
        let mut restored = HashSet::default();

        Executor::add_restored_bv_coverage_from_sources(
            &TermStore::new(),
            &mut restored,
            &coverage_covered,
            Some(&coverage_source_sets),
        );

        assert!(
            !restored.contains(&original_a),
            "all current roots covered must not delegate an unrelated original"
        );
        assert!(restored.contains(&original_b));
    }

    #[test]
    fn restored_bv_coverage_missing_sources_fails_closed_9732() {
        let coverage_covered = vec![true, true];
        let mut restored = HashSet::default();

        let (_source_mapped_assertions, _split_source_assertions, source_sets_valid) =
            Executor::add_restored_bv_coverage_from_sources(
                &TermStore::new(),
                &mut restored,
                &coverage_covered,
                None,
            );

        assert!(
            !source_sets_valid,
            "missing provenance must not be treated as valid restored coverage"
        );
        assert!(
            restored.is_empty(),
            "missing provenance must fail closed instead of delegating all covered roots"
        );
    }

    #[test]
    fn restored_bv_coverage_handles_duplicate_sources_9732() {
        let original_a = TermId::new(1);
        let original_b = TermId::new(2);
        let coverage_covered = vec![true, false, true];
        let coverage_source_sets = vec![
            vec![original_a, original_a],
            vec![original_a],
            vec![original_b, original_b],
        ];
        let mut restored = HashSet::default();

        Executor::add_restored_bv_coverage_from_sources(
            &TermStore::new(),
            &mut restored,
            &coverage_covered,
            Some(&coverage_source_sets),
        );

        assert!(
            !restored.contains(&original_a),
            "duplicate source entries must not hide an uncovered produced root"
        );
        assert!(restored.contains(&original_b));
    }

    #[test]
    fn restored_bv_coverage_delegates_fully_covered_split_9732() {
        let original = TermId::new(1);
        let coverage_covered = vec![true, true];
        let coverage_source_sets = vec![vec![original], vec![original]];
        let mut restored = HashSet::default();

        Executor::add_restored_bv_coverage_from_sources(
            &TermStore::new(),
            &mut restored,
            &coverage_covered,
            Some(&coverage_source_sets),
        );

        assert!(
            restored.contains(&original),
            "split original should delegate once every produced root is covered"
        );
    }

    #[test]
    fn restored_bv_coverage_mismatch_fails_closed_9732() {
        let original = TermId::new(1);
        let coverage_covered = vec![true, false];
        let coverage_source_sets = vec![vec![original]];
        let mut restored = HashSet::default();

        let (source_mapped_assertions, _split_source_assertions, source_sets_valid) =
            Executor::add_restored_bv_coverage_from_sources(
                &TermStore::new(),
                &mut restored,
                &coverage_covered,
                Some(&coverage_source_sets),
            );

        assert!(
            !source_sets_valid,
            "release builds must detect coverage/source length mismatches"
        );
        assert!(
            source_mapped_assertions.contains(&original),
            "seen sources should suppress rewritten-root fallback on mismatch"
        );
        assert!(
            restored.is_empty(),
            "mismatched provenance must not delegate restored assertions"
        );
    }
}

impl Executor {
    // Model extraction (extract_bv_model_from_bits) is in bv_model.rs.
    // Array axiom generation is in bv_axioms_array.rs.
    // EUF congruence axiom generation is in bv_axioms_euf.rs.

    fn preprocessed_bv_assertion_covered(
        terms: &TermStore,
        assertion: TermId,
        tseitin_result: &TseitinResult,
        sat_model: &[bool],
    ) -> bool {
        if matches!(terms.get(assertion), TermData::Const(Constant::Bool(true))) {
            return true;
        }
        tseitin_result
            .term_to_var
            .get(&assertion)
            .and_then(|&dimacs_var| sat_model.get((dimacs_var - 1) as usize))
            .copied()
            .unwrap_or(false)
    }

    fn sat_model_lit_assigned_true(sat_model: &[bool], dimacs_lit: i32) -> bool {
        if dimacs_lit == 0 {
            return false;
        }
        let Some(value) = sat_model
            .get(dimacs_lit.unsigned_abs().saturating_sub(1) as usize)
            .copied()
        else {
            return false;
        };
        if dimacs_lit > 0 {
            value
        } else {
            !value
        }
    }

    fn bv_assertion_covered(
        terms: &TermStore,
        assertion: TermId,
        tseitin_result: &TseitinResult,
        bv_predicate_to_var: &HashMap<TermId, i32>,
        bv_bool_to_var: &HashMap<TermId, i32>,
        var_offset: i32,
        sat_model: &[bool],
    ) -> bool {
        if Self::preprocessed_bv_assertion_covered(terms, assertion, tseitin_result, sat_model) {
            return true;
        }

        let (bv_assertion, positive) = match terms.get(assertion) {
            TermData::Not(inner) => (*inner, false),
            TermData::App(sym, args) if sym.name() == "not" && args.len() == 1 => (args[0], false),
            _ => (assertion, true),
        };

        let bitblast_lit = bv_predicate_to_var
            .get(&bv_assertion)
            .or_else(|| bv_bool_to_var.get(&bv_assertion));
        bitblast_lit.is_some_and(|&lit| {
            let lit = if positive { lit } else { -lit };
            Self::sat_model_lit_assigned_true(
                sat_model,
                bv_encoding::offset_cnf_lit(lit, var_offset),
            )
        })
    }

    fn add_restored_bv_coverage_from_sources(
        terms: &TermStore,
        restored_assertions_covered_by_bv: &mut HashSet<TermId>,
        coverage_covered: &[bool],
        coverage_source_sets: Option<&[Vec<TermId>]>,
    ) -> (HashSet<TermId>, HashSet<TermId>, bool) {
        let mut source_mapped_assertions = HashSet::default();
        let mut source_counts: HashMap<TermId, usize> = HashMap::default();
        let Some(coverage_source_sets) = coverage_source_sets else {
            return (source_mapped_assertions, HashSet::default(), false);
        };
        for source_set in coverage_source_sets {
            for &source in source_set {
                source_mapped_assertions.insert(source);
                *source_counts.entry(source).or_default() += 1;
            }
        }
        let split_source_assertions = source_counts
            .into_iter()
            .filter_map(|(source, count)| (count > 1).then_some(source))
            .collect();
        if coverage_covered.len() != coverage_source_sets.len() {
            return (source_mapped_assertions, split_source_assertions, false);
        }

        let mut source_fully_covered: HashMap<TermId, bool> = HashMap::default();
        for (&covered, source_set) in coverage_covered.iter().zip(coverage_source_sets.iter()) {
            for &source in source_set {
                if source.index() < terms.len()
                    && matches!(
                        terms.get(source),
                        TermData::Forall(..) | TermData::Exists(..)
                    )
                {
                    continue;
                }
                source_fully_covered
                    .entry(source)
                    .and_modify(|fully_covered| *fully_covered &= covered)
                    .or_insert(covered);
            }
        }
        restored_assertions_covered_by_bv.extend(
            source_fully_covered
                .into_iter()
                .filter_map(|(source, fully_covered)| fully_covered.then_some(source)),
        );
        (source_mapped_assertions, split_source_assertions, true)
    }

    fn add_delegated_validation_conjuncts(
        terms: &TermStore,
        delegated_assertions: &mut HashSet<TermId>,
    ) {
        let roots: Vec<TermId> = delegated_assertions.iter().copied().collect();
        for root in roots {
            Self::add_top_level_and_leaves(terms, root, delegated_assertions);
        }
    }

    fn add_top_level_and_leaves(
        terms: &TermStore,
        assertion: TermId,
        delegated_assertions: &mut HashSet<TermId>,
    ) {
        match terms.get(assertion) {
            TermData::App(sym, args) if sym.name() == "and" => {
                for &arg in args {
                    Self::add_top_level_and_leaves(terms, arg, delegated_assertions);
                }
            }
            _ => {
                delegated_assertions.insert(assertion);
            }
        }
    }

    /// Solve using Bitvector theory (eager bit-blasting).
    /// Dispatcher for QF_BV — delegates to `solve_bv_core` with QF_BV config.
    /// In incremental mode (push/pop), uses `qf_bv_incremental` config which
    /// activates persistent SAT solver and cached Tseitin/BV state.
    pub(in crate::executor) fn solve_bv(&mut self) -> Result<SolveResult> {
        if self.incremental_mode {
            return self.solve_bv_core(BvSolveConfig::qf_bv_incremental(), &[]);
        }
        self.solve_bv_core(BvSolveConfig::qf_bv(), &[])
    }

    /// Solve QF_ABV (Arrays + Bitvectors) using eager bit-blasting with array axioms
    pub(in crate::executor) fn solve_abv(&mut self) -> Result<SolveResult> {
        if self.incremental_mode {
            return self.solve_bv_core(BvSolveConfig::qf_abv_incremental(), &[]);
        }
        self.solve_bv_core(BvSolveConfig::qf_abv(), &[])
    }

    /// Solve QF_UFBV (UF + Bitvectors) using eager bit-blasting with UF congruence
    pub(in crate::executor) fn solve_ufbv(&mut self) -> Result<SolveResult> {
        if self.incremental_mode {
            return self.solve_bv_core(BvSolveConfig::qf_ufbv_incremental(), &[]);
        }
        self.solve_bv_core(BvSolveConfig::qf_ufbv(), &[])
    }

    /// Solve QF_AUFBV (Arrays + UF + Bitvectors) using eager bit-blasting
    /// with array and EUF congruence axioms
    pub(in crate::executor) fn solve_aufbv(&mut self) -> Result<SolveResult> {
        if self.incremental_mode {
            return self.solve_bv_core(BvSolveConfig::qf_aufbv_incremental(), &[]);
        }
        self.solve_bv_core(BvSolveConfig::qf_aufbv(), &[])
    }

    /// Shared BV solve pipeline. ALL BV logic variants route through this
    /// function: QF_BV, QF_ABV, QF_UFBV, QF_AUFBV (non-incremental), and
    /// QF_BV incremental (push/pop). Configuration via `BvSolveConfig`.
    pub(in crate::executor) fn solve_bv_core(
        &mut self,
        config: BvSolveConfig,
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        self.solve_bv_core_inner(config, assumptions, &[])
    }

    /// BV solve pipeline with extra root terms for assumption-aware array
    /// axiom generation (#6736). In incremental mode, assumption terms are
    /// not in `self.ctx.assertions` and would be excluded from the reachable
    /// set that scopes axiom generation. This variant includes
    /// `assumption_roots` so array operations appearing only in assumptions
    /// get proper axioms.
    pub(in crate::executor) fn solve_bv_core_with_assumption_roots(
        &mut self,
        config: BvSolveConfig,
        assumptions: &[TermId],
        assumption_roots: &[TermId],
    ) -> Result<SolveResult> {
        self.solve_bv_core_inner(config, assumptions, assumption_roots)
    }

    fn solve_bv_core_inner(
        &mut self,
        mut config: BvSolveConfig,
        assumptions: &[TermId],
        assumption_roots: &[TermId],
    ) -> Result<SolveResult> {
        // Certificate export is deliberately a fresh, eager per-check mode.
        // The persistent incremental solver does not expose a lossless snapshot
        // of active scoped/global clauses, and delayed BV operations add clauses
        // after the first SAT call.  Re-encoding the currently active assertion
        // vector here avoids both omissions while preserving normal fast paths
        // when no dump was requested.
        let export_bv_cnf = bv_cnf_dump::enabled();
        if export_bv_cnf {
            if config.theory_tag != "BV" {
                return Err(crate::executor_types::ExecutorError::ArtifactExport(
                    format!(
                        "--dump-bv-cnf supports pure QF_BV only; {} has post-encoding theory refinements",
                        config.theory_tag
                    ),
                ));
            }
            config.incremental = false;
        }

        // Early exit if already timed out or interrupted (#3070).
        // Without this, the entire encoding pipeline (Tseitin, bitblasting,
        // axiom generation) runs to completion even when the deadline has
        // already passed, causing deductive-checks to hang on wide BV queries.
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        // #abv-subst-model-retry: the single reactive re-solve after a
        // substitution-recovery model rejection runs with preprocessing
        // disabled, so the model is built directly from the bit-blasted
        // original assertions (no VariableSubstitution, no recovery).
        if self.bv_subst_retry_disable_preprocess {
            config.preprocess = false;
        }

        // Env-gated phase timing (`AY_PHASE_TRACE=1`): one stderr line per phase
        // boundary with elapsed seconds since this solve entered. Zero cost when
        // the env var is absent. Diagnostic-only (`c ...` comment lines), so it
        // cannot perturb transcript parsing or the verdict.
        let phase_trace_start = std::env::var_os("AY_PHASE_TRACE")
            .is_some()
            .then(Instant::now);
        macro_rules! phase_trace {
            ($name:expr) => {
                if let Some(t0) = phase_trace_start {
                    eprintln!(
                        "c phase-trace {} t={:.1}s",
                        $name,
                        t0.elapsed().as_secs_f64()
                    );
                }
            };
        }

        // --- Phase 0: Optional preprocessing (#8140) ---
        phase_trace!("phase0-preprocess");
        // When both preprocessing and array axioms are enabled (QF_ABV), run
        // preprocessing BEFORE array axiom generation. This ensures the array
        // axiom fixpoint operates on post-substitution terms, avoiding stale
        // term ID references that previously caused regressions.
        //
        // For pure BV (no array axioms), preprocessing runs in Phase 2 as before.
        //
        // Preprocessing MUST be disabled when assumptions are present (#5581):
        // VariableSubstitution and PropagateValues can eliminate the relationship
        // between assumption terms and the formula. For example, `(= p (= x #x00))`
        // with `(= x #xFF)` can be simplified away, disconnecting the assumption
        // literal `p` from the BV encoding. The Tseitin variable for `p` then has
        // no clauses connecting it to the rest of the formula, allowing the SAT
        // solver to assign it freely and produce a wrong-SAT result.
        let early_preprocess = config.preprocess && config.array_axioms && assumptions.is_empty();
        let mut current_assertion_source_sets: Option<Vec<Vec<TermId>>> = None;
        let original_assertions_before_early_preprocess = if early_preprocess {
            let original_assertions = self.ctx.assertions.clone();
            let mut source_sets: Vec<Vec<TermId>> = original_assertions
                .iter()
                .map(|&assertion| vec![assertion])
                .collect();
            phase_trace!("phase0.pre-bvand-flatten");
            self.flatten_bv1_bvand_assertions_with_sources(&mut source_sets);
            phase_trace!("phase0.pre-packed-mux");
            if !self.produce_proofs_enabled() {
                let derived = self.add_packed_mux_output_select_equalities_for_preprocess();
                if derived > 0 {
                    source_sets.resize(self.ctx.assertions.len(), Vec::new());
                    self.last_statistics.set_int(
                        "smt.abv.packed_mux.derived_select_equalities",
                        derived as u64,
                    );
                }
            }
            current_assertion_source_sets = Some(source_sets);
            Some(original_assertions)
        } else {
            None
        };
        let var_subst = if early_preprocess {
            phase_trace!("phase0.count-array-ops");
            let mut preprocessed = self.ctx.assertions.clone();
            let mut preprocessed_source_sets = current_assertion_source_sets
                .clone()
                .expect("early preprocess source sets initialized");
            let (mut preprocessor, var_subst) = Preprocessor::new_with_subst();
            let (initial_num_selects, initial_num_stores) =
                self.count_array_op_occurrences_in_assertions();
            self.last_statistics.set_int(
                "smt.abv.variable_subst.scalar_budget_input_selects",
                initial_num_selects as u64,
            );
            self.last_statistics.set_int(
                "smt.abv.variable_subst.scalar_budget_input_stores",
                initial_num_stores as u64,
            );
            if Self::should_budget_scalar_variable_substitution(
                initial_num_stores,
                initial_num_selects,
            ) {
                var_subst
                    .lock()
                    .expect("variable substitution mutex poisoned during ABV budget setup")
                    .set_scalar_replacement_node_limit(VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT);
                self.last_statistics
                    .set_int("smt.abv.variable_subst.scalar_budgeted", 1);
            } else {
                self.last_statistics
                    .set_int("smt.abv.variable_subst.scalar_budgeted", 0);
            }
            phase_trace!("phase0.preprocessor-loop");
            preprocessor.preprocess_with_sources(
                &mut self.ctx.terms,
                &mut preprocessed,
                &mut preprocessed_source_sets,
            );
            phase_trace!("phase0.preprocessor-loop-done");
            // Some ABV generators SSA-lower packed muxes through many one-bit
            // variables. The first preprocessing pass exposes those ITE/concat
            // structures; run the packed-mux alias detector once more before
            // bit-blasting, then re-run preprocessing so variable substitution
            // can collapse downstream BV users of the derived equality.
            std::mem::swap(&mut self.ctx.assertions, &mut preprocessed);
            current_assertion_source_sets = Some(preprocessed_source_sets);
            if !self.produce_proofs_enabled() {
                let derived = self.add_packed_mux_output_select_equalities_for_preprocess();
                if derived > 0 {
                    let source_sets = current_assertion_source_sets
                        .as_mut()
                        .expect("early preprocess source sets preserved");
                    source_sets.resize(self.ctx.assertions.len(), Vec::new());
                    let total = self
                        .last_statistics
                        .get_int("smt.abv.packed_mux.derived_select_equalities")
                        .unwrap_or(0)
                        + derived as u64;
                    self.last_statistics
                        .set_int("smt.abv.packed_mux.derived_select_equalities", total);
                    preprocessor.preprocess_with_sources(
                        &mut self.ctx.terms,
                        &mut self.ctx.assertions,
                        source_sets,
                    );
                }
            }
            if debug_preprocessed_enabled() {
                safe_eprintln!(
                    "[preprocess] assertions after preprocessing (early/ABV): {}",
                    self.ctx.assertions.len()
                );
                for (idx, &assertion) in self.ctx.assertions.iter().enumerate() {
                    safe_eprintln!("[preprocess] {}: {}", idx, self.format_term(assertion));
                }
            }
            // Swap assertions with preprocessed version so array axiom fixpoint
            // sees post-substitution terms. Original assertions are preserved for
            // restore/model validation; the flattened form is only an encoding aid.
            Some((
                var_subst,
                original_assertions_before_early_preprocess
                    .expect("early preprocess original assertions saved"),
            ))
        } else {
            None
        };

        // --- Phase 0a: BV1 bvand flattening ---
        phase_trace!("phase0a-bvand-flatten");
        // Flatten `(= #b1 (bvand t1 t2 ...))` into separate assertions.
        // The try3/try5 QF_ABV benchmarks encode their entire formula as a
        // single assertion with a giant bvand tree at BV1 width. Flattening
        // exposes individual constraints (including store equalities) for
        // the array axiom fixpoint and store-flat substitution to operate on.
        if config.array_axioms && !early_preprocess {
            self.flatten_bv1_bvand_assertions();
        }

        // Track the source-mapped primary roots separately from generated array
        // axioms. Array preprocessing appends ROW/FC roots and rewrites selects;
        // source sets must follow only the original prefix through those
        // same-length rewrites.
        let primary_formula_len = if config.array_axioms && var_subst.is_some() {
            Some(self.ctx.assertions.len())
        } else {
            None
        };
        let mut primary_formula_assertions = if config.array_axioms && var_subst.is_some() {
            Some(self.ctx.assertions.clone())
        } else {
            None
        };
        let primary_formula_assertion_source_sets = if config.array_axioms && var_subst.is_some() {
            current_assertion_source_sets.clone()
        } else {
            None
        };

        // --- Phase 0b: Array axiom fixpoint (if enabled) ---
        phase_trace!("phase0b-array-axioms");
        // Must run before Tseitin because it adds new assertion-level terms.
        // When preprocessing is enabled (QF_ABV), assertions are already
        // preprocessed at this point (#8140).
        if config.array_axioms {
            // Reify array-sorted equality atoms for UF arguments (#12).
            // When a UF takes whole-array arguments (e.g. `h(a)`, `h(b)`),
            // congruence `(= a b) → (= h(a) h(b))` requires the atom `(= a b)`
            // (and its negation) to exist BEFORE extensionality runs, so that:
            //   1. extensionality generates `(= a b) ∨ select(a,k) ≠ select(b,k)`,
            //      letting the array theory drive `(= a b)` true from a store
            //      no-op (`a = store(b, i, select a i)`, `select a i = select b i`);
            //   2. Tseitin internalizes `(= a b)`, giving the non-BV congruence
            //      generator a variable to build the `(args differ) ∨ (h(a)=h(b))`
            //      clause from.
            // Without the atom, `a = b` is only derivable inside the array layer,
            // never reaches the UF layer, and `(distinct (h a) (h b))` is wrongly
            // satisfiable (Nelson-Oppen sharing gap). The tautology
            // `(or (= a b) (not (= a b)))` adds no semantic constraint.
            // Must run before extensionality / finite-array axioms below.
            if config.uf_congruence || config.non_bv_congruence {
                let uf_eq_roots: Vec<TermId> = assumption_roots.to_vec();
                let reified = self.reify_array_uf_arg_equalities(&uf_eq_roots);
                if reified > 0 {
                    self.last_statistics
                        .set_int("smt.aufbv.array_uf_eq.reified", reified as u64);
                }
            }

            // Ensure negation terms exist for array equalities inside ITE
            // conditions. Without this, `add_array_extensionality_axioms` skips
            // array equalities used only as ITE conditions (no standalone
            // negation), leaving them unconstrained and causing unknown/wrong-SAT
            // on QF_ABV benchmarks with `(ite (= array1 array2) ...)` patterns.
            self.ensure_array_eq_ite_negations();
            self.add_array_extensionality_axioms();

            // Finite-domain extensionality for array equalities over a small
            // BitVec index domain. The single-Skolem extensionality axiom can
            // only witness a difference, never refute an equality that holds/
            // fails at a specific concrete index, which left QF_ABV equalities
            // involving `(as const ...)` / store-chains under-constrained
            // (wrong-SAT). Expanding the exact biconditional over all 2^w
            // indices makes them completely decided by the bit-blaster.
            self.add_finite_bv_array_extensionality();

            // Adaptive fixpoint gate: skip the array axiom fixpoint on formulas
            // where it would cause term explosion. The fixpoint loop creates
            // new selects via congruence axioms, compounding O(N^2) term growth.
            //
            // Gate: skip the fixpoint when the formula has too many selects
            // (> 80), since the O(selects^2) congruence axiom generation is
            // too expensive. For smaller formulas, the fixpoint runs with a
            // term budget (10K terms, #8140) that prevents runaway expansion
            // on deep store chains (bubble_sort, wchains). The budget is
            // enforced inside run_array_axiom_fixpoint_inner.
            //
            // When the fixpoint is skipped or bails on budget, the
            // expand_select_store pass and ROW axioms in
            // generate_array_bv_axioms provide sufficient array reasoning.
            // #8510: Count only selects that interact with stores (selects
            // on store-chain arrays or selects with symbolic indices). The
            // original gate threshold of 80 is hit by benchmarks with many
            // trivial constant-indexed selects on constant arrays (e.g.,
            // csplit-query QF_ABV benchmarks have 2000+ trivial selects but
            // only 8 complex ones). Skipping the fixpoint causes false SAT.
            let complex_selects = self.count_complex_array_selects_in_assertions();
            if complex_selects <= 80 {
                if assumption_roots.is_empty() {
                    if let Some(primary_formula_len) = primary_formula_len {
                        self.run_array_axiom_fixpoint_at(
                            primary_formula_len,
                            ArrayAxiomMode::EagerAll,
                        );
                    } else {
                        self.run_array_axiom_fixpoint_5();
                    }
                } else {
                    self.run_array_axiom_fixpoint_5_with_roots(assumption_roots);
                }
            }

            // Expand select(store(a, I, v), J) into ITE chains. This converts
            // remaining select-over-store patterns into boolean structure that
            // Tseitin + BV bitblasting encode directly, avoiding expensive
            // bit-level ROW axiom generation in generate_array_bv_axioms.
            // Concrete-distinct indices skip through without generating ITEs.
            // Z3 ref: array_rewriter.cpp:354-381.
            //
            // Adaptive ITE budget (#8140): use a higher symbolic ITE budget for
            // formulas with moderate store chain depth. For bubble_sort22-like
            // benchmarks, this resolves more store levels as ITEs at the term
            // level, dramatically reducing the clause count sent to the SAT
            // solver and avoiding the pathological L0 GC overhead on 4M+ clause
            // databases.
            let num_stores = self.count_array_stores_in_assertions();
            let num_selects = self.count_array_selects_in_assertions();
            self.last_statistics
                .set_int("smt.abv.select_store_expansion.stores", num_stores as u64);
            self.last_statistics
                .set_int("smt.abv.select_store_expansion.selects", num_selects as u64);
            self.ctx.assertions = self
                .ctx
                .terms
                .expand_select_store_all_adaptive(&self.ctx.assertions, num_stores);
            if let Some(primary_formula_len) = primary_formula_len {
                primary_formula_assertions =
                    Some(self.ctx.assertions[..primary_formula_len].to_vec());
            }
        }
        debug_assert_eq!(
            primary_formula_assertions.as_ref().map(Vec::len),
            primary_formula_assertion_source_sets.as_ref().map(Vec::len)
        );

        let mut array_axiom_extra_roots = assumption_roots.to_vec();
        if let Some((ref var_subst, _)) = var_subst {
            let substitutions = var_subst
                .lock()
                .expect("variable substitution mutex poisoned during BV extra-root collection");
            for &replacement in substitutions.substitutions().values() {
                array_axiom_extra_roots.push(replacement);
            }
            for &source in substitutions.substitution_sources().values() {
                array_axiom_extra_roots.push(source);
            }
        }
        if config.array_axioms {
            let row2_roots = self.materialize_array_row2_read_terms(&mut array_axiom_extra_roots);
            if row2_roots > 0 {
                self.last_statistics
                    .set_int("smt.abv.row2.materialized_read_terms", row2_roots as u64);
            }
        }

        // --- Phase 1: Proof setup ---
        phase_trace!("phase1-proof-setup");
        let proof_enabled = self.produce_proofs_enabled();
        if proof_enabled {
            self.proof_tracker.set_theory(config.theory_tag);
            for (idx, &assertion) in self.ctx.assertions.iter().enumerate() {
                let _ = self
                    .proof_tracker
                    .add_assumption(assertion, Some(format!("h{idx}")));
            }
        }

        // --- Incremental path: persistent SAT solver with push/pop scoping ---
        // When config.incremental is true, uses IncrementalBvState for cached
        // Tseitin/BvSolver/SatSolver state management. This path only encodes NEW
        // assertions incrementally and adds definitional clauses globally.
        if config.incremental {
            return self.solve_bv_incremental_inner(&config, proof_enabled);
        }

        // Interrupt check after array axiom fixpoint and proof setup (#3070).
        if self.should_abort_theory_loop() {
            if let Some((_, original)) = var_subst {
                self.ctx.assertions = original;
            }
            return Ok(SolveResult::Unknown);
        }

        // --- Phase 2: Optional preprocessing (pure BV without array axioms) ---
        phase_trace!("phase2-preprocess");
        // For combined theories (QF_ABV), preprocessing already ran in Phase 0.
        // This phase handles the pure BV case (no array axioms).
        let var_subst = if !early_preprocess && config.preprocess && assumptions.is_empty() {
            let mut preprocessed = self.ctx.assertions.clone();
            let mut preprocessed_source_sets: Vec<Vec<TermId>> = preprocessed
                .iter()
                .map(|&assertion| vec![assertion])
                .collect();
            let (mut preprocessor, var_subst) = Preprocessor::new_with_subst();
            preprocessor.preprocess_with_sources(
                &mut self.ctx.terms,
                &mut preprocessed,
                &mut preprocessed_source_sets,
            );
            if debug_preprocessed_enabled() {
                safe_eprintln!(
                    "[preprocess] assertions after preprocessing: {}",
                    preprocessed.len()
                );
                for (idx, &assertion) in preprocessed.iter().enumerate() {
                    safe_eprintln!("[preprocess] {}: {}", idx, self.format_term(assertion));
                }
            }
            if debug_ite_conditions_enabled() {
                use ay_core::kani_compat::DetHashMap as HashMap;
                let mut cond_terms: HashMap<String, Vec<(usize, TermId)>> = HashMap::default();
                for (idx, &assertion) in preprocessed.iter().enumerate() {
                    if let TermData::Ite(cond, _, _) = self.ctx.terms.get(assertion) {
                        let cond = *cond;
                        let cond_str = self.format_term(cond);
                        cond_terms.entry(cond_str).or_default().push((idx, cond));
                    }
                }
                for (cond_str, occurrences) in &cond_terms {
                    let ids: Vec<_> = occurrences.iter().map(|(_, id)| id.index()).collect();
                    let same = occurrences.iter().all(|(_, id)| *id == occurrences[0].1);
                    safe_eprintln!(
                        "[ite-cond] '{}': TermIds {:?}, unified={}",
                        cond_str,
                        ids,
                        same
                    );
                }
            }
            // Swap assertions with preprocessed version for Tseitin/bitblast.
            // Original assertions are preserved in `saved_assertions` and restored
            // at the end of the function for incremental mode, model verification,
            // and proof production.
            std::mem::swap(&mut self.ctx.assertions, &mut preprocessed);
            current_assertion_source_sets = Some(preprocessed_source_sets);
            Some((var_subst, preprocessed))
        } else {
            var_subst
        };
        // #abv-subst-model-retry: mark this check-sat as a substitution-
        // carrying BV-lane solve (Phase 0 ABV path or Phase 2 pure-BV path).
        // A model refutation from this solve (in-loop BV validation or the
        // independent gate) then arms the single preprocessing-free re-solve
        // in `check_sat_guarded`.
        if var_subst.is_some() {
            self.bv_subst_lane = true;
        }

        // --- Phase 3: Tseitin transformation (incremental API) ---
        phase_trace!("phase3-tseitin");
        // Use incremental Tseitin so we can encode assumptions without asserting
        // them as unit clauses. This ensures assumption terms (e.g., UF applications
        // in `distinct(f(x), f(y))`) get Tseitin variables assigned and are visible
        // to downstream axiom generation (EUF congruence, array axioms).
        let mut tseitin = Tseitin::new(&self.ctx.terms);
        for &assertion in &self.ctx.assertions {
            tseitin.assert_term(assertion);
        }

        // --- Phase 3b: Assumption handling ---
        // Encode assumption terms via Tseitin (without adding unit clauses) so they
        // get CNF variables. This fixes #5535: assumption terms not in assertions
        // were silently dropped because they had no Tseitin encoding.
        let has_assumptions = !assumptions.is_empty();
        let (sat_assumptions, assumption_to_term): (Vec<SatLiteral>, Vec<(SatLiteral, TermId)>) =
            if has_assumptions {
                let mut sat_assumps = Vec::new();
                let mut map = Vec::new();
                for &assumption in assumptions {
                    let (base_term, positive) = match self.ctx.terms.get(assumption) {
                        TermData::Not(inner) => (*inner, false),
                        _ => (assumption, true),
                    };
                    // Encode the base term to get/create its CNF variable
                    let cnf_lit = tseitin.encode(base_term, true);
                    let sat_var = SatVariable::new(cnf_lit.unsigned_abs() - 1);
                    let sat_lit = if (cnf_lit > 0) == positive {
                        SatLiteral::positive(sat_var)
                    } else {
                        SatLiteral::negative(sat_var)
                    };
                    sat_assumps.push(sat_lit);
                    map.push((sat_lit, assumption));
                }
                (sat_assumps, map)
            } else {
                (Vec::new(), Vec::new())
            };

        // Build TseitinResult from incremental state
        let tseitin_result = TseitinResult::new(
            tseitin.all_clauses().to_vec(),
            tseitin.term_to_var().clone(),
            tseitin.var_to_term().clone(),
            0, // Not used when clauses are added individually
            tseitin.num_vars(),
        );

        debug_assert!(
            self.ctx.assertions.is_empty() || !tseitin_result.clauses.is_empty(),
            "BUG: Tseitin produced 0 clauses from {} assertions in {}",
            self.ctx.assertions.len(),
            config.theory_tag
        );

        // Interrupt check before bitblasting (#3070). Wide BV multipliers
        // (64-bit) generate ~128K gates; bail out before that work if timed out.
        if self.should_abort_theory_loop() {
            if let Some((_, original)) = var_subst {
                self.ctx.assertions = original;
            }
            return Ok(SolveResult::Unknown);
        }

        // --- Phase 4: Bitblasting ---
        phase_trace!("phase4-bitblast");
        // Enable delayed internalization for non-incremental, non-assumption paths (#7015).
        // For expensive operations (mul/div/rem on wide BV with 2+ variable args),
        // the BvSolver allocates fresh unconstrained bits instead of building circuits.
        // After SAT solving, we check these against the model and add conflict clauses.
        //
        // For combined theories (#8142): delayed internalization IS enabled, but BV
        // terms that appear as array select/store indices, store values, or UF arguments
        // are marked as "eager" — they and their BV sub-expressions are always fully
        // bit-blasted. This ensures array/EUF axioms reason over constrained bits while
        // allowing bulk BV operations (e.g., data-path multiplications that don't feed
        // into indices) to remain delayed.
        let use_delayed =
            !config.incremental && assumptions.is_empty() && !proof_enabled && !export_bv_cnf;

        // Capture interrupt state before taking &self.ctx.terms borrow (#8609).
        // bv_solver holds an immutable borrow on self.ctx.terms, so we cannot
        // call self.should_abort_theory_loop() while bv_solver is alive.
        // Instead, capture the flag and deadline for local interrupt checking.
        let bv_interrupt_flag = self.solve_interrupt.clone();
        let bv_deadline = self.solve_deadline.clone();
        let bv_is_interrupted = || -> bool {
            if let Some(ref flag) = bv_interrupt_flag {
                if flag.load(Ordering::Relaxed) {
                    return true;
                }
            }
            bv_deadline.expired()
        };

        let mut bv_solver = BvSolver::new(&self.ctx.terms);
        // Wire the executor's interrupt flag into the BV solver so that
        // set_timeout() and interrupt() are respected during bitblasting (#8609).
        if let Some(ref flag) = bv_interrupt_flag {
            bv_solver.set_interrupt(flag.clone());
        }
        if use_delayed {
            bv_solver.set_delay_enabled(true);

            // For combined theories, collect terms that must be eagerly internalized.
            if config.array_axioms || config.uf_congruence {
                let eager_terms = self.collect_eager_bv_terms(&config, &array_axiom_extra_roots);
                if !eager_terms.is_empty() {
                    bv_solver.set_eager_terms(eager_terms);
                }
            }
        }
        let bv_clauses = bv_solver.bitblast_all(&self.ctx.assertions);

        // Interrupt / memory check after bitblasting (#8609). bitblast_all() now
        // checks the interrupt flag *and* the process memory ceiling periodically
        // and may return a partial result on either. A partial CNF can only ever
        // yield Unknown (never SAT/UNSAT), so bailing here is sound — it converts
        // an eager-blast memory blowup that would otherwise OOM-kill the process
        // into a graceful Unknown that respects the -memory budget.
        // Use local check (not should_abort_theory_loop) to avoid borrow conflict.
        if bv_is_interrupted() || ay_sys::process_memory_exceeded() {
            drop(bv_solver);
            if let Some((_, original)) = var_subst {
                self.ctx.assertions = original;
            }
            self.propagate_bv_unknown_reason(true);
            return Ok(SolveResult::Unknown);
        }

        if self.debug_ufbv && config.uf_congruence {
            safe_eprintln!("DEBUG: Tseitin num_vars = {}", tseitin_result.num_vars);
            safe_eprintln!(
                "DEBUG: BV num_vars (before linking) = {}",
                bv_solver.num_vars()
            );
            safe_eprintln!("DEBUG: Tseitin clauses = {}", tseitin_result.clauses.len());
            safe_eprintln!(
                "DEBUG: BV clauses (before offset) = {}",
                bv_solver.clauses().len()
            );
            for (term_id, bits) in bv_solver.iter_term_bits() {
                safe_eprintln!("DEBUG: Term {:?} has bits {:?}", term_id, bits);
            }
        }

        // --- Phase 5: Combine Tseitin + BV clauses ---
        phase_trace!("phase5-combine");
        let mut all_clauses = tseitin_result.clauses.clone();
        if phase_trace_start.is_some() {
            eprintln!("c phase-trace clauses.tseitin={}", all_clauses.len());
        }
        let var_offset = tseitin_result.num_vars as i32;
        bv_encoding::offset_and_push_clauses(bv_clauses, var_offset, &mut all_clauses);
        if phase_trace_start.is_some() {
            eprintln!("c phase-trace clauses.after-bitblast={}", all_clauses.len());
        }

        // Materialize BV bits for array terms (ABV/AUFBV only)
        if config.array_axioms {
            self.materialize_array_bv_terms(&mut bv_solver, &array_axiom_extra_roots);
            let extra = bv_solver.take_clauses();
            bv_encoding::offset_and_push_clauses(extra, var_offset, &mut all_clauses);
        }

        // Materialize single-literal encodings for Bool-sorted UF application
        // arguments BEFORE Tseitin↔BV linking (#boolarg-congruence): Bool args
        // have no BV bits, so both congruence generators dropped every
        // application pair containing one — congruence over Bool argument
        // positions was silently lost (wrong-SAT: 256 finite-domain instances
        // of `(= (BoolUnbox (BoolBox c)) c)` answered `sat`). Allocating the
        // literal here lets `build_linking_batch` bridge it to any Tseitin
        // variable for the same term, and the generators encode the argument
        // difference as a 1-bit XOR. The clauses `bitblast_bool` emits are
        // drained into the linking batch's extra BV clauses below.
        if config.uf_congruence || config.non_bv_congruence {
            for arg in self.collect_uf_bool_args(assumptions) {
                let _ = bv_solver.ensure_bool_literal(arg);
            }
        }

        // --- Phases 6-7: Predicate + Bool linking (#858, #5457) ---
        let mut linking_batch = bv_encoding::build_linking_batch(
            &tseitin_result.var_to_term,
            &mut bv_solver,
            var_offset,
            &self.ctx.terms,
            None,
        );
        linking_batch.push_equivalence_clauses(&mut all_clauses);
        let extra_bv_clauses = linking_batch.take_extra_bv_clauses();
        bv_encoding::offset_and_push_clauses(extra_bv_clauses, var_offset, &mut all_clauses);

        // --- Phase 8: BV equality congruence axioms (#1708, QF_BV only) ---
        if config.bv_eq_congruence {
            all_clauses.extend(bv_encoding::generate_bv_eq_congruence_clauses(
                &self.ctx.terms,
                &self.ctx.assertions,
                &bv_solver,
                var_offset,
            ));
        }

        // --- Phase 9: Theory-specific axiom generation ---
        phase_trace!("phase9-theory-axioms");
        if phase_trace_start.is_some() {
            eprintln!(
                "c phase-trace clauses.after-linking-congruence={}",
                all_clauses.len()
            );
        }

        // Materialize BV bits for UF application arguments (#5475).
        // Complex BV sub-expressions (e.g., bvadd(x, #x01)) inside UF calls
        // are opaque to the BV bitblaster and need explicit materialization
        // before congruence axiom generation.
        if config.uf_congruence {
            self.materialize_uf_arg_bv_terms(&mut bv_solver, assumptions);
            let extra = bv_solver.take_clauses();
            bv_encoding::offset_and_push_clauses(extra, var_offset, &mut all_clauses);
        }

        let bv_num_vars = bv_solver.num_vars();
        let mut running_offset = tseitin_result.num_vars + bv_num_vars;

        // Array axiom clauses (ABV/AUFBV)
        let _array_axiom_vars = if config.array_axioms {
            let array_axiom_result = self.generate_array_bv_axioms(
                &bv_solver,
                tseitin_result.num_vars,
                running_offset,
                &array_axiom_extra_roots,
                &tseitin_result.term_to_var,
            );
            for clause in array_axiom_result.clauses {
                all_clauses.push(clause);
            }
            if phase_trace_start.is_some() {
                eprintln!(
                    "c phase-trace clauses.after-array-axioms={}",
                    all_clauses.len()
                );
            }
            running_offset += array_axiom_result.num_vars;
            array_axiom_result.num_vars
        } else {
            0
        };

        // EUF congruence axiom clauses (UFBV/AUFBV)
        let _euf_axiom_vars = if config.uf_congruence {
            let euf_axiom_result = self.generate_euf_bv_axioms_debug(
                &bv_solver,
                tseitin_result.num_vars,
                running_offset,
                self.debug_ufbv,
                assumptions,
            );
            if self.debug_ufbv {
                safe_eprintln!("DEBUG: EUF axiom num_vars = {}", euf_axiom_result.num_vars);
                safe_eprintln!(
                    "DEBUG: EUF axiom clauses = {}",
                    euf_axiom_result.clauses.len()
                );
            }
            for clause in euf_axiom_result.clauses {
                all_clauses.push(clause);
            }
            if phase_trace_start.is_some() {
                eprintln!(
                    "c phase-trace clauses.after-euf-axioms={}",
                    all_clauses.len()
                );
            }
            running_offset += euf_axiom_result.num_vars;
            euf_axiom_result.num_vars
        } else {
            0
        };

        // Interrupt check after encoding phases (#8609).
        // Phases 5-9 (clause combination, linking, congruence, axiom generation)
        // can be expensive for combined theories (QF_ABV, QF_UFBV). Check before
        // committing to SAT solving. Use local check to avoid borrow conflict
        // with bv_solver's &self.ctx.terms borrow.
        if bv_is_interrupted() {
            drop(bv_solver);
            if let Some((_, original)) = var_subst {
                self.ctx.assertions = original;
            }
            self.propagate_bv_unknown_reason(true);
            return Ok(SolveResult::Unknown);
        }

        // Clone term_bits for model extraction (needed after bv_solver is consumed).
        let term_bits = bv_solver.term_to_bits().clone();
        let bv_predicate_to_var = bv_solver.predicate_to_var().clone();
        let bv_bool_to_var = bv_solver.bool_to_var().clone();
        // Alias for assumption path which references term_bits_snapshot
        let term_bits_snapshot = &term_bits;
        // Extract delayed state before dropping bv_solver (#7015).
        let mut delayed_state = bv_solver.take_delayed_state();
        // Save division caches for Phase 2 circuit building.
        // The actual next_var for tmp_bv is computed later using total_vars
        // to avoid variable collisions with array/EUF axiom variables.
        let mut delay_div_caches = if delayed_state.is_some() {
            Some((
                bv_solver.div_caches().0.clone(),
                bv_solver.div_caches().1.clone(),
                // Placeholder; will be updated after total_vars is computed.
                bv_solver.num_vars() + 1,
            ))
        } else {
            None
        };
        let has_delayed_ops = delayed_state.is_some();
        drop(bv_solver);

        // Non-BV-return UF congruence (#5433)
        // Item 4 Stage 2: the pass polls interrupt/deadline/memory inside its
        // all-pairs loop and may bail with a PARTIAL axiomatization. Partial
        // congruence is sound for UNSAT only — any CDCL SAT below must be
        // degraded to Unknown while `non_bv_congruence_bailed` is set.
        let mut non_bv_congruence_bailed = false;
        if config.non_bv_congruence {
            let congruence_outcome = self.generate_non_bv_euf_congruence(
                &term_bits,
                &bv_bool_to_var,
                &tseitin_result,
                running_offset,
                &mut all_clauses,
                assumptions,
            );
            non_bv_congruence_bailed = congruence_outcome.bailed;
            if non_bv_congruence_bailed && std::env::var_os("AY_PHASE_TRACE").is_some() {
                eprintln!("c phase-trace non-bv-congruence-bailed");
            }
            if phase_trace_start.is_some() {
                eprintln!(
                    "c phase-trace clauses.after-non-bv-congruence={}",
                    all_clauses.len()
                );
            }
            running_offset += congruence_outcome.num_vars;
        }

        let mut total_vars = running_offset;

        // Fix next_var for delayed circuit building (#8480):
        // New BV variables must not collide with array/EUF axiom variables.
        // The BV offset is var_offset (= tseitin_num_vars), so BV var N maps
        // to SAT var (var_offset + N - 1). To avoid collisions with variables
        // in the [tseitin+bv .. total_vars) range, new BV variables must start
        // at (total_vars - var_offset + 1) = (running_offset - tseitin_num_vars + 1).
        if let Some((_, _, ref mut next_var)) = delay_div_caches {
            let safe_next = total_vars - tseitin_result.num_vars + 1;
            if safe_next > *next_var {
                *next_var = safe_next;
            }
        }

        if self.debug_ufbv && config.uf_congruence {
            safe_eprintln!("DEBUG: Total vars = {}", total_vars);
            safe_eprintln!("DEBUG: Total clauses = {}", all_clauses.len());
            safe_eprintln!(
                "DEBUG: tseitin_num_vars={} bv_num_vars={} var_offset={}",
                tseitin_result.num_vars,
                bv_num_vars,
                var_offset
            );
        }

        // Interrupt check after all encoding phases, before SAT solve (#3070).
        if self.should_abort_theory_loop() {
            if let Some((_, original)) = var_subst {
                self.ctx.assertions = original;
            }
            return Ok(SolveResult::Unknown);
        }

        // --- Phase 10: SAT solving ---
        phase_trace!("phase10-sat");
        if phase_trace_start.is_some() {
            let total_lits: usize = all_clauses.iter().map(|c| c.literals().len()).sum();
            eprintln!(
                "c phase-trace phase10-load vars={} clauses={} lits={}",
                total_vars,
                all_clauses.len(),
                total_lits
            );
        }
        // B-cert pipeline (#56): dump the complete eager bit-blast plus any
        // check-sat-assuming literals (as unit clauses).  I/O failure aborts
        // this check before a verdict can escape; certificate production is
        // never a best-effort trace side effect.
        bv_cnf_dump::write_formula(&all_clauses, total_vars, &sat_assumptions)?;

        // B-cert single-invocation DRAT (#56): when `--proof X.drat` is paired
        // with `--dump-bv-cnf`, the SAME eager bit-blast that produced the dumped
        // CNF also emits a drat-trim-checkable DRAT beside it. The DRAT stream is
        // written live by the SAT solver's proof manager (identical to DIMACS
        // mode) against the exact variable numbering of the dumped CNF, so the
        // CNF and its UNSAT certificate are guaranteed to come from one solve.
        //
        // Only the plain (no check-sat-assuming) path is certified this way: an
        // assumption-augmented formula is dumped as CNF-plus-unit-clauses, but
        // the live DRAT of an assumption solve terminates in an
        // assumption-negation clause rather than the empty clause, so it would
        // not be a stand-alone refutation of the dumped CNF. That case fails
        // closed rather than emit an uncheckable proof (§0).
        let bv_drat = if export_bv_cnf {
            bv_cnf_dump::bv_drat_target()
        } else {
            None
        };
        if bv_drat.is_some() && has_assumptions {
            return Err(crate::executor_types::ExecutorError::ArtifactExport(
                "--proof DRAT with --dump-bv-cnf does not support check-sat-assuming: the \
                 assumption-augmented bit-blast has no single-invocation DRAT certificate"
                    .to_string(),
            ));
        }

        let mut solver = if let Some((drat_path, binary)) = bv_drat {
            let file = std::fs::File::create(drat_path).map_err(|error| {
                crate::executor_types::ExecutorError::ArtifactExport(format!(
                    "cannot create --proof DRAT output '{drat_path}': {error}"
                ))
            })?;
            let writer = std::io::BufWriter::new(file);
            let output = if binary {
                ProofOutput::drat_binary(writer)
            } else {
                ProofOutput::drat_text(writer)
            };
            SatSolver::with_proof_output(total_vars as usize, output)
        } else {
            SatSolver::new(total_vars as usize)
        };
        self.apply_random_seed_to_sat(&mut solver);
        self.apply_progress_to_sat(&mut solver);
        configure_ephemeral_bv_sat_solver(
            &mut solver,
            total_vars as usize,
            all_clauses.len(),
            config.array_axioms,
        );

        // Wire a deadline-aware interrupt flag to the SAT solver so
        // preprocessing passes (congruence, BVE, probing) honor the DPLL
        // executor timeout (#8782). The deadline timer must not write into the
        // executor/API interrupt flag: API callers reuse a solver across many
        // checks, and a timed-out BV subsolve must not poison later queries as
        // externally interrupted (#8961).
        let _deadline_guard = install_bv_sat_interrupt(
            &mut solver,
            self.solve_interrupt.clone(),
            self.solve_deadline.get(),
        );

        // The internal Alethe clause trace and the live DRAT proof manager are
        // mutually exclusive proof surfaces; the DRAT route owns the proof
        // manager, so never also arm clause tracing on it.
        if proof_enabled && bv_drat.is_none() {
            solver.enable_clause_trace();
            solver.set_proof_bookkeeping_budget(self.search_proof_bookkeeping_budget());
        }

        // --- JIT batch compilation for BV clauses (#8275) ---
        // Feed clauses to SAT solver and collect arena offsets for JIT compilation.
        // BV clauses use arena offsets as clause IDs so that conflict analysis
        // can construct ClauseRef(arena_offset) to access the clause via standard
        // 2WL infrastructure. The compiled formula is installed as a separate
        // bv_compiled_formula alongside the main compiled_formula.
        //
        // On non-JIT builds, clauses are added via add_clause_prenormalized
        // (the original path).
        {
            let mut lit_buf: Vec<SatLiteral> = Vec::with_capacity(8);
            for clause in &all_clauses {
                lit_buf.clear();
                lit_buf.extend(
                    clause
                        .literals()
                        .iter()
                        .map(|&lit| crate::cnf_lit_to_sat(lit)),
                );
                // Sort for add_clause_prenormalized contract: Tseitin/BV
                // gate clauses have unique variables but may not be sorted.
                lit_buf.sort_unstable_by_key(|l| l.raw());
                solver.add_clause_prenormalized(&lit_buf);
            }
        }

        // When assumptions are present, use solve_with_assumptions for unsat core
        // extraction. Otherwise use the standard solve() path.
        if has_assumptions {
            solver.set_max_learned_clauses(self.learned_clause_limit);
            solver.set_max_clause_db_bytes(resolve_clause_db_bytes_limit(
                self.clause_db_bytes_limit,
                total_vars,
            ));

            // Use interruptible variant to respect timeout/interrupt (#3381)
            let should_stop = self.make_should_stop();
            let assume_result =
                solver.solve_with_assumptions_interruptible(&sat_assumptions, should_stop);

            collect_sat_stats!(self, &solver);

            match assume_result.into_inner() {
                AssumeResult::Sat(model) => {
                    // Item 4 Stage 2 soundness gate (see the Phase 11 twin):
                    // SAT under a bailed partial congruence axiomatization
                    // degrades to Unknown.
                    if non_bv_congruence_bailed {
                        if let Some((_, original)) = var_subst {
                            self.ctx.assertions = original;
                        }
                        return self.finalize_bv_congruence_bail();
                    }
                    self.last_assumption_core = None;
                    let mut bv_model = Self::extract_bv_model_from_bits(
                        &model,
                        term_bits_snapshot,
                        var_offset,
                        &self.ctx.terms,
                    );
                    // Carry Bool-in-BV variable assignments (ite conditions)
                    // into the model (#bv-ite-bool-model).
                    Self::seed_bv_bool_assignments_from_bitblast(
                        &model,
                        &bv_bool_to_var,
                        var_offset,
                        &self.ctx.terms,
                        &mut bv_model,
                    );
                    let bv_validation = ay_bv::validate_bv_assertions(
                        &self.ctx.terms,
                        &self.ctx.assertions,
                        &bv_model,
                    );
                    match bv_validation {
                        Ok(checked) => {
                            self.last_statistics
                                .set_int("model_validation.bv.checked", checked as u64);
                        }
                        Err(error) => {
                            return self.finalize_bv_model_validation_failure(error);
                        }
                    }
                    return self.solve_and_store_model_full(
                        SatResult::Sat(model),
                        &tseitin_result,
                        None,
                        None,
                        None,
                        None,
                        Some(bv_model),
                        None,
                        None,
                        None,
                    );
                }
                AssumeResult::Unsat(core_lits, _) => {
                    // Map SAT literals back to original assumption TermIds
                    let core_terms: Vec<TermId> = core_lits
                        .iter()
                        .filter_map(|&lit| {
                            assumption_to_term
                                .iter()
                                .find(|(sat_lit, _)| {
                                    sat_lit.variable() == lit.variable()
                                        && sat_lit.is_positive() == lit.is_positive()
                                })
                                .map(|(_, term)| *term)
                        })
                        .collect();
                    debug_assert!(
                        core_terms.iter().all(|ct| assumptions.contains(ct)),
                        "BUG: BV assumption core contains term not in original assumptions"
                    );
                    self.last_assumption_core = Some(core_terms);

                    // UNSAT proof handling (#340, #4176)
                    if proof_enabled {
                        self.save_bv_unsat_proof_state(
                            solver.take_clause_trace(),
                            &tseitin_result.var_to_term,
                        );
                    }

                    return self.solve_and_store_model(
                        SatResult::Unsat(ay_sat::ProofCertificate::empty()),
                        &tseitin_result,
                        None,
                        None,
                    );
                }
                AssumeResult::Unknown => {
                    self.last_assumption_core = None;
                    return self.solve_and_store_model(
                        SatResult::Unknown,
                        &tseitin_result,
                        None,
                        None,
                    );
                }
                #[allow(unreachable_patterns)]
                _ => unreachable!("BUG: AssumeResult variant not handled in BV assumption path"),
            }
        }

        // Standard solve path (no assumptions)
        //
        // Delayed internalization (#7015) uses a post-solve re-check loop:
        // 1. Solve the formula without circuit clauses (delayed ops have
        //    unconstrained result bits)
        // 2. If SAT, check delayed ops against the model
        // 3. If violations: add cheap axiom clauses or full circuit clauses
        //    as regular clauses and re-solve
        // 4. Repeat until consistent or max iterations
        //
        // This replaces the previous Extension::check() + AddClauses approach
        // (#8284) which caused spurious UNSAT (#8480). The AddClauses path
        // injected thousands of new-variable clauses into a complete model
        // via add_theory_lemma, which interacted badly with the CDCL loop
        // (pending_theory_conflict overwrite, level-0 unit conflicts from
        // partial propagation during batch addition). The re-solve loop is
        // simpler, correct, and matches Z3's actual implementation: Z3's
        // bv_solver::check() returns a status that causes the outer DPLL(T)
        // loop to restart from scratch with the new clauses.
        let mut solve_result;

        if has_delayed_ops {
            let mut ds = delayed_state
                .take()
                .expect("delayed_state must exist when has_delayed_ops");

            // First solve: no extension, just the original clauses.
            let should_stop = self.make_should_stop();
            let mut current_result = solver.solve_interruptible(should_stop).into_inner();
            collect_sat_stats!(self, &solver);

            // Re-check loop: verify delayed ops and add clauses as needed.
            const MAX_DELAYED_ITERATIONS: u32 = 32;
            let mut iteration = 0u32;

            // Accumulator: ALL cheap-axiom and circuit clauses added across
            // re-check iterations. Required because each iteration creates a
            // fresh SAT solver (to avoid stale BCP state after add_clause on a
            // solved solver — see #8480), so circuit clauses added in a prior
            // iteration would be lost without this accumulator. Without the
            // accumulator, the SAT solver can return a model in iter N that
            // violates circuit constraints added in iter N-1, leaving a
            // delayed op with `circuit_built=true` but an inconsistent value
            // (bug #8698: z3_7526 at width=16+ returned Unknown because the
            // 32-bit bvmul's circuit clauses were dropped on the next
            // re-solve).
            let mut accumulated_delayed_clauses: Vec<Vec<SatLiteral>> = Vec::new();

            // If the first solve returns UNSAT but there are unresolved delayed
            // ops, the UNSAT may be spurious: unconstrained result bits are
            // connected to constrained formula terms via Tseitin equality
            // clauses, and the SAT solver can derive false contradictions.
            //
            // Fix: build all delayed circuits and re-solve from scratch with
            // a fresh SAT solver. We cannot reuse the existing solver because
            // once has_empty_clause is set, it always returns UNSAT.
            if matches!(current_result, SatResult::Unsat(_)) && ds.has_unresolved() {
                let unresolved_indices: Vec<usize> = ds
                    .delayed_ops()
                    .iter()
                    .enumerate()
                    .filter(|(_, op)| !op.circuit_built)
                    .map(|(i, _)| i)
                    .collect();

                if !unresolved_indices.is_empty() {
                    let mut tmp_bv = BvSolver::new(&self.ctx.terms);
                    tmp_bv.set_term_to_bits(ds.term_to_bits().clone());
                    if let Some((ref ucache, ref scache, ref mut next_var)) = delay_div_caches {
                        tmp_bv.set_div_caches(ucache.clone(), scache.clone());
                        tmp_bv.set_next_var(*next_var);
                    }
                    tmp_bv.set_delayed_ops(ds.delayed_ops().to_vec());

                    let mut circuit_clauses_sat: Vec<Vec<SatLiteral>> = Vec::new();
                    for &idx in &unresolved_indices {
                        let circuit_clauses = tmp_bv.build_delayed_circuit(idx);
                        for clause in &circuit_clauses {
                            let sat_lits: Vec<SatLiteral> = clause
                                .literals()
                                .iter()
                                .map(|&lit| {
                                    crate::cnf_lit_to_sat(bv_encoding::offset_cnf_lit(
                                        lit, var_offset,
                                    ))
                                })
                                .collect();
                            circuit_clauses_sat.push(sat_lits);
                        }
                        let bv_extra = tmp_bv.take_clauses();
                        for clause in &bv_extra {
                            let sat_lits: Vec<SatLiteral> = clause
                                .literals()
                                .iter()
                                .map(|&lit| {
                                    crate::cnf_lit_to_sat(bv_encoding::offset_cnf_lit(
                                        lit, var_offset,
                                    ))
                                })
                                .collect();
                            circuit_clauses_sat.push(sat_lits);
                        }
                    }

                    if let Some((_, _, ref mut next_var)) = delay_div_caches {
                        *next_var = tmp_bv.num_vars() + 1;
                    }

                    if !circuit_clauses_sat.is_empty() && !self.should_abort_theory_loop() {
                        // Persist circuit clauses into the accumulator so that
                        // every subsequent fresh-solver rebuild (#8698) keeps
                        // them in scope. Without this, a later cheap-axiom
                        // re-solve would drop the circuit clauses on the
                        // floor, allowing the SAT solver to return a model
                        // where the circuit-built op is still inconsistent.
                        accumulated_delayed_clauses.extend(circuit_clauses_sat.iter().cloned());

                        // Determine the new total variable count.
                        let circuit_max_var = circuit_clauses_sat
                            .iter()
                            .flat_map(|c| c.iter())
                            .map(|l| l.variable().index() + 1)
                            .max()
                            .unwrap_or(0);
                        let new_total_vars = circuit_max_var.max(total_vars as usize);

                        // Create a fresh SAT solver with original + circuit clauses.
                        let mut fresh_solver = SatSolver::new(new_total_vars);
                        self.apply_random_seed_to_sat(&mut fresh_solver);
                        self.apply_progress_to_sat(&mut fresh_solver);
                        configure_ephemeral_bv_sat_solver(
                            &mut fresh_solver,
                            new_total_vars,
                            all_clauses.len() + accumulated_delayed_clauses.len(),
                            config.array_axioms,
                        );
                        if let Some(ref flag) = self.solve_interrupt {
                            fresh_solver.set_interrupt(flag.clone());
                        }

                        // Re-add all original clauses.
                        for clause in &all_clauses {
                            let sat_lits: Vec<SatLiteral> = clause
                                .literals()
                                .iter()
                                .map(|&lit| crate::cnf_lit_to_sat(lit))
                                .collect();
                            fresh_solver.add_clause(sat_lits);
                        }
                        // Add circuit clauses.
                        for clause in circuit_clauses_sat {
                            fresh_solver.add_clause(clause);
                        }

                        let should_stop = self.make_should_stop();
                        current_result = fresh_solver.solve_interruptible(should_stop).into_inner();
                        collect_sat_stats!(self, &fresh_solver);
                        solver = fresh_solver;
                        // Update total_vars so CEGAR loop doesn't collide.
                        total_vars = total_vars.max(new_total_vars as u32);
                    }
                }
            }

            // Residual iteration-cap hole (#4666/#8595): when the CEGAR refinement
            // budget is exhausted, the candidate model has NOT been verified against
            // the remaining delayed ops (the `ds.check` below is skipped), so a
            // delayed result variable may still violate its defining op (e.g.
            // `full_chunks = usize::MAX` while the udiv relation requires
            // `full_chunks*3 <= len <= isize::MAX`). Record that case and downgrade to
            // Unknown after the loop instead of publishing a possibly-spurious Sat.
            let mut cap_hit_unresolved = false;
            while let SatResult::Sat(ref model) = current_result {
                if iteration >= MAX_DELAYED_ITERATIONS {
                    // Downgrade ONLY if the candidate model is actually INCONSISTENT
                    // with a remaining delayed op — i.e. a final `check` against THIS
                    // model still yields refinement clauses. A model that happens to
                    // satisfy every delayed op (empty check) is a genuine Sat and must
                    // be preserved (using `has_unresolved()` alone over-rejects such
                    // consistent-but-not-circuit-built models).
                    if ds.has_unresolved() {
                        let (cheap, circ) = ds.check(model, var_offset);
                        cap_hit_unresolved = !cheap.is_empty() || !circ.is_empty();
                    }
                    break;
                }
                iteration += 1;

                if !ds.has_unresolved() {
                    break;
                }

                // Check delayed ops against the current model.
                let (cheap_clauses, needs_circuit) = ds.check(model, var_offset);

                if cheap_clauses.is_empty() && needs_circuit.is_empty() {
                    // All delayed ops are consistent under the current model.
                    // This is only correct when previously-built circuits are
                    // preserved across re-solves via accumulated_delayed_clauses
                    // (#8698) — otherwise a "built" op may still be inconsistent.
                    break;
                }

                // Collect all new clauses (cheap axioms + full circuits).
                let mut new_clauses: Vec<Vec<SatLiteral>> = Vec::new();

                // Phase 1: cheap axiom clauses.
                for clause in &cheap_clauses {
                    let sat_lits: Vec<SatLiteral> = clause
                        .literals()
                        .iter()
                        .map(|&lit| {
                            crate::cnf_lit_to_sat(bv_encoding::offset_cnf_lit(lit, var_offset))
                        })
                        .collect();
                    new_clauses.push(sat_lits);
                }

                // Phase 2: build full circuits for ops that exhausted cheap axioms.
                if !needs_circuit.is_empty() {
                    let mut tmp_bv = BvSolver::new(&self.ctx.terms);
                    tmp_bv.set_term_to_bits(ds.term_to_bits().clone());
                    if let Some((ref ucache, ref scache, ref mut next_var)) = delay_div_caches {
                        tmp_bv.set_div_caches(ucache.clone(), scache.clone());
                        tmp_bv.set_next_var(*next_var);
                    }
                    tmp_bv.set_delayed_ops(ds.delayed_ops().to_vec());

                    for &idx in &needs_circuit {
                        let circuit_clauses = tmp_bv.build_delayed_circuit(idx);
                        for clause in &circuit_clauses {
                            let sat_lits: Vec<SatLiteral> = clause
                                .literals()
                                .iter()
                                .map(|&lit| {
                                    crate::cnf_lit_to_sat(bv_encoding::offset_cnf_lit(
                                        lit, var_offset,
                                    ))
                                })
                                .collect();
                            new_clauses.push(sat_lits);
                        }
                        let bv_extra = tmp_bv.take_clauses();
                        for clause in &bv_extra {
                            let sat_lits: Vec<SatLiteral> = clause
                                .literals()
                                .iter()
                                .map(|&lit| {
                                    crate::cnf_lit_to_sat(bv_encoding::offset_cnf_lit(
                                        lit, var_offset,
                                    ))
                                })
                                .collect();
                            new_clauses.push(sat_lits);
                        }
                    }

                    if let Some((_, _, ref mut next_var)) = delay_div_caches {
                        *next_var = tmp_bv.num_vars() + 1;
                    }
                }

                if new_clauses.is_empty() {
                    break;
                }

                // Accumulate this iteration's cheap-axiom and circuit clauses
                // so future re-solves keep them in scope (#8698). Each fresh
                // SAT solver below adds `all_clauses` plus the entire
                // accumulator — this guarantees that once a delayed op's
                // circuit is built, the SAT solver can never again return a
                // model where that circuit is violated.
                accumulated_delayed_clauses.extend(new_clauses.iter().cloned());

                // Re-solve with a fresh SAT solver containing original + ALL
                // accumulated delayed clauses. We cannot reuse the existing
                // solver because adding clauses to a solver that has a
                // complete SAT model can trigger BCP during add_clause that
                // derives false contradictions from the stale model state
                // (#8480).
                if self.should_abort_theory_loop() {
                    current_result = SatResult::Unknown;
                    break;
                }

                let circuit_max_var = accumulated_delayed_clauses
                    .iter()
                    .flat_map(|c| c.iter())
                    .map(|l| l.variable().index() + 1)
                    .max()
                    .unwrap_or(0);
                let new_total = circuit_max_var.max(total_vars as usize);

                let mut fresh = SatSolver::new(new_total);
                self.apply_random_seed_to_sat(&mut fresh);
                self.apply_progress_to_sat(&mut fresh);
                configure_ephemeral_bv_sat_solver(
                    &mut fresh,
                    new_total,
                    all_clauses.len() + accumulated_delayed_clauses.len(),
                    config.array_axioms,
                );
                if let Some(ref flag) = self.solve_interrupt {
                    fresh.set_interrupt(flag.clone());
                }

                // Re-add all original clauses.
                for clause in &all_clauses {
                    let sat_lits: Vec<SatLiteral> = clause
                        .literals()
                        .iter()
                        .map(|&lit| crate::cnf_lit_to_sat(lit))
                        .collect();
                    fresh.add_clause(sat_lits);
                }
                // Add ALL accumulated delayed clauses (circuits + cheap axioms)
                // across every iteration so far.
                for clause in &accumulated_delayed_clauses {
                    fresh.add_clause(clause.clone());
                }

                let should_stop = self.make_should_stop();
                current_result = fresh.solve_interruptible(should_stop).into_inner();
                collect_sat_stats!(self, &fresh);
                solver = fresh;
                // Update total_vars so CEGAR loop doesn't collide.
                total_vars = total_vars.max(new_total as u32);
            }

            // SOUND downgrade (#4666/#8595): a Sat that exhausted the delayed-op
            // refinement budget with ops still unresolved is possibly spurious (a
            // delayed result variable may violate its defining op) — publish Unknown,
            // never a false counterexample. This only ever turns a candidate-Sat into
            // Unknown: a genuine model resolves every delayed op and exits the loop
            // via the `!ds.has_unresolved()` / consistent-`check` breaks (leaving
            // `cap_hit_unresolved == false`), so real Sat and all Unsat results are
            // unaffected — the feasible set is never enlarged or under-cut.
            if cap_hit_unresolved && matches!(current_result, SatResult::Sat(_)) {
                current_result = SatResult::Unknown;
            }
            solve_result = current_result;
            self.propagate_bv_unknown_reason(matches!(solve_result, SatResult::Unknown));
        } else {
            // Bound the learned-clause DB on the long naked solve (#dt-array-fc-lazy),
            // mirroring the has-assumptions branch. A huge instance (21M+ vars) can
            // otherwise grow an unbounded learned DB over a multi-hour solve,
            // drowning BCP. Caps bound only LEARNED clauses (never original), so
            // completeness/soundness are unaffected — just memory.
            solver.set_max_learned_clauses(self.learned_clause_limit);
            solver.set_max_clause_db_bytes(resolve_clause_db_bytes_limit(
                self.clause_db_bytes_limit,
                total_vars,
            ));
            let should_stop = self.make_should_stop();
            solve_result = solver.solve_interruptible(should_stop).into_inner();
            collect_sat_stats!(self, &solver);
            self.propagate_bv_unknown_reason(matches!(solve_result, SatResult::Unknown));
        }

        // --- Phase 10.7: CEGAR array FC refinement (#8510) ---
        phase_trace!("phase10.7-cegar");
        //
        // After SAT returns a satisfying assignment, check array functional
        // consistency: for any two select terms on the same array with equal
        // concrete index values, their result values must also be equal.
        //
        // The upfront FC axiom budget (FC_CROSS_BASE_BUDGET_PER_ARRAY = 200)
        // can be insufficient for arrays with many constant-indexed selects
        // and few symbolic-indexed selects (e.g., csplit-query QF_ABV:
        // 2050 constant selects + 8 symbolic selects = 16K+ needed cross-base
        // pairs, but only 200 generated). The CEGAR loop lazily adds only
        // the FC axioms that are actually violated by the current model.
        if config.array_axioms {
            // Env-tunable (#dt-array-fc-lazy): with a lowered eager FC budget,
            // more real FC violations surface across rounds, so a large-array
            // instance may need more than 16 lazy refinements to converge (it
            // fail-closes to Unknown if the cap is hit with residual violations).
            let max_cegar_iterations: u32 = std::env::var("AY_FC_CEGAR_ITERS")
                .ok()
                .and_then(|s| s.trim().parse::<u32>().ok())
                .unwrap_or(16);
            let mut cegar_next_var = total_vars;
            let mut cegar_iteration = 0u32;
            let mut already_covered = HashSet::default();

            while let SatResult::Sat(ref model) = solve_result {
                if cegar_iteration >= max_cegar_iterations {
                    // Fail-closed exhaustion (#8510 + FC same-base budget): the
                    // last refinement round added axioms and re-solved, but the
                    // NEW model has not been re-verified. If FC violations
                    // remain, letting this Sat escape would be a WRONG sat
                    // (the model contradicts array functional consistency).
                    // One final check; violations => degrade to Unknown.
                    let residual = self.check_array_fc_violations(
                        model,
                        &term_bits,
                        var_offset,
                        cegar_next_var as usize,
                        &mut already_covered,
                    );
                    if residual.is_some() {
                        if std::env::var_os("AY_PHASE_TRACE").is_some() {
                            eprintln!("c phase-trace cegar-exhausted-residual-violations");
                        }
                        self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        solve_result = SatResult::Unknown;
                    }
                    break;
                }
                if self.should_abort_theory_loop() {
                    solve_result = SatResult::Unknown;
                    break;
                }

                let violations = self.check_array_fc_violations(
                    model,
                    &term_bits,
                    var_offset,
                    cegar_next_var as usize,
                    &mut already_covered,
                );

                let Some(result) = violations else {
                    break; // No FC violations — model is consistent
                };

                cegar_iteration += 1;

                // Grow solver and add FC axiom clauses.
                cegar_next_var += result.num_new_vars as u32;
                let max_var = result
                    .clauses
                    .iter()
                    .flat_map(|c| c.iter())
                    .map(|l| l.variable().index() + 1)
                    .max()
                    .unwrap_or(0);
                solver.ensure_num_vars(max_var);
                for clause in result.clauses {
                    solver.add_clause(clause);
                }

                // Re-solve with additional FC axiom clauses.
                let should_stop = self.make_should_stop();
                solve_result = solver.solve_interruptible(should_stop).into_inner();
                collect_sat_stats!(self, &solver);
            }
        }

        // Item 4 Stage 2 soundness gate: a SAT found under a BAILED (partial)
        // non-BV congruence axiomatization may violate an unemitted
        // congruence constraint — degrade to Unknown before model
        // extraction. UNSAT remains reportable (partial axioms are a subset
        // of the full axiomatization).
        if non_bv_congruence_bailed && matches!(solve_result, SatResult::Sat(_)) {
            if let Some((_, original)) = var_subst {
                self.ctx.assertions = original;
            }
            return self.finalize_bv_congruence_bail();
        }

        // Finalize the single-invocation BV DRAT (#56) now that the verdict is
        // settled: on UNSAT flush and keep the (empty-clause-terminated) proof,
        // on SAT/Unknown remove the scratch file so no verdict carries a
        // non-refuting proof. `solve_result` is final here for the export path
        // (pure QF_BV has no delayed-op re-solve, array CEGAR, or congruence
        // bail; the assumption path returned earlier and never installs a DRAT).
        if let Some((drat_path, _)) = bv_drat {
            let proof = solver.take_proof_writer();
            bv_cnf_dump::finish_bv_drat(
                proof,
                drat_path,
                matches!(solve_result, SatResult::Unsat(_)),
            )?;
        }

        // --- Phase 11: Model extraction ---
        phase_trace!("phase11-model");
        if let SatResult::Sat(ref model) = solve_result {
            let sat_model: Vec<bool> = model.clone();
            // Use term_bits clone if bv_solver was dropped (non-BV congruence path),
            // otherwise get from bv_solver directly.
            let mut bv_model = Self::extract_bv_model_from_bits(
                &sat_model,
                &term_bits,
                var_offset,
                &self.ctx.terms,
            );

            // Seed bool_overrides with Tseitin SAT assignments for Bool-sorted terms (#5115).
            for (&dimacs_var, &term) in &tseitin_result.var_to_term {
                if *self.ctx.terms.sort(term) == Sort::Bool {
                    let sat_idx = (dimacs_var - 1) as usize;
                    if let Some(&val) = sat_model.get(sat_idx) {
                        bv_model.bool_overrides.entry(term).or_insert(val);
                    }
                }
            }

            // Seed bool_overrides with the BV bit-blaster's SAT assignments for
            // Bool variables reached only inside BV terms (ite conditions),
            // which the Tseitin encoding never sees (#bv-ite-bool-model).
            Self::seed_bv_bool_assignments_from_bitblast(
                &sat_model,
                &bv_bool_to_var,
                var_offset,
                &self.ctx.terms,
                &mut bv_model,
            );

            // Preprocessor variable substitution recovery (#1708/#1789, #8140)
            let mut array_substitutions = Vec::new();
            let mut substituted_vars: HashSet<TermId> = HashSet::default();
            let mut restored_assertions_covered_by_bv = HashSet::default();
            let current_assertions: Vec<TermId> = self.ctx.assertions.clone();
            let coverage_assertions = if var_subst.is_some() {
                primary_formula_assertions
                    .as_deref()
                    .unwrap_or(current_assertions.as_slice())
            } else {
                current_assertions.as_slice()
            };
            let coverage_covered: Vec<bool> = coverage_assertions
                .iter()
                .map(|&assertion| {
                    Self::bv_assertion_covered(
                        &self.ctx.terms,
                        assertion,
                        &tseitin_result,
                        &bv_predicate_to_var,
                        &bv_bool_to_var,
                        var_offset,
                        &sat_model,
                    )
                })
                .collect();
            self.last_statistics.set_int(
                "model_validation.bv.coverage_assertions",
                coverage_assertions.len() as u64,
            );
            self.last_statistics.set_int(
                "model_validation.bv.covered_assertions",
                coverage_covered.iter().filter(|&&covered| covered).count() as u64,
            );
            let covered_formula_roots: HashSet<TermId> = coverage_assertions
                .iter()
                .zip(coverage_covered.iter())
                .filter_map(|(&assertion, &covered)| covered.then_some(assertion))
                .collect();
            let coverage_source_sets = if var_subst.is_some() {
                primary_formula_assertion_source_sets
                    .as_deref()
                    .or(current_assertion_source_sets.as_deref())
            } else {
                None
            };
            if var_subst.is_none() {
                restored_assertions_covered_by_bv.extend(covered_formula_roots.iter().copied());
            }
            if let Some((ref var_subst, _)) = var_subst {
                let source_sets_present = coverage_source_sets.is_some();
                let (source_mapped_assertions, split_source_assertions, source_sets_valid) =
                    Self::add_restored_bv_coverage_from_sources(
                        &self.ctx.terms,
                        &mut restored_assertions_covered_by_bv,
                        &coverage_covered,
                        coverage_source_sets,
                    );
                self.last_statistics.set_int(
                    "model_validation.bv.source_sets_present",
                    u64::from(source_sets_present),
                );
                self.last_statistics.set_int(
                    "model_validation.bv.source_sets_valid",
                    u64::from(source_sets_valid),
                );
                self.last_statistics.set_int(
                    "model_validation.bv.source_mapped_assertions",
                    source_mapped_assertions.len() as u64,
                );
                self.last_statistics.set_int(
                    "model_validation.bv.split_source_assertions",
                    split_source_assertions.len() as u64,
                );

                let substitutions = var_subst
                    .lock()
                    .expect("variable substitution mutex poisoned during BV model recovery");
                let subs: Vec<(TermId, TermId)> = substitutions
                    .substitutions()
                    .iter()
                    .map(|(&k, &v)| (k, v))
                    .collect();
                // Record eliminated-variable definitions for model completion
                // at finalize time (model/completion.rs). Complements the
                // BV-local recovery below for RHS forms it cannot evaluate.
                for &(from, to) in &subs {
                    self.recorded_var_substitutions.insert(from, to);
                }
                array_substitutions = subs
                    .iter()
                    .copied()
                    .filter(|(from_var, _)| {
                        matches!(self.ctx.terms.sort(*from_var), Sort::Array(_))
                    })
                    .collect();
                // #abv-select-congruence: array-model extraction excludes
                // select pairs whose index mentions an eliminated variable
                // (their bit-blast values are decoupled junk).
                substituted_vars = subs.iter().map(|&(from_var, _)| from_var).collect();
                Self::recover_substituted_bv_bool_values(&self.ctx.terms, &subs, &mut bv_model);

                if !source_sets_present {
                    self.last_statistics
                        .set_int("model_validation.bv.source_sets_missing_fail_closed", 1);
                }
            }

            // Restore original assertions if preprocessed
            if let Some((_, original)) = &var_subst {
                self.ctx.assertions = original.clone();
            }
            Self::add_delegated_validation_conjuncts(
                &self.ctx.terms,
                &mut restored_assertions_covered_by_bv,
            );
            self.model_validation_delegated_assertions = restored_assertions_covered_by_bv;
            self.last_statistics.set_int(
                "model_validation.bv.restored_delegated_assertions",
                self.model_validation_delegated_assertions.len() as u64,
            );

            match ay_bv::validate_bv_assertions(&self.ctx.terms, &self.ctx.assertions, &bv_model) {
                Ok(checked) => {
                    self.last_statistics
                        .set_int("model_validation.bv.checked", checked as u64);
                }
                Err(error) => {
                    return self.finalize_bv_model_validation_failure(error);
                }
            }

            // Extract array model from BV select terms (#5449)
            let array_model = if config.array_axioms {
                let mut am = Self::extract_array_model_from_bv_model(
                    &self.ctx.terms,
                    &bv_model,
                    &self.ctx.assertions,
                    &substituted_vars,
                );
                Self::populate_array_models_from_substitutions(
                    &self.ctx.terms,
                    &bv_model,
                    &array_substitutions,
                    &mut am.array_values,
                );
                if am.array_values.is_empty() {
                    None
                } else {
                    Some(am)
                }
            } else {
                None
            };
            return self.solve_and_store_model_full(
                SatResult::Sat(sat_model),
                &tseitin_result,
                None,
                array_model,
                None,
                None,
                Some(bv_model),
                None,
                None,
                None,
            );
        }

        // --- Phase 12: Non-SAT result finalization ---
        debug_assert!(
            !matches!(solve_result, SatResult::Sat(_)),
            "BUG: BV SAT case must go through solve_and_store_model_full, not From conversion"
        );

        let clause_trace = if proof_enabled && matches!(solve_result, SatResult::Unsat(_)) {
            solver.take_clause_trace()
        } else {
            None
        };

        if matches!(solve_result, SatResult::Unsat(_)) {
            self.last_assumption_core = Some(vec![]);
        }

        let result = match solve_result {
            SatResult::Unsat(_) => {
                self.finalize_bv_unsat(clause_trace, &tseitin_result.var_to_term, proof_enabled)
            }
            SatResult::Unknown => self.finalize_bv_unknown(),
            SatResult::Sat(_) => {
                unreachable!("BUG: BV SAT case handled above")
            }
            #[allow(unreachable_patterns)]
            _ => unreachable!("BUG: SatResult variant not handled in BV non-incremental path"),
        };

        // Restore original assertions if preprocessed
        if let Some((_, original)) = var_subst {
            self.ctx.assertions = original;
        }

        result
    }

    /// Finalize a BV UNSAT result: save proof state, set result, build proof.
    ///
    /// Shared by non-incremental (no-assumption) and incremental BV paths.
    /// Caller must extract `clause_trace` from the SAT solver before calling
    /// (to release the solver borrow for NLL purposes).
    pub(super) fn finalize_bv_unsat(
        &mut self,
        clause_trace: Option<ClauseTrace>,
        var_to_term: &std::collections::BTreeMap<u32, TermId>,
        proof_enabled: bool,
    ) -> Result<SolveResult> {
        if proof_enabled {
            self.save_bv_unsat_proof_state(clause_trace, var_to_term);
        }
        self.last_model = None;
        self.last_result = Some(SolveResult::unsat());
        if proof_enabled {
            self.build_unsat_proof();
        }
        Ok(SolveResult::unsat())
    }

    /// Degrade a CDCL SAT found under a BAILED (partial) non-BV congruence
    /// axiomatization to Unknown (item 4 Stage 2).
    ///
    /// The congruence pair loop stopped early on interrupt/deadline/memory,
    /// so the emitted axioms are a SUBSET of the full axiomatization: UNSAT
    /// verdicts remain valid, but a model may violate an unemitted
    /// congruence constraint (the 2026-06-20 wrong-SAT hunt class). Fail
    /// closed to Unknown with an Incomplete marker.
    pub(super) fn finalize_bv_congruence_bail(&mut self) -> Result<SolveResult> {
        tracing::warn!(
            "BV non-BV congruence axiomatization bailed mid-loop; degrading CDCL SAT to \
             Unknown (partial congruence is sound for UNSAT only)"
        );
        self.last_statistics
            .set_string("unknown.reason", UnknownReason::Incomplete.to_string());
        self.last_statistics
            .set_string("unknown.phase", "non-bv-congruence-bail");
        self.last_statistics
            .set_string("unknown.cost_center", "bv-non-bv-congruence");
        self.last_model = None;
        self.last_unknown_reason = Some(UnknownReason::Incomplete);
        self.last_result = Some(SolveResult::Unknown);
        Ok(SolveResult::Unknown)
    }

    /// Finalize a BV Unknown result: map SAT-level reason, set result.
    ///
    /// Shared by non-incremental (no-assumption) and incremental BV paths.
    /// Consumes `pending_sat_unknown_reason` (set by `collect_sat_stats!`).
    pub(super) fn finalize_bv_unknown(&mut self) -> Result<SolveResult> {
        self.last_model = None;
        Self::record_sat_unknown_reason(
            &mut self.last_unknown_reason,
            self.pending_sat_unknown_reason.take(),
        );
        if self.last_unknown_reason.is_none() {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
        }
        self.last_result = Some(SolveResult::Unknown);
        Ok(SolveResult::Unknown)
    }

    /// Fail closed when the semantic BV validator disproves the extracted SAT
    /// model. This runs before `solve_and_store_model_full`, so release builds
    /// cannot publish SAT after a BV/QF_ABV assertion evaluates to false.
    pub(super) fn finalize_bv_model_validation_failure(
        &mut self,
        error: BvValidationError,
    ) -> Result<SolveResult> {
        if std::env::var_os("AY_PHASE_TRACE").is_some() {
            eprintln!(
                "c phase-trace bv-model-validation-failed assertion_index={}",
                error.assertion_index
            );
        }
        self.last_statistics.model_validation_failures += 1;
        self.last_statistics.set_int(
            "model_validation.bv.failure.assertion_index",
            error.assertion_index as u64,
        );
        self.last_statistics
            .set_string("model_validation.bv.failure.kind", "false-evaluation");
        self.last_statistics.set_string(
            "model_validation.bv.failure.term",
            self.format_term(error.assertion),
        );
        self.last_statistics
            .set_string("unknown.reason", UnknownReason::Incomplete.to_string());
        self.last_statistics
            .set_string("unknown.phase", "model-validation");
        self.last_statistics
            .set_string("unknown.cost_center", "bv-model-validation");
        self.last_statistics.set_string(
            "unknown.detail",
            format!(
                "BV SAT model validation false-evaluation at assertion {}",
                error.assertion_index
            ),
        );
        tracing::warn!(
            assertion_index = error.assertion_index,
            assertion = ?error.assertion,
            "BV SAT model validation failed, degrading SAT to Unknown"
        );
        // #abv-subst-model-retry: a false-evaluation on a substitution-carrying
        // solve is the in-loop face of the same defect class the independent
        // gate catches downstream (recovery manufactured an invalid model while
        // the SAT search itself was consistent). Arm the single
        // preprocessing-free re-solve in `check_sat_guarded`. No-op for
        // incremental/preprocess-free solves (`bv_subst_lane` stays false).
        if self.bv_subst_lane {
            self.bv_subst_model_rejected = true;
        }
        self.last_model = None;
        self.last_unknown_reason = Some(UnknownReason::Incomplete);
        self.last_result = Some(SolveResult::Unknown);
        Ok(SolveResult::Unknown)
    }

    /// Propagate interrupt/timeout reason to executor when SAT returns Unknown (#3381).
    ///
    /// Called after `collect_sat_stats!` which sets `pending_sat_unknown_reason`.
    /// Only checks interrupt/timeout when the SAT solver didn't provide its own
    /// reason. Shared by non-incremental and incremental BV paths (#6691).
    pub(super) fn propagate_bv_unknown_reason(&mut self, is_unknown: bool) {
        if is_unknown && self.pending_sat_unknown_reason.is_none() {
            if self
                .solve_interrupt
                .as_ref()
                .is_some_and(|f| f.load(Ordering::Relaxed))
            {
                self.last_unknown_reason = Some(UnknownReason::Interrupted);
            } else if self.solve_deadline.expired() {
                self.last_unknown_reason = Some(UnknownReason::Timeout);
            }
        }
    }

    fn should_budget_scalar_variable_substitution(num_stores: usize, num_selects: usize) -> bool {
        num_stores >= 200 && num_selects >= 3_000 && num_selects > 12 * num_stores
    }

    fn count_array_op_occurrences_in_assertions(&self) -> (usize, usize) {
        let mut selects = 0usize;
        let mut stores = 0usize;
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        // Visited set: the term store is a hash-consed DAG, so without it this
        // walk enumerates every tree PATH — exponential in sharing depth (a large
        // BMC instance made this budget-counting helper alone spin for minutes;
        // the DAG→tree pathology). Counting each distinct node once is also the
        // semantically right metric for the substitution budget: the encoder
        // processes each hash-consed node once, not once per path.
        let mut visited: HashSet<TermId> = HashSet::default();

        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) => {
                    match sym.name() {
                        "select" if args.len() == 2 => selects += 1,
                        "store" if args.len() == 3 => stores += 1,
                        _ => {}
                    }
                    stack.extend(args.iter().copied());
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Let(bindings, body) => {
                    stack.push(*body);
                    for (_, binding) in bindings {
                        stack.push(*binding);
                    }
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    for &trigger in triggers.iter().flatten() {
                        stack.push(trigger);
                    }
                }
                TermData::Const(_) | TermData::Var(_, _) => {}
                other => unreachable!(
                    "unhandled TermData variant in count_array_op_occurrences_in_assertions(): {other:?}"
                ),
            }
        }

        (selects, stores)
    }

    /// Save BV UNSAT proof state: clause trace, var→term (DIMACS-1 offset), negations.
    ///
    /// Replaces the 3-copy pattern in BV solve paths (#6691). Builds the
    /// negation map from var_to_term on demand via `build_negation_map`.
    fn save_bv_unsat_proof_state(
        &mut self,
        clause_trace: Option<ClauseTrace>,
        var_to_term: &std::collections::BTreeMap<u32, TermId>,
    ) {
        self.last_clause_trace = clause_trace;
        self.last_var_to_term = Some(var_to_term.iter().map(|(&v, &t)| (v - 1, t)).collect());
        self.last_negations = Some(bv_encoding::build_negation_map(
            &mut self.ctx.terms,
            var_to_term,
        ));
        self.last_clausification_proofs = None;
        self.last_original_clause_theory_proofs = None;
    }

    // Array axiom generation (generate_array_bv_axioms, collect_array_terms) is in bv_axioms_array.rs.
    // EUF axiom generation (generate_euf_bv_axioms*, collect_uf_applications) is in bv_axioms_euf.rs.

    /// Collect BV terms that must be eagerly internalized in combined theories (#8142).
    ///
    /// When delayed BV internalization is enabled for QF_ABV/QF_UFBV/QF_AUFBV,
    /// certain BV terms must still be fully bit-blasted:
    /// - Array select/store index terms and their BV sub-expressions
    /// - Array store value terms and their BV sub-expressions
    /// - UF argument terms and their BV sub-expressions
    ///
    /// This ensures that array functional consistency axioms and EUF congruence
    /// axioms reason over fully constrained bits, preventing false-UNSAT from
    /// unconstrained delayed-op bits in critical positions.
    ///
    /// BV terms that do NOT feed into indices/arguments (e.g., data-path
    /// multiplications stored as values but not used as indices) can still
    /// be delayed.
    /// Collect BV terms that must be eagerly internalized in combined theories (#8142).
    ///
    /// When delayed BV internalization is enabled for QF_ABV/QF_UFBV/QF_AUFBV,
    /// certain BV terms must still be fully bit-blasted:
    /// - Array select/store index terms and their BV sub-expressions
    /// - Array store value terms and their BV sub-expressions
    /// - UF argument terms and their BV sub-expressions
    ///
    /// This ensures that array functional consistency axioms and EUF congruence
    /// axioms reason over fully constrained bits, preventing false-UNSAT from
    /// unconstrained delayed-op bits in critical positions.
    pub(in crate::executor) fn collect_eager_bv_terms(
        &self,
        config: &BvSolveConfig,
        assumption_roots: &[TermId],
    ) -> HashSet<TermId> {
        let mut eager = HashSet::default();

        // Collect array index and value terms that need eager internalization.
        if config.array_axioms {
            let mut selects = Vec::new();
            let mut stores = Vec::new();
            let mut visited = HashSet::default();

            for &assertion in &self.ctx.assertions {
                self.collect_array_terms(assertion, &mut selects, &mut stores, &mut visited);
            }
            for &term in assumption_roots {
                self.collect_array_terms(term, &mut selects, &mut stores, &mut visited);
            }

            // Mark index and value sub-expressions as eager.
            // select(array, INDEX) — index must be eager
            for &(_sel_term, _array, index) in &selects {
                BvSolver::collect_bv_subterms(&self.ctx.terms, index, &mut eager);
            }
            // store(array, INDEX, VALUE) — index must be eager.
            // Value terms also need eager internalization because ROW1 axioms
            // equate store values with select results at the same index.
            for &(_store_term, _base, store_idx, store_val) in &stores {
                BvSolver::collect_bv_subterms(&self.ctx.terms, store_idx, &mut eager);
                BvSolver::collect_bv_subterms(&self.ctx.terms, store_val, &mut eager);
            }
            // Select result terms themselves must also be eager since they
            // appear in functional consistency axiom bit-comparisons.
            for &(sel_term, _array, _index) in &selects {
                BvSolver::collect_bv_subterms(&self.ctx.terms, sel_term, &mut eager);
            }
        }

        // Collect UF argument terms that need eager internalization.
        if config.uf_congruence {
            // Keyed by (name, arity) — distinct arities are distinct UF symbols (#4661).
            let mut uf_apps: HashMap<(String, usize), Vec<(TermId, Vec<TermId>)>> =
                HashMap::default();
            let mut visited = HashSet::default();
            for &assertion in &self.ctx.assertions {
                self.collect_uf_applications(assertion, &mut uf_apps, &mut visited);
            }
            for (_key, applications) in &uf_apps {
                for (_app_term, args) in applications {
                    for &arg in args {
                        BvSolver::collect_bv_subterms(&self.ctx.terms, arg, &mut eager);
                    }
                }
            }
        }

        eager
    }
}

#[cfg(test)]
mod tests;
