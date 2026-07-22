// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared DPLL(T) support types extracted from `lib.rs`.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::time::Instant;
use ay_core::{TermId, TheoryPropagation, TheoryResult, TheorySolver};
use ay_sat::{
    Literal, SatGuidanceFingerprint, SatGuidanceImportDecision, Solver as SatSolver,
    TlaTraceWriter, Variable,
};
use std::time::Duration;

/// Cached env flag for `AY_DEBUG_DPLL` (checked once per process via `OnceLock`).
#[inline]
pub(crate) fn debug_dpll_enabled() -> bool {
    crate::theory_debug_flags::debug_dpll()
}

/// Cached env flag for `AY_DEBUG_SYNC` (checked once per process via `OnceLock`).
#[inline]
pub(crate) fn debug_sync_enabled() -> bool {
    crate::theory_debug_flags::debug_sync()
}

/// Cached env flag: `AY_UFLIA_PHASE=2` additionally prints per-round lazy
/// split-loop timings (SAT-solve / theory-check durations per refinement
/// round). Measurement-only diagnostic for the UFLIA hybrid detour; see the
/// phase-edge companion in `executor/theories/combined/mod.rs`.
#[inline]
pub(crate) fn uflia_phase_round_debug() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AY_UFLIA_PHASE").ok().as_deref() == Some("2"))
}

/// Iterate var->term mappings in deterministic variable order.
///
/// Internal storage uses `HashMap` for O(1)-amortized lookups, but model-to-theory
/// synchronization requires deterministic traversal for stable debugging/proof output.
pub(crate) fn iter_var_to_term_sorted(
    var_to_term: &HashMap<u32, TermId>,
) -> impl Iterator<Item = (u32, TermId)> {
    let mut pairs: Vec<(u32, TermId)> = var_to_term
        .iter()
        .map(|(&var, &term)| (var, term))
        .collect();
    pairs.sort_unstable_by_key(|(var, _)| *var);
    pairs.into_iter()
}

/// Convert a DIMACS literal (1-indexed, signed) to a `ay_sat::Literal` (0-indexed).
///
/// DIMACS convention: positive lit `n` → variable `n-1` positive,
/// negative lit `-n` → variable `n-1` negative. Lit 0 is invalid.
#[inline]
pub(crate) fn cnf_lit_to_sat(lit: i32) -> Literal {
    debug_assert_ne!(lit, 0, "Tseitin literal 0 is invalid");
    if lit > 0 {
        let var = Variable::new((lit - 1) as u32);
        Literal::positive(var)
    } else {
        let var = Variable::new((-lit - 1) as u32);
        Literal::negative(var)
    }
}

/// RAII guard for accumulating phase timing into a `Duration`.
///
/// Modeled on Z3's `scoped_watch` (`reference/z3/src/util/stopwatch.h:83`)
/// and CaDiCaL's `START`/`STOP` macros (`reference/cadical/src/profile.hpp:153`).
/// Accumulates elapsed wall time into the target `Duration` on drop.
pub(crate) struct PhaseTimer<'a> {
    target: &'a mut Duration,
    start: Instant,
}

impl<'a> PhaseTimer<'a> {
    #[inline]
    pub(crate) fn new(target: &'a mut Duration) -> Self {
        Self {
            target,
            start: Instant::now(),
        }
    }
}

impl Drop for PhaseTimer<'_> {
    #[inline]
    fn drop(&mut self) {
        *self.target += self.start.elapsed();
    }
}

/// Construction-side timing breakdown for DPLL(T) setup work.
///
/// These counters are intentionally separate from solve-loop timings so
/// constructor-heavy benchmarks can distinguish setup cost from SAT/theory
/// round-trip cost.
#[derive(Debug, Clone, Default)]
pub(crate) struct DpllConstructionTimings {
    /// Total `from_tseitin_impl()` wall time.
    pub from_tseitin: Duration,
    /// Clause loading into the SAT solver.
    pub clause_load: Duration,
    /// Theory-atom discovery and deduplication.
    pub theory_atom_scan: Duration,
    /// Variable freezing plus initial theory internalization.
    pub freeze_internalize: Duration,
    /// `TheoryExtension::new()` atom registration and sorting.
    pub extension_register_atoms: Duration,
    /// Bound-axiom generation, materialization, and debug validation.
    pub extension_bound_axioms: Duration,
}

/// Timing breakdown for DPLL(T) solve calls (#4802).
///
/// Follows CaDiCaL's flat struct design (`reference/cadical/src/stats.hpp`)
/// with Z3's hierarchical naming (e.g., `time.spacer.solve.reach`).
/// Accumulates across all solve calls on the same `DpllT` instance.
#[derive(Debug, Clone, Default)]
pub(crate) struct DpllTimings {
    /// Total SAT solver time (`sat.solve()` calls)
    pub sat_solve: Duration,
    /// Total theory sync time (model communication to theory solver)
    pub theory_sync: Duration,
    /// Total theory check time (consistency + propagation checking)
    pub theory_check: Duration,
    /// DPLL(T) round-trip count (SAT → theory → SAT iterations)
    pub round_trips: u64,
}

/// Deterministic eager-extension counters for batching diagnostics.
///
/// Unlike wall-clock timings, these counters are stable across noisy machines
/// and directly measure whether the level-0 batching guard is active on a path.
#[derive(Debug, Clone, Default)]
pub(crate) struct DpllEagerStats {
    /// Number of `propagate()` calls observed by the eager extension.
    pub propagate_calls: u64,
    /// Number of early returns because theory state did not change.
    pub state_unchanged_skips: u64,
    /// Number of inline bound-refinement handoffs from theory to SAT replay.
    pub bound_refinement_handoffs: u64,
    /// Number of deferred theory checks due to batching.
    pub batch_defers: u64,
    /// Number of times batching was otherwise ready but blocked by `sat_level == 0`.
    pub level0_batch_guard_hits: u64,
    /// Number of eager theory checks executed at SAT decision level 0.
    pub level0_checks: u64,
    /// Number of theory lemma clauses injected inline during BCP (#6546).
    pub inline_lemma_clauses: u64,
    /// Number of theory atoms skipped by ITE relevancy filter (#8125).
    pub ite_relevancy_skips: u64,
    /// Number of ITE-deferred atoms kept deferred at final check (#8125 Phase 2).
    /// These atoms remained in inactive ITE branches even at the final
    /// consistency check, so the theory solver never processed them.
    pub ite_deferred_kept: u64,
    /// Number of ITE-deferred atoms flushed at final check (#8003).
    pub ite_deferred_flushed: u64,
    /// Number of times deferred theory mode was activated (#8008).
    pub deferred_mode_activations: u64,
    /// Number of BCP checks skipped due to deferred theory mode (#8008).
    pub deferred_mode_skips: u64,
    /// Number of theory atoms dispatched via the JIT dispatch table (#8177).
    /// Only incremented when the `jit` feature is enabled and the table is active.
    pub jit_dispatch_atoms: u64,
    /// Native theory-bound propagation profiles blocked by the DPLL control plane.
    pub native_theory_prop_disabled: u64,
    /// Native theory-bound propagation profiles rejected as unsupported/partial.
    pub native_theory_prop_unsupported: u64,
    /// Native theory-bound propagation profiles that passed eligibility checks.
    pub native_theory_prop_eligible: u64,
    /// Number of literals removed by theory conflict minimization (#8424).
    pub theory_minimize_lits_removed: u64,
    /// Number of semantic verifications skipped due to sampling on large formulas (#8558).
    pub semantic_verify_budget_skips: u64,
    /// Theory propagations dropped because the propagated term has no SAT
    /// variable in the eager extension (#euf-prop-gap diagnostics).
    pub props_unmapped: u64,
    /// Theory propagations skipped because the literal was already assigned
    /// to the propagated value (#euf-prop-gap diagnostics).
    pub props_already_assigned: u64,
    /// Already-assigned ITE-guarded propagations fed back to the theory to
    /// close the relevancy-deferral blind spot (#euf-prop-gap).
    pub props_fed_back: u64,
    /// Theory propagations converted into SAT propagation clauses.
    pub props_clause_added: u64,
}

impl DpllEagerStats {
    #[inline]
    pub(crate) fn accumulate_from(&mut self, other: &Self) {
        self.propagate_calls += other.propagate_calls;
        self.state_unchanged_skips += other.state_unchanged_skips;
        self.bound_refinement_handoffs += other.bound_refinement_handoffs;
        self.batch_defers += other.batch_defers;
        self.level0_batch_guard_hits += other.level0_batch_guard_hits;
        self.level0_checks += other.level0_checks;
        self.inline_lemma_clauses += other.inline_lemma_clauses;
        self.ite_relevancy_skips += other.ite_relevancy_skips;
        self.ite_deferred_kept += other.ite_deferred_kept;
        self.ite_deferred_flushed += other.ite_deferred_flushed;
        self.deferred_mode_activations += other.deferred_mode_activations;
        self.deferred_mode_skips += other.deferred_mode_skips;
        self.jit_dispatch_atoms += other.jit_dispatch_atoms;
        self.native_theory_prop_disabled += other.native_theory_prop_disabled;
        self.native_theory_prop_unsupported += other.native_theory_prop_unsupported;
        self.native_theory_prop_eligible += other.native_theory_prop_eligible;
        self.theory_minimize_lits_removed += other.theory_minimize_lits_removed;
        self.semantic_verify_budget_skips += other.semantic_verify_budget_skips;
        self.props_unmapped += other.props_unmapped;
        self.props_already_assigned += other.props_already_assigned;
        self.props_fed_back += other.props_fed_back;
        self.props_clause_added += other.props_clause_added;
    }
}

/// Split-loop-local solve timing accumulator.
///
/// Survives repeated fresh `DpllT::from_tseitin*()` rebuilds so the exported
/// `time.dpll.*` counters include every solver instance, not only the last one.
#[derive(Debug, Clone, Default)]
pub(crate) struct SplitLoopTimingStats {
    /// Sum of all DPLL(T) solve-call timings across split-loop rebuilds.
    pub dpll: DpllTimings,
    /// Wall time spent extracting theory models on SAT.
    pub model_extract: Duration,
    /// Wall time spent storing the final result/model back onto the executor.
    pub store_model: Duration,
    /// Total wall time for the entire split loop (#6503).
    pub total: Duration,
}

/// SAT-side state that can be preserved while rebuilding a DPLL(T) wrapper.
///
/// Used by string-theory CEGAR flows that need to mutate the term store
/// (allocate new split/skolem terms) between solver steps without discarding
/// SAT learned clauses and variable assignments.
pub(crate) struct DpllSatState {
    pub(crate) sat: SatSolver,
    pub(crate) var_to_term: HashMap<u32, TermId>,
    pub(crate) term_to_var: HashMap<TermId, u32>,
    pub(crate) theory_atoms: Vec<TermId>,
    pub(crate) theory_atom_set: HashSet<TermId>,
    pub(crate) debug_dpll: bool,
    pub(crate) debug_sync: bool,
    pub(crate) theory_conflict_count: u64,
    pub(crate) theory_propagation_count: u64,
    pub(crate) partial_clause_count: u64,
    pub(crate) theory_unknown_count: u64,
    pub(crate) conflict_max_literals: u64,
    pub(crate) conflict_total_literals: u64,
    /// Number of literals removed by theory conflict minimization (#8424).
    pub(crate) theory_minimize_lits_removed: u64,
    pub(crate) farkas_certificate_failures: u64,
    pub(crate) farkas_certificate_downgrades: u64,
    pub(crate) semantic_verify_budget_skips: u64,
    pub(crate) semantic_verify_sample_counter: u64,
    pub(crate) semantic_verify_warned: bool,
    pub(crate) eager_stats: DpllEagerStats,
    pub(crate) timings: DpllTimings,
    pub(crate) construction_timings: DpllConstructionTimings,
    pub(crate) diagnostic_trace: Option<crate::diagnostic_trace::DpllDiagnosticWriter>,
    pub(crate) dpll_tla_trace: Option<TlaTraceWriter>,
    /// Datatype tautology literals for conflict re-verification (#8123).
    /// Preserved across the into/from_sat_state round-trip so split-solving
    /// paths keep datatype-aware conflict verification.
    pub(crate) dt_verification_axioms: Vec<ay_core::TheoryLit>,
    /// Ground-instance support literals (instances of unconditionally-asserted
    /// Foralls) for conflict re-verification (#AUFLIA-support). Preserved across
    /// the into/from_sat_state round-trip alongside `dt_verification_axioms` so
    /// split-solving paths keep the AUFLIA-support-aware conflict verification.
    pub(crate) ematching_support_axioms: Vec<ay_core::TheoryLit>,
    /// Solve controls (deadline + interrupt) preserved across the
    /// into/from_sat_state round-trip, so a split/CEGAR reconstruction
    /// mid-solve cannot silently shed the executor's wall-clock deadline.
    pub(crate) solve_deadline: Option<Instant>,
    pub(crate) solve_interrupt: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
}

/// Lightweight SAT solver state preserved across CEGAR iterations (#3762).
///
/// When the SLIA CEGAR loop clears its persistent SAT solver (because the
/// assertion set changes between effort passes or pivot candidates), this
/// struct captures high-quality learned clauses, VSIDS activity scores, and
/// phase hints from the prior solve. The next solver instance imports this
/// state to avoid cold-start overhead.
///
/// Unlike `DpllSatState` (which preserves the entire SAT solver), this is
/// a lightweight snapshot designed for cross-solve seeding where the formula
/// structure changes but the variable semantics (term-to-var mapping) are
/// partially shared.
#[derive(Debug, Clone, Default)]
pub struct SatWarmState {
    /// SAT guidance v2 formula fingerprint for learned-clause replay.
    ///
    /// `None` represents legacy v1 warm state: activities and phase hints
    /// remain readable, but learned clauses are not replayed by default.
    pub formula_fingerprint: Option<SatGuidanceFingerprint>,
    /// High-quality learned clauses (LBD <= threshold) from the prior solve.
    /// Stored as literal vectors that can be injected into a fresh solver
    /// via `add_preserved_learned()`.
    pub learned_clauses: Vec<Vec<Literal>>,
    /// VSIDS activity scores from the prior solve, as (var_index, activity).
    /// Used to seed the decision heuristic so the solver prioritizes
    /// variables that were contentious in prior iterations.
    pub variable_activities: Vec<(usize, f64)>,
    /// Phase hints from the prior solve, as (var_index, positive_polarity).
    /// Seeds initial polarities so the solver starts near the prior solution.
    pub phase_hints: Vec<(usize, bool)>,
    /// Number of conflicts in the prior solve. Used for diagnostic logging
    /// to assess how much search effort is being preserved.
    pub prior_conflicts: u64,
}

/// Result of importing a [`SatWarmState`] into a SAT solver.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SatWarmStateImportReport {
    /// SAT guidance compatibility decision used for the import.
    pub decision: SatGuidanceImportDecision,
    /// Number of learned clauses inserted into the fresh solver.
    pub imported_learned_clauses: usize,
    /// Number of variable-activity hints offered to the fresh solver.
    pub variable_activity_hints: usize,
    /// Number of phase hints offered to the fresh solver.
    pub phase_hints: usize,
}

impl SatWarmState {
    /// Maximum LBD for a learned clause to be preserved across CEGAR iterations.
    ///
    /// LBD 1-2 are "glue" clauses (extremely high quality in CaDiCaL/Glucose).
    /// LBD 3-6 are still useful. Above 6, clauses are typically specific to the
    /// search path and unlikely to help a different formula.
    const MAX_PRESERVE_LBD: u32 = 6;

    /// Maximum number of learned clauses to preserve. Caps memory usage
    /// in long CEGAR runs where many high-LBD clauses accumulate.
    const MAX_PRESERVE_CLAUSES: usize = 10_000;

    /// Extract warm state from a SAT solver before it is dropped (#3762).
    pub fn extract(solver: &ay_sat::Solver) -> Self {
        Self {
            formula_fingerprint: Some(solver.guidance_fingerprint()),
            learned_clauses: solver
                .get_learned_clauses_by_quality(Self::MAX_PRESERVE_LBD, Self::MAX_PRESERVE_CLAUSES),
            variable_activities: solver.export_variable_activities(),
            phase_hints: solver.export_phase_hints(),
            prior_conflicts: solver.num_conflicts(),
        }
    }

    /// Import warm state into a fresh SAT solver (#3762, #8935).
    ///
    /// Conditionally injects preserved learned clauses, seeds VSIDS activities,
    /// and sets phase hints. Returns the number of clauses successfully imported.
    pub fn import_into(&self, solver: &mut ay_sat::Solver) -> usize {
        self.import_into_with_report(solver)
            .imported_learned_clauses
    }

    /// Import warm state and return the guidance compatibility decision.
    ///
    /// Learned clauses are imported only when the v2 formula fingerprint proves
    /// exact replay compatibility. Legacy or mismatched warm state is downgraded
    /// to heuristic hints only.
    pub fn import_into_with_report(&self, solver: &mut ay_sat::Solver) -> SatWarmStateImportReport {
        let decision = solver.classify_guidance_import(self.formula_fingerprint.as_ref());
        let mut imported = 0;
        if decision.level.imports_learned_clauses() {
            for clause in &self.learned_clauses {
                if solver.add_preserved_learned(clause.clone()) {
                    imported += 1;
                }
            }
        }
        let import_heuristics = decision.level.imports_heuristic_hints();
        if import_heuristics {
            solver.import_variable_activities(&self.variable_activities);
            solver.import_phase_hints(&self.phase_hints);
        }
        SatWarmStateImportReport {
            decision,
            imported_learned_clauses: imported,
            variable_activity_hints: if import_heuristics {
                self.variable_activities.len()
            } else {
                0
            },
            phase_hints: if import_heuristics {
                self.phase_hints.len()
            } else {
                0
            },
        }
    }

    /// Whether this warm state has any content worth importing.
    pub fn is_empty(&self) -> bool {
        self.learned_clauses.is_empty()
            && self.variable_activities.is_empty()
            && self.phase_hints.is_empty()
    }
}

/// A simple empty theory solver for propositional logic.
pub(crate) struct PropositionalTheory;

impl TheorySolver for PropositionalTheory {
    fn assert_literal(&mut self, _literal: TermId, _value: bool) {
        // No theory reasoning needed
    }

    fn check(&mut self) -> TheoryResult {
        // Propositional logic is always consistent
        TheoryResult::Sat
    }

    fn propagate(&mut self) -> Vec<TheoryPropagation> {
        // No propagations
        vec![]
    }

    fn push(&mut self) {
        // No state to push
    }

    fn pop(&mut self) {
        // No state to pop
    }

    fn reset(&mut self) {
        // Nothing to reset
    }
}
