// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! De-macro'd pipeline helper functions.
//!
//! Home for the ordinary functions extracted from the former `pipeline_*`/
//! `collect_*` `macro_rules!` borrow-workarounds. Each was a macro only to keep
//! disjoint-field borrows lexical at the call site; the functions take the
//! written `Executor`/state fields as separate `&mut` params and read
//! `&mut`-borrowed sources by `Copy` value (never a whole-struct borrow), so the
//! call sites' existing borrows are preserved. The thin `macro_rules!` shims in
//! `pipeline_setup_macros.rs` delegate here.

use std::time::Duration;

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_sat::SatUnknownReason;

use crate::dpll_support::DpllEagerStats;
use crate::executor_types::{SolveResult, Statistics, UnknownReason};

/// Per-SAT-solve conflict allowance (#ground-determinism).
///
/// Diagnostic-only exit-site logger for the split-loop pipeline macros.
///
/// Prints the exit site tag when `AY_DEBUG_SPLIT_EXIT` is set. Used to
/// attribute an `unknown` verdict to the exact give-up point inside the
/// pipeline macros without a debugger. Zero-cost unless the env var is set.
pub(crate) fn debug_split_exit(site: &str) {
    if std::env::var_os("AY_DEBUG_SPLIT_EXIT").is_some() {
        safe_eprintln!("[split-exit] {}", site);
    }
}

/// Field-only free function (takes the two executor fields by `Copy` value)
/// so the pipeline macros can compute it while holding disjoint `&mut`
/// borrows of other executor fields — an `&self` method would borrow the
/// whole struct. An explicit `:rlimit` (`resource_limit`) always wins;
/// otherwise the default ground budget supplies
/// [`crate::executor::Executor::DEFAULT_GROUND_CONFLICT_ALLOWANCE`] unless
/// disabled (`set_ground_budget_enabled(false)` / `:rlimit 0` / the
/// `AY_NO_GROUND_BUDGET` env knob). `None` = no conflict budget.
pub(crate) fn effective_conflict_allowance(
    resource_limit: Option<u64>,
    ground_budget_enabled: bool,
) -> Option<u64> {
    resource_limit.or_else(|| {
        (ground_budget_enabled && !ground_budget_env_disabled())
            .then_some(crate::executor::Executor::DEFAULT_GROUND_CONFLICT_ALLOWANCE)
    })
}

/// Per-SAT-solve decision allowance (#ground-determinism). An explicit
/// decision limit (`Executor::set_decision_limit`) always wins; otherwise the
/// default ground allowance applies while the ground budget is in force. An
/// explicit `:rlimit` (a CONFLICT budget) does not replace it. `None` = no
/// decision budget.
pub(crate) fn effective_decision_allowance(
    decision_limit: Option<u64>,
    ground_budget_enabled: bool,
) -> Option<u64> {
    decision_limit.or_else(|| {
        (ground_budget_enabled && !ground_budget_env_disabled())
            .then_some(crate::executor::Executor::DEFAULT_GROUND_DECISION_ALLOWANCE)
    })
}

/// Process-wide debug opt-out for the default ground budget
/// (`AY_NO_GROUND_BUDGET=1`), cached once. For A/B verdict experiments only —
/// the default path never reads the environment per solve.
pub(crate) fn ground_budget_env_disabled() -> bool {
    static DISABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *DISABLED.get_or_init(|| std::env::var_os("AY_NO_GROUND_BUDGET").is_some())
}

/// SAT-solver statistics snapshot, taken from the SAT solver by value so the
/// caller may hold a disjoint `&mut` borrow of that same solver while these are
/// read (#4622). All fields are `Copy`.
#[derive(Debug, Clone, Copy)]
pub(crate) struct SatStatsSnapshot {
    pub conflicts: u64,
    pub decisions: u64,
    pub propagations: u64,
    pub restarts: u64,
    pub learned_clauses: u64,
    pub deleted_clauses: u64,
    pub num_vars: u64,
    pub num_clauses: u64,
    pub unknown_reason: Option<SatUnknownReason>,
}

/// Assert top-level arithmetic disequality FACTS into a theory solver
/// (#qf-auflia-fc-diseq-sync).
///
/// The eager split loop feeds theories through the SAT extension, which only
/// forwards atoms that hold live SAT variables. Top-level unit facts like the
/// SMT-COMP storecomm element disequalities `(not (= e_i e_j))` are simplified
/// away by preprocessing, so the theory instance at the final check has seen
/// only a small synced subset (measured: ~50 of ~3000 on
/// storeinv_invalid_t3_pp) — its model can then freely violate the invisible
/// facts, and only the fail-closed validation gate catches it (degrading a
/// genuine `sat` to `unknown`). Re-asserting the facts here is sound: they are
/// unconditional top-level assertions, so they hold in every model. With them
/// visible, LIA's disequality check/repair machinery enforces distinct values
/// (or requests the splits) BEFORE the model is accepted.
///
/// Returns the number of facts asserted. (The former `AY_FC_DISEQ_SYNC=0`
/// kill switch is removed; the sync is always on.)
pub(crate) fn assert_top_level_arith_diseq_facts<T: ay_core::TheorySolver>(
    terms: &ay_core::TermStore,
    assertions: &[ay_core::TermId],
    theory: &mut T,
) -> usize {
    use ay_core::term::TermData;
    use ay_core::Sort;
    const MAX_FACTS: usize = 20_000;
    let is_arith = |t: ay_core::TermId| matches!(terms.sort(t), Sort::Int | Sort::Real);
    let mut asserted = 0usize;
    let dbg_sync = std::env::var_os("AY_DEBUG_FC_SYNC").is_some();
    for &a in assertions {
        if asserted >= MAX_FACTS {
            break;
        }
        match terms.get(a) {
            TermData::Not(inner) => {
                if let TermData::App(sym, args) = terms.get(*inner) {
                    if dbg_sync {
                        let sorts: Vec<String> = args
                            .iter()
                            .map(|&x| format!("{:?}|{:?}", terms.sort(x), terms.get(x)))
                            .collect();
                        eprintln!(
                            "[fc-diseq-sync]   not({} {:?})",
                            sym.name(),
                            sorts
                                .iter()
                                .map(|x| &x[..x.len().min(60)])
                                .collect::<Vec<_>>()
                        );
                    }
                    if sym.name() == "=" && args.len() == 2 && args.iter().copied().all(is_arith) {
                        // Assert the INNER equality atom with value=false —
                        // the shape theory solvers receive from the SAT
                        // extension (atoms map to SAT vars; polarity is the
                        // assignment). A Not-wrapped term with value=true is
                        // silently skipped by LIA's atom parser.
                        theory.assert_literal(*inner, false);
                        asserted += 1;
                    }
                }
            }
            TermData::App(sym, args)
                if sym.name() == "distinct"
                    && args.len() >= 2
                    && args.iter().copied().all(is_arith) =>
            {
                theory.assert_literal(a, true);
                asserted += 1;
            }
            // Positive top-level arithmetic EQUALITY facts have the same
            // delta-sync visibility gap: without them the round's LIA never
            // asserts the defining row (e.g. '(= e_0 (select a2 i1))'), its
            // model values the two sides independently, and the emitted model
            // violates the definition (the storecomm/storeinv _pp_ family's
            // root defect after all downstream repairs). Same soundness
            // argument as the disequalities: top-level facts hold in every
            // model.
            TermData::App(sym, args)
                if sym.name() == "=" && args.len() == 2 && args.iter().copied().all(is_arith) =>
            {
                theory.assert_literal(a, true);
                asserted += 1;
            }
            _ => {}
        }
    }
    if dbg_sync {
        eprintln!(
            "[fc-diseq-sync] assertions={} facts_asserted={}",
            assertions.len(),
            asserted
        );
    }
    asserted
}

/// Collect the Int variables appearing in top-level arithmetic disequality
/// facts (the companion of [`assert_top_level_arith_diseq_facts`]) — used to
/// protect their tableau values from substitution-recovery overwrites at model
/// extraction (#qf-auflia-subst-clobber).
pub(crate) fn collect_top_level_arith_diseq_vars(
    terms: &ay_core::TermStore,
    assertions: &[ay_core::TermId],
) -> ay_core::kani_compat::DetHashSet<ay_core::TermId> {
    use ay_core::term::TermData;
    use ay_core::Sort;
    let is_arith_var = |t: ay_core::TermId| {
        matches!(terms.sort(t), Sort::Int | Sort::Real)
            && matches!(terms.get(t), TermData::Var(_, _))
    };
    let mut out = ay_core::kani_compat::det_hash_set_new();
    for &a in assertions {
        match terms.get(a) {
            TermData::Not(inner) => {
                if let TermData::App(sym, args) = terms.get(*inner) {
                    if sym.name() == "=" && args.len() == 2 {
                        for &x in args {
                            if is_arith_var(x) {
                                out.insert(x);
                            }
                        }
                    }
                }
            }
            TermData::App(sym, args) if sym.name() == "distinct" => {
                for &x in args {
                    if is_arith_var(x) {
                        out.insert(x);
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// Collect SAT-level statistics and record the SAT-side unknown reason (#4622).
///
/// De-macro'd from the former `collect_sat_stats!`. Takes the SAT counters and
/// unknown reason BY VALUE (via [`SatStatsSnapshot`]) rather than `&solver`, so
/// call sites that hold a disjoint `&mut` borrow of the SAT solver still compile;
/// the `collect_sat_stats!` shim calls the by-value getters before delegating
/// here. This is a write-only snapshot with NO assertions: phase-ambiguous
/// `debug_assert!`s here would expand at 28+ sites and panic (#4756, #4804); the
/// consistency check stays in `collect_theory_stats_incremental` after both SAT
/// and theory counters are set.
pub(crate) fn collect_sat_stats_snapshot(
    stats: &mut Statistics,
    pending_sat_unknown_reason: &mut Option<SatUnknownReason>,
    snapshot: SatStatsSnapshot,
) {
    stats.conflicts = snapshot.conflicts;
    stats.decisions = snapshot.decisions;
    stats.propagations = snapshot.propagations;
    stats.restarts = snapshot.restarts;
    stats.learned_clauses = snapshot.learned_clauses;
    stats.deleted_clauses = snapshot.deleted_clauses;
    stats.num_vars = snapshot.num_vars;
    stats.num_clauses = snapshot.num_clauses;
    *pending_sat_unknown_reason = snapshot.unknown_reason;
}

/// Copy snapshot of the u64 observability counters read from a `DpllT`
/// instance. Built inline in the `collect_observability_stats_from_dpll!`
/// shim from disjoint by-value getter calls so the function never holds a
/// whole-struct borrow of the `DpllT` (avoids E0502 at the call sites where
/// `dpll` is independently `&mut`-borrowed). See #8165.
#[derive(Clone, Copy)]
pub(crate) struct DpllObservabilityStats {
    pub theory_unknown_count: u64,
    pub partial_clause_count: u64,
    pub conflict_max_literals: u64,
    pub conflict_total_literals: u64,
    pub theory_minimize_lits_removed: u64,
    pub farkas_certificate_failures: u64,
    pub farkas_certificate_downgrades: u64,
    pub semantic_verify_budget_skips: u64,
    pub sync_atoms_asserted: u64,
    pub sync_skipped_identical: u64,
    pub sync_delta_changed: u64,
    pub sync_delta_unchanged: u64,
}

/// Collect theory observability statistics from a `DpllT` instance (#8165).
///
/// Function form of the `collect_observability_stats_from_dpll!` macro. The
/// shim gathers the Copy counter snapshot and the theory-specific stats vector
/// by value (the latter via `TheorySolver::collect_statistics`), so this fn
/// only borrows `last_statistics` mutably and never the `DpllT`/executor whole.
pub(crate) fn collect_observability_stats_from_dpll(
    last_statistics: &mut Statistics,
    counters: DpllObservabilityStats,
    theory_stats: Vec<(&'static str, u64)>,
) {
    last_statistics.theory_unknown_count = counters.theory_unknown_count;
    last_statistics.partial_clause_count = counters.partial_clause_count;
    last_statistics.conflict_max_literals = counters.conflict_max_literals;
    last_statistics.conflict_total_literals = counters.conflict_total_literals;
    last_statistics.theory_minimize_lits_removed = counters.theory_minimize_lits_removed;
    last_statistics.farkas_certificate_failures = counters.farkas_certificate_failures;
    last_statistics.farkas_certificate_downgrades = counters.farkas_certificate_downgrades;
    last_statistics.semantic_verify_budget_skips = counters.semantic_verify_budget_skips;
    // #2138: Incremental theory sync observability stats.
    last_statistics.set_int("dpll.sync_atoms_asserted", counters.sync_atoms_asserted);
    last_statistics.set_int(
        "dpll.sync_skipped_identical",
        counters.sync_skipped_identical,
    );
    last_statistics.set_int("dpll.sync_delta_changed", counters.sync_delta_changed);
    last_statistics.set_int("dpll.sync_delta_unchanged", counters.sync_delta_unchanged);
    // Collect N-O and other theory-specific stats via the trait method.
    for (name, value) in theory_stats {
        last_statistics.set_int(name, value);
    }
}

pub(crate) fn collect_observability_stats_from_theory(
    last_statistics: &mut Statistics,
    theory_stats: &[(&'static str, u64)],
) {
    for (name, value) in theory_stats {
        match *name {
            "nelson_oppen_rounds" => last_statistics.nelson_oppen_rounds = *value,
            "nelson_oppen_max_rounds" => last_statistics.nelson_oppen_max_rounds = *value,
            "equalities_propagated_to_euf" => {
                last_statistics.equalities_propagated_to_euf = *value;
            }
            "equalities_propagated_to_arith" => {
                last_statistics.equalities_propagated_to_arith = *value;
            }
            _ => {
                last_statistics.set_int(name, *value);
            }
        }
    }
}

/// Rebind a fresh LRA checker's positional certificate to the bound axiom's
/// solver-visible clause order. The checker is free to return its conflict
/// literals in tableau order, which need not match `(t1, t2)`.
pub(crate) fn rebind_bound_axiom_farkas(
    conflict: ay_core::TheoryConflict,
    asserted_negations: &[(ay_core::TermId, bool)],
) -> Option<ay_core::FarkasAnnotation> {
    use std::collections::{BTreeMap, BTreeSet};

    let farkas = conflict.farkas?;
    if farkas.coefficients.len() != conflict.literals.len() {
        return None;
    }

    let zero = num_rational::Rational64::from(0);
    let mut by_literal = BTreeMap::new();
    for (literal, coefficient) in conflict.literals.iter().zip(&farkas.coefficients) {
        *by_literal
            .entry((literal.term, literal.value))
            .or_insert(zero) += *coefficient;
    }

    let mut seen = BTreeSet::new();
    let mut rebound = Vec::with_capacity(asserted_negations.len());
    for &literal in asserted_negations {
        if seen.insert(literal) {
            rebound.push(by_literal.remove(&literal).unwrap_or(zero));
        } else {
            rebound.push(zero);
        }
    }
    if by_literal.values().any(|coefficient| *coefficient != zero) {
        return None;
    }
    Some(ay_core::FarkasAnnotation::new(rebound))
}

pub(crate) fn pipeline_add_bound_axiom_clauses(
    terms: &mut ay_core::TermStore,
    proof_tracker: &mut crate::proof_tracker::ProofTracker,
    solver: &mut ay_sat::Solver,
    term_to_var: &HashMap<ay_core::TermId, u32>,
    proof_enabled: bool,
    axiom_pairs: &[(ay_core::TermId, bool, ay_core::TermId, bool)],
    farkas_store: &mut [Option<ay_core::FarkasAnnotation>],
    from_cache: bool,
    local_clausification_proofs: &mut Vec<Option<ay_core::ClausificationProof>>,
    local_original_clause_theory_proofs: &mut Vec<Option<ay_core::TheoryLemmaProof>>,
) -> (usize, usize) {
    let mut bac_added = 0usize;
    let mut bac_dropped = 0usize;
    for (ba_i, &(t1, p1, t2, p2)) in axiom_pairs.iter().enumerate() {
        if let (Some(&v1), Some(&v2)) = (term_to_var.get(&t1), term_to_var.get(&t2)) {
            let l1 = if p1 {
                ay_sat::Literal::positive(ay_sat::Variable::new(v1))
            } else {
                ay_sat::Literal::negative(ay_sat::Variable::new(v1))
            };
            let l2 = if p2 {
                ay_sat::Literal::positive(ay_sat::Variable::new(v2))
            } else {
                ay_sat::Literal::negative(ay_sat::Variable::new(v2))
            };
            solver.add_clause(vec![l1, l2]);
            if proof_enabled {
                let clause_terms = vec![
                    if p1 { t1 } else { terms.mk_not(t1) },
                    if p2 { t2 } else { terms.mk_not(t2) },
                ];
                // #8857: On a cache hit, reuse the stored per-pair Farkas
                // certificate instead of re-validating with a fresh
                // LraSolver per pair. On a miss the pair is already a
                // validated tautology (the injection macro ran the
                // #6242/#6564/seed-981 soundness gate), so this check only
                // re-extracts the Farkas certificate for the proof.
                let farkas = if from_cache {
                    farkas_store[ba_i].clone()
                } else {
                    let mut check_lra = ay_lra::LraSolver::new(&*terms);
                    ay_core::TheorySolver::assert_literal(&mut check_lra, t1, !p1);
                    ay_core::TheorySolver::assert_literal(&mut check_lra, t2, !p2);
                    let conflict = match ay_core::TheorySolver::check(&mut check_lra) {
                        ay_core::TheoryResult::UnsatWithFarkas(conflict) => Some(conflict),
                        _ => None,
                    };
                    drop(check_lra);
                    let ba_new_farkas = conflict.and_then(|conflict| {
                        rebind_bound_axiom_farkas(conflict, &[(t1, !p1), (t2, !p2)])
                    });
                    farkas_store[ba_i] = ba_new_farkas.clone();
                    ba_new_farkas
                };
                let kind =
                    crate::theory_inference::infer_theory_lemma_kind_from_clause_terms_and_farkas(
                        &*terms,
                        &clause_terms,
                        farkas.as_ref(),
                    );
                match (&kind, &farkas) {
                    (_, Some(farkas)) => {
                        let _ = proof_tracker.add_theory_lemma_with_farkas_and_kind(
                            clause_terms.clone(),
                            farkas.clone(),
                            kind,
                        );
                    }
                    (ay_core::TheoryLemmaKind::Generic, None) => {
                        let _ = proof_tracker.add_theory_lemma(clause_terms.clone());
                    }
                    (_, None) => {
                        let _ =
                            proof_tracker.add_theory_lemma_with_kind(clause_terms.clone(), kind);
                    }
                }
                local_clausification_proofs.push(None);
                local_original_clause_theory_proofs.push(Some(ay_core::TheoryLemmaProof {
                    clause: clause_terms,
                    kind,
                    farkas,
                    lia: None,
                }));
            }
            bac_added += 1;
        } else {
            bac_dropped += 1;
        }
    }
    (bac_added, bac_dropped)
}

/// Apply pending activation clauses inside a private push scope (#6853).
///
/// De-macro'd from `pipeline_apply_pending_activations!`. The call site holds
/// `solver = &mut state.<sat_field>`, so the macro could not be a method on
/// `state`: it also writes the disjoint `state.clausification_proofs` /
/// `state.original_clause_theory_proofs` fields. The function takes the solver
/// reborrow and each written field as separate `&mut` params (disjoint borrows),
/// plus the pending clauses by shared slice.
///
/// Only the root literal (`.0`) of each pending entry is used here; the depth
/// (`.1`) is ignored because these clauses are added inside the already-open
/// private push scope.
pub(crate) fn apply_pending_activations(
    solver: &mut ay_sat::Solver,
    pending: &[(ay_sat::Literal, usize)],
    proof_enabled: bool,
    clausification_proofs: &mut Vec<Option<ay_core::ClausificationProof>>,
    original_clause_theory_proofs: &mut Vec<Option<ay_core::TheoryLemmaProof>>,
) {
    for &(root, _depth) in pending {
        solver.add_clause(vec![root]);
        if proof_enabled {
            clausification_proofs.push(None);
            original_clause_theory_proofs.push(None);
        }
    }
}

pub(crate) fn apply_pending_activations_immediate(
    solver: &mut ay_sat::Solver,
    pending: &[(ay_sat::Literal, usize)],
    proof_enabled: bool,
    clausification_proofs: &mut Vec<Option<ay_core::ClausificationProof>>,
    original_clause_theory_proofs: &mut Vec<Option<ay_core::TheoryLemmaProof>>,
) {
    for &(root, depth) in pending {
        if depth == 0 {
            solver.add_clause_global(vec![root]);
        } else {
            solver.add_clause_at_scope_depth(vec![root], depth);
        }
        if proof_enabled {
            clausification_proofs.push(None);
            original_clause_theory_proofs.push(None);
        }
    }
}

pub(crate) fn clone_local_proof_ledgers(
    proof_enabled: bool,
    clausification_proofs: &[Option<ay_core::ClausificationProof>],
    original_clause_theory_proofs: &[Option<ay_core::TheoryLemmaProof>],
) -> (
    Vec<Option<ay_core::ClausificationProof>>,
    Vec<Option<ay_core::TheoryLemmaProof>>,
) {
    let local_clausification_proofs = if proof_enabled {
        clausification_proofs.to_vec()
    } else {
        Vec::new()
    };
    let local_original_clause_theory_proofs = if proof_enabled {
        original_clause_theory_proofs.to_vec()
    } else {
        Vec::new()
    };
    (
        local_clausification_proofs,
        local_original_clause_theory_proofs,
    )
}

pub(crate) fn export_split_loop_eager_stats(
    last_statistics: &mut Statistics,
    stats: &DpllEagerStats,
) {
    last_statistics.set_int("dpll.eager.propagate_calls", stats.propagate_calls);
    last_statistics.set_int("dpll.eager.props_unmapped", stats.props_unmapped);
    last_statistics.set_int(
        "dpll.eager.props_already_assigned",
        stats.props_already_assigned,
    );
    last_statistics.set_int("dpll.eager.props_fed_back", stats.props_fed_back);
    last_statistics.set_int("dpll.eager.props_clause_added", stats.props_clause_added);
    last_statistics.set_int(
        "dpll.eager.state_unchanged_skips",
        stats.state_unchanged_skips,
    );
    last_statistics.set_int(
        "dpll.eager.bound_refinement_handoffs",
        stats.bound_refinement_handoffs,
    );
    last_statistics.set_int("dpll.eager.batch_defers", stats.batch_defers);
    last_statistics.set_int(
        "dpll.eager.level0_batch_guard_hits",
        stats.level0_batch_guard_hits,
    );
    last_statistics.set_int("dpll.eager.level0_checks", stats.level0_checks);
    last_statistics.set_int("dpll.eager.ite_relevancy_skips", stats.ite_relevancy_skips);
    last_statistics.set_int("dpll.eager.ite_deferred_kept", stats.ite_deferred_kept);
    last_statistics.set_int(
        "dpll.eager.ite_deferred_flushed",
        stats.ite_deferred_flushed,
    );
    last_statistics.set_int(
        "dpll.eager.deferred_mode_activations",
        stats.deferred_mode_activations,
    );
    last_statistics.set_int("dpll.eager.deferred_mode_skips", stats.deferred_mode_skips);
    last_statistics.set_int("dpll.eager.jit_dispatch_atoms", stats.jit_dispatch_atoms);
    last_statistics.set_int(
        "dpll.eager.native_theory_prop_disabled",
        stats.native_theory_prop_disabled,
    );
    last_statistics.set_int(
        "dpll.eager.native_theory_prop_unsupported",
        stats.native_theory_prop_unsupported,
    );
    last_statistics.set_int(
        "dpll.eager.native_theory_prop_eligible",
        stats.native_theory_prop_eligible,
    );
}

/// Export split-loop solve timing statistics into `stats` (#5814 Packet C).
///
/// De-macro'd from the former `pipeline_export_split_loop_timing_stats!`. Takes
/// the timing counters by value (via [`SplitLoopTimingStatsSnapshot`], all Copy)
/// rather than `&SplitLoopTimingStats`, matching the template used by
/// `collect_theory_stats_incremental`: the shim builds the snapshot from disjoint
/// Copy field reads so no whole-struct borrow is reintroduced. The macro now
/// delegates here, surviving only to capture the private `last_statistics` field.
pub(crate) fn export_split_loop_timing_stats(
    stats: &mut Statistics,
    timing: SplitLoopTimingStatsSnapshot,
) {
    stats.set_float("time.dpll.sat_solve", timing.sat_solve.as_secs_f64());
    stats.set_float("time.dpll.theory_sync", timing.theory_sync.as_secs_f64());
    stats.set_float("time.dpll.theory_check", timing.theory_check.as_secs_f64());
    stats.set_int("dpll.round_trips", timing.round_trips);
    stats.set_float(
        "time.split_loop.model_extract",
        timing.model_extract.as_secs_f64(),
    );
    stats.set_float(
        "time.split_loop.store_model",
        timing.store_model.as_secs_f64(),
    );
    stats.set_float("time.split_loop.total", timing.total.as_secs_f64());
}

/// Flat, `Copy` snapshot of [`crate::dpll_support::SplitLoopTimingStats`] timing
/// fields, taken by value so [`export_split_loop_timing_stats`] never needs a
/// borrow of the source struct (which is only `Clone`, not `Copy`).
#[derive(Debug, Clone, Copy)]
pub(crate) struct SplitLoopTimingStatsSnapshot {
    pub sat_solve: Duration,
    pub theory_sync: Duration,
    pub theory_check: Duration,
    pub round_trips: u64,
    pub model_extract: Duration,
    pub store_model: Duration,
    pub total: Duration,
}

pub(crate) fn reactivate_all_in_scope(
    solver: &mut ay_sat::Solver,
    assertions: &[ay_core::TermId],
    encoded: &HashMap<ay_core::TermId, i32>,
    pending: &[(ay_sat::Literal, usize)],
    proof_enabled: bool,
    clausification_proofs: &mut Vec<Option<ay_core::ClausificationProof>>,
    original_clause_theory_proofs: &mut Vec<Option<ay_core::TheoryLemmaProof>>,
) {
    let mut seen: HashSet<ay_sat::Literal> = pending.iter().map(|&(lit, _)| lit).collect();
    for &assertion in assertions {
        if let Some(&root_lit) = encoded.get(&assertion) {
            let root = crate::cnf_lit_to_sat(root_lit);
            if seen.insert(root) {
                solver.add_clause(vec![root]);
                if proof_enabled {
                    clausification_proofs.push(None);
                    original_clause_theory_proofs.push(None);
                }
            }
        }
    }
}

pub(crate) fn register_proof_context(
    proof_tracker: &mut crate::proof_tracker::ProofTracker,
    proof_enabled: bool,
    tag: &str,
    has_provenance: bool,
    ctx_assertions: &[ay_core::TermId],
    problem_assertions: Vec<ay_core::TermId>,
    assumptions: &[(ay_core::TermId, ay_core::TermId)],
) {
    if !proof_enabled {
        return;
    }
    proof_tracker.set_theory(tag);
    if has_provenance {
        // #6759: inside deferred-postprocessing, register ALL temporary
        // assertions as Assumes so ensure_empty_clause_derivation can resolve
        // through auxiliary constraints (mod/div side conditions, array axioms).
        // Only problem-provenance assertions get h{idx} labels; the demotion
        // pass demotes unlabeled ones to Trust.
        let problem_set: HashSet<ay_core::TermId> = problem_assertions.into_iter().collect();
        for (idx, &assertion) in ctx_assertions.iter().enumerate() {
            let label = if problem_set.contains(&assertion) {
                Some(format!("h{idx}"))
            } else {
                None
            };
            let _ = proof_tracker.add_assumption(assertion, label);
        }
    } else {
        for (idx, assertion) in problem_assertions.into_iter().enumerate() {
            let _ = proof_tracker.add_assumption(assertion, Some(format!("h{idx}")));
        }
    }
    for (idx, &(_preprocessed, original)) in assumptions.iter().enumerate() {
        let _ = proof_tracker.add_assumption(original, Some(format!("ha{idx}")));
    }
}

/// Function form of `pipeline_encode_model_equality!`'s `@impl` arm (#5814).
///
/// Encodes a model equality `(= eq_lhs eq_rhs)` into the incremental SAT
/// solver: ensures the eq atom is Tseitin-encoded, applies phase bias + VSIDS
/// bump, optionally adds the implied-reason lemma, and (for Int/Real sorts)
/// emits the arith_eq_adapter triangle axioms. Pure: no caller control flow.
///
/// Borrow notes: `terms` and `solver` are disjoint mutable borrows at every
/// call site (`solver` comes from `state`/a local, never from `self.ctx`), so
/// passing both `&mut` reintroduces no conflict. The eq pieces are passed by
/// Copy value (`eq_lhs`/`eq_rhs`/`eq_implied`) plus a borrowed reason slice.
#[allow(clippy::too_many_arguments)]
pub(crate) fn encode_model_equality(
    terms: &mut ay_core::TermStore,
    solver: &mut ay_sat::Solver,
    term_to_var: &mut HashMap<ay_core::TermId, u32>,
    var_to_term: &mut HashMap<u32, ay_core::TermId>,
    next_var: &mut u32,
    negations: &mut crate::incremental_proof_cache::IncrementalNegationCache,
    eq_lhs: ay_core::TermId,
    eq_rhs: ay_core::TermId,
    eq_implied: bool,
    eq_reason: &[ay_core::TheoryLit],
    added_model_eqs: Option<&mut HashSet<ay_core::TermId>>,
    theory_opt: Option<&mut dyn ay_core::TheorySolver>,
    emit_arith_triangle: bool,
) {
    let eq_atom = terms.mk_eq_coerce(eq_lhs, eq_rhs);
    // For the dedup variant, triangle clauses are added only on the first
    // request for this eq atom; without a dedup set, always add them.
    let add_triangle_clauses = match added_model_eqs {
        Some(set) => set.insert(eq_atom),
        None => true,
    };

    let eq_var = crate::executor::theories::split_incremental::ensure_incremental_atom_encoded(
        terms,
        solver,
        term_to_var,
        var_to_term,
        next_var,
        negations,
        eq_atom,
    );
    solver.set_var_phase(eq_var, true);
    for _ in 0..20 {
        solver.bump_variable_activity(eq_var);
    }

    if eq_implied && !eq_reason.is_empty() {
        let mut implied_clause = Vec::with_capacity(eq_reason.len() + 1);
        let mut unmapped_implied_reason = false;
        for reason_lit in eq_reason {
            let Some(&reason_var) = term_to_var.get(&reason_lit.term) else {
                unmapped_implied_reason = true;
                break;
            };
            let reason_var = ay_sat::Variable::new(reason_var);
            implied_clause.push(if reason_lit.value {
                ay_sat::Literal::negative(reason_var)
            } else {
                ay_sat::Literal::positive(reason_var)
            });
        }
        if !unmapped_implied_reason {
            implied_clause.push(ay_sat::Literal::positive(eq_var));
            // ORIGINAL ledger (#lemma-wipe class, extends 4d4a297b): the
            // implied-equality coupling must survive destructive rebuilds —
            // the ModelEqualityTracker/seen-request dedups never re-add, and
            // the stale checks downstream treat an already-requested eq as
            // settled ("treat as Sat"), so a wiped learned-tier clause turns
            // into a livelock or an accepted model violating the implication.
            let _ = solver.add_clause(implied_clause);
        }
    }

    // #6846: Triangle axioms for Int/Real model equalities.
    // (= a b) <=> (a <= b) AND (b <= a) (Z3 arith_eq_adapter pattern).
    // #8596: Skip when there is no arithmetic solver (pure ArrayEUF).
    if emit_arith_triangle && matches!(terms.sort(eq_lhs), ay_core::Sort::Int | ay_core::Sort::Real)
    {
        let le_atom = terms.mk_le(eq_lhs, eq_rhs);
        let ge_atom = terms.mk_le(eq_rhs, eq_lhs);

        let le_var = crate::executor::theories::split_incremental::ensure_incremental_atom_encoded(
            terms,
            solver,
            term_to_var,
            var_to_term,
            next_var,
            negations,
            le_atom,
        );
        let ge_var = crate::executor::theories::split_incremental::ensure_incremental_atom_encoded(
            terms,
            solver,
            term_to_var,
            var_to_term,
            next_var,
            negations,
            ge_atom,
        );

        if add_triangle_clauses {
            // ORIGINAL ledger (#lemma-wipe class): the triangle axioms are
            // added once per eq atom (added_model_eqs dedup) and every
            // downstream stale check assumes they stay present — see the
            // implied-clause note above.
            let _ = solver.add_clause(vec![
                ay_sat::Literal::negative(eq_var),
                ay_sat::Literal::positive(le_var),
            ]);
            let _ = solver.add_clause(vec![
                ay_sat::Literal::negative(eq_var),
                ay_sat::Literal::positive(ge_var),
            ]);
            let _ = solver.add_clause(vec![
                ay_sat::Literal::negative(le_var),
                ay_sat::Literal::negative(ge_var),
                ay_sat::Literal::positive(eq_var),
            ]);
        }

        // #8254: theory variant currently unused; retained for restoration.
        if let Some(theory_ref) = theory_opt {
            ay_core::TheorySolver::register_atom(theory_ref, le_atom);
            ay_core::TheorySolver::register_atom(theory_ref, ge_atom);
            ay_core::TheorySolver::sort_atom_index(theory_ref);
        }

        solver.set_var_phase(le_var, true);
        solver.set_var_phase(ge_var, true);
    }
}

/// Outcome of [`add_incremental_conflict_clause`]: either the blocking clause
/// was added (caller continues its solve loop) or the caller must break out of
/// that loop with the given result. De-macro'd from the control-flow macro
/// `pipeline_add_incremental_conflict_clause!`: the macro's `break Ok(..)` into
/// the caller's loop can't be expressed by a plain function, so the function
/// returns this verdict and the (still-macro) shim performs the actual `break`.
pub(crate) enum AddConflictClauseOutcome {
    /// Clause added (or root-conflict handled); caller proceeds normally.
    Added,
    /// Caller should `break Ok(result)` out of its incremental solve loop.
    Break(SolveResult),
}

/// Convert a verified incremental theory conflict into a SAT blocking clause,
/// pre-minimizing it by removing level-0 (permanently assigned) literals (#8424).
///
/// De-macro'd from `pipeline_add_incremental_conflict_clause!`. Returns
/// [`AddConflictClauseOutcome`] instead of doing caller-loop control flow; the
/// thin shim translates `Break` into the loop's `break Ok(..)`. `solver` and
/// `term_to_var` are disjoint borrows at the call sites (both reborrowed from
/// `state`), and `last_result`/`last_unknown_reason` are separate `&mut` fields
/// of `self`, so no whole-struct borrow is taken.
pub(crate) fn add_incremental_conflict_clause(
    last_result: &mut Option<SolveResult>,
    last_unknown_reason: &mut Option<UnknownReason>,
    solver: &mut ay_sat::Solver,
    term_to_var: &HashMap<ay_core::TermId, u32>,
    conflict_terms: &[ay_core::TheoryLit],
    tag: &str,
    set_unknown_on_error: bool,
    unmapped_message: &str,
) -> AddConflictClauseOutcome {
    let mut clause: Vec<ay_sat::Literal> = conflict_terms
        .iter()
        .filter_map(|t| {
            term_to_var.get(&t.term).map(|&var| {
                if t.value {
                    ay_sat::Literal::negative(ay_sat::Variable::new(var))
                } else {
                    ay_sat::Literal::positive(ay_sat::Variable::new(var))
                }
            })
        })
        .collect();
    if clause.is_empty() {
        if !conflict_terms.is_empty() {
            tracing::warn!(
                tag = tag,
                num_conflict_terms = conflict_terms.len(),
                "{}",
                unmapped_message
            );
            if set_unknown_on_error {
                *last_unknown_reason = Some(UnknownReason::Incomplete);
            }
            *last_result = Some(SolveResult::Unknown);
            return AddConflictClauseOutcome::Break(SolveResult::Unknown);
        }
        *last_result = Some(SolveResult::unsat());
        return AddConflictClauseOutcome::Break(SolveResult::unsat());
    }
    // #8424: Pre-minimize conflict clause with level-0 removal.
    let _minimize_removed =
        crate::theory_inference::minimize_conflict_with_levels(&mut clause, |var| {
            solver.var_level(var)
        });
    if clause.is_empty() {
        // All conflict literals were at level 0 — this is an UNSAT root conflict.
        *last_result = Some(SolveResult::unsat());
        return AddConflictClauseOutcome::Break(SolveResult::unsat());
    }
    solver.add_clause(clause);
    AddConflictClauseOutcome::Added
}

/// Proof data captured for an incremental-split UNSAT exit (#6725): everything
/// the `Executor::last_*` proof fields need, cloned out so the caller can then
/// take `&mut self` for `build_unsat_proof()` without aliasing the solver.
pub(crate) struct CapturedSplitUnsatProof {
    pub clause_trace: Option<ay_sat::ClauseTrace>,
    pub clausification_proofs: Vec<Option<ay_core::ClausificationProof>>,
    pub theory_proofs: Vec<Option<ay_core::TheoryLemmaProof>>,
    pub var_to_term: HashMap<u32, ay_core::TermId>,
    pub negations: HashMap<ay_core::TermId, ay_core::TermId>,
}

/// Capture the proof ledgers for an incremental-split UNSAT exit, resizing the
/// local proof vectors to the clause trace's original-clause count (#6725).
///
/// De-macro'd from the capture half of
/// `pipeline_incremental_split_eager_build_unsat_proof!`. Returns `None` when
/// `proof_enabled` is false. `solver` is only read (so it can be borrowed
/// disjointly from the `&mut self` the shim later needs for `build_unsat_proof`);
/// the shim assigns the returned data to `Executor::last_*` and breaks the loop.
/// Provenance introspection for proof-reconstruction var maps
/// (`AY_PROOF_INTROSPECT=<path>`).
///
/// `var_to_term` is known to cover only a dense PREFIX of the SAT variable
/// space at the CONSUMING end, and any clause mentioning an index above it is
/// discarded wholesale (measured: 97% of trace entries). There are several
/// capture sites, so each one records the map size it stored against the
/// solver's own counts; a site whose `map_len` is far below `num_vars` is the
/// one pairing a stale map with a larger trace.
pub(crate) fn record_var_map_provenance(site: &str, solver: &ay_sat::Solver, map_len: usize) {
    let Some(path) = std::env::var_os("AY_PROOF_INTROSPECT") else {
        return;
    };
    use std::io::Write as _;
    if let Ok(mut fh) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
    {
        let line = format!(
            "VAR_COUNTS site={site} map_len={} user_num_vars={} num_vars={} scope_depth={}\n",
            map_len,
            solver.user_num_vars(),
            <ay_sat::Solver as ay_sat::SolverContext>::num_vars(solver),
            solver.scope_depth(),
        );
        let _ = fh.write_all(line.as_bytes());
    }
}

/// Variant for capture sites where the solver borrow is already released:
/// compares the stored map size against the clause trace it will be paired
/// with, which is the comparison that actually matters for reconstruction.
pub(crate) fn record_var_map_provenance_trace(
    site: &str,
    map_len: usize,
    trace: Option<&ay_sat::ClauseTrace>,
) {
    let Some(path) = std::env::var_os("AY_PROOF_INTROSPECT") else {
        return;
    };
    use std::io::Write as _;
    if let Ok(mut fh) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
    {
        let line = format!(
            "VAR_COUNTS site={site} map_len={} trace_entries={}\n",
            map_len,
            trace.map_or(0, ay_sat::ClauseTrace::len),
        );
        let _ = fh.write_all(line.as_bytes());
    }
}

pub(crate) fn capture_split_unsat_proof(
    solver: &ay_sat::Solver,
    proof_enabled: bool,
    local_var_to_term: &HashMap<u32, ay_core::TermId>,
    local_clausification_proofs: &mut Vec<Option<ay_core::ClausificationProof>>,
    local_theory_proofs: &mut Vec<Option<ay_core::TheoryLemmaProof>>,
    negations: &HashMap<ay_core::TermId, ay_core::TermId>,
) -> Option<CapturedSplitUnsatProof> {
    if !proof_enabled {
        return None;
    }
    let clause_trace = solver.clause_trace().cloned();
    if let Some(ref trace) = clause_trace {
        let original_count = trace.original_clauses().count();
        if local_clausification_proofs.len() < original_count {
            local_clausification_proofs.resize(original_count, None);
        }
        if local_theory_proofs.len() < original_count {
            local_theory_proofs.resize(original_count, None);
        }
    }
    record_var_map_provenance("split_eager", solver, local_var_to_term.len());
    Some(CapturedSplitUnsatProof {
        clause_trace,
        clausification_proofs: local_clausification_proofs.clone(),
        theory_proofs: local_theory_proofs.clone(),
        var_to_term: local_var_to_term.clone(),
        negations: negations.clone(),
    })
}

#[cfg(test)]
mod tests {
    use super::rebind_bound_axiom_farkas;
    use ay_core::{FarkasAnnotation, Sort, TermStore, TheoryConflict, TheoryLit};
    use num_bigint::BigInt;
    use num_rational::Rational64;

    #[test]
    fn bound_axiom_farkas_rebinds_reversed_conflict_order() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let minus_two = terms.mk_int(BigInt::from(-2));
        let two = terms.mk_int(BigInt::from(2));
        let minus_two_x = terms.mk_mul(vec![x, minus_two]);
        let upper = terms.mk_le(minus_two, minus_two_x);
        let lower = terms.mk_le(two, x);
        // The fresh LRA solver may report [lower, upper]. Its coefficients are
        // valid in that order: 1*(2 <= x) + 1/2*(-2 <= -2*x).
        let reversed = TheoryConflict::with_farkas(
            vec![TheoryLit::new(lower, true), TheoryLit::new(upper, true)],
            FarkasAnnotation::new(vec![Rational64::from(1), Rational64::new(1, 2)]),
        );
        let rebound = rebind_bound_axiom_farkas(reversed, &[(upper, true), (lower, true)])
            .expect("same literals in a different order must rebind");

        assert_eq!(
            rebound.coefficients,
            vec![Rational64::new(1, 2), Rational64::from(1)]
        );
        ay_core::proof_validation::verify_farkas_conflict_lits_linear(
            &terms,
            &[TheoryLit::new(upper, true), TheoryLit::new(lower, true)],
            &rebound,
        )
        .expect("rebound coefficients must certify the clause order");
    }
}
