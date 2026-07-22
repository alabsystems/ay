// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

//! Construction, accessors, and bound-axiom generation for `TheoryExtension`.
//!
//! Extracted from `mod.rs` to keep that file under the 1,200-line target.

use std::cell::Cell;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{
    BoundRefinementRequest, FarkasAnnotation, Symbol, TermData, TermId, TermStore, TheoryLemmaKind,
    TheoryLit, TheorySolver,
};
use ay_sat::{Literal, Variable};

use super::{
    BoundRefinementHandoff, NativeTheoryPropagationControl, NativeTheoryPropagationDispatch,
    ProofContext, TheoryAxiomKey, TheoryExtension,
};
use crate::executor::BoundRefinementReplayKey;
use crate::proof_tracker::ProofTracker;
use crate::{DpllConstructionTimings, DpllEagerStats, PhaseTimer};

/// Returns `Some(LraFarkas)` if both terms are arithmetic comparisons and unit
/// Farkas coefficients validate; `None` otherwise.
pub(crate) fn infer_bound_axiom_arith_kind(
    terms: &TermStore,
    t1: TermId,
    t2: TermId,
    p1: bool,
    p2: bool,
) -> Option<TheoryLemmaKind> {
    // Both terms must be binary arithmetic comparisons.
    let is_arith_cmp = |tid: TermId| -> bool {
        matches!(
            terms.get(tid),
            TermData::App(Symbol::Named(name), args)
                if matches!(name.as_str(), "<=" | "<" | ">=" | ">" | "=") && args.len() == 2
        )
    };
    if !is_arith_cmp(t1) || !is_arith_cmp(t2) {
        return None;
    }

    // Validate unit Farkas coefficients against the conflict (negation of clause).
    let conflict_lits = [
        TheoryLit {
            term: t1,
            value: !p1,
        },
        TheoryLit {
            term: t2,
            value: !p2,
        },
    ];
    let unit_farkas = FarkasAnnotation::from_ints(&[1i64, 1]);
    if ay_core::proof_validation::verify_farkas_conflict_lits_full(
        terms,
        &conflict_lits,
        &unit_farkas,
    )
    .is_ok()
    {
        return Some(TheoryLemmaKind::LraFarkas);
    }

    let is_int_arg = |tid: TermId| -> bool {
        match terms.get(tid) {
            TermData::App(Symbol::Named(name), args)
                if matches!(name.as_str(), "<=" | "<" | ">=" | ">" | "=") && args.len() == 2 =>
            {
                matches!(terms.sort(args[0]), ay_core::Sort::Int)
                    || matches!(terms.sort(args[1]), ay_core::Sort::Int)
            }
            _ => false,
        }
    };

    if is_int_arg(t1) || is_int_arg(t2) {
        Some(TheoryLemmaKind::LiaGeneric)
    } else {
        Some(TheoryLemmaKind::LraFarkas)
    }
}

impl<'a, T: TheorySolver> TheoryExtension<'a, T> {
    /// Create a new theory extension wrapper.
    pub(crate) fn new(
        theory: &'a mut T,
        var_to_term: &'a HashMap<u32, TermId>,
        term_to_var: &'a HashMap<TermId, u32>,
        theory_atoms: &'a [TermId],
        theory_atom_set: &'a HashSet<TermId>,
        terms: Option<&'a TermStore>,
        diagnostic_trace: Option<&'a crate::diagnostic_trace::DpllDiagnosticWriter>,
    ) -> Self {
        Self::new_with_construction_timings(
            theory,
            var_to_term,
            term_to_var,
            theory_atoms,
            theory_atom_set,
            terms,
            diagnostic_trace,
            None,
        )
    }

    /// Create a theory extension and optionally accumulate constructor timing.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new_with_construction_timings(
        theory: &'a mut T,
        var_to_term: &'a HashMap<u32, TermId>,
        term_to_var: &'a HashMap<TermId, u32>,
        theory_atoms: &'a [TermId],
        theory_atom_set: &'a HashSet<TermId>,
        terms: Option<&'a TermStore>,
        diagnostic_trace: Option<&'a crate::diagnostic_trace::DpllDiagnosticWriter>,
        construction_timings: Option<&mut DpllConstructionTimings>,
    ) -> Self {
        Self::new_inner(
            theory,
            var_to_term,
            term_to_var,
            theory_atoms,
            theory_atom_set,
            terms,
            diagnostic_trace,
            construction_timings,
            false,
        )
    }

    /// Create a theory extension, skipping the expensive bound axiom
    /// generation and validation when all base axioms are already cached.
    ///
    /// Used by the persistent split-loop on iterations > 0: the axiom set
    /// is unchanged across iterations (only split atoms get added), so
    /// regenerating + revalidating (O(axioms * LRA_solver_creation)) per
    /// iteration is wasteful — `retain_new_axioms()` would filter them all out.
    ///
    /// Atom registration and `sort_atom_index` still run so the theory solver
    /// has a consistent atom index for propagation.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new_skip_bound_axioms(
        theory: &'a mut T,
        var_to_term: &'a HashMap<u32, TermId>,
        term_to_var: &'a HashMap<TermId, u32>,
        theory_atoms: &'a [TermId],
        theory_atom_set: &'a HashSet<TermId>,
        terms: Option<&'a TermStore>,
        diagnostic_trace: Option<&'a crate::diagnostic_trace::DpllDiagnosticWriter>,
    ) -> Self {
        Self::new_inner(
            theory,
            var_to_term,
            term_to_var,
            theory_atoms,
            theory_atom_set,
            terms,
            diagnostic_trace,
            None,
            true,
        )
    }

    /// Create a theory extension reusing precomputed cached data (#8256).
    ///
    /// Skips the expensive O(|terms|) ITE branch guard scan and O(|vars|)
    /// bitset construction that dominate per-iteration overhead on large
    /// QF_LRA formulas. The cached data is extended incrementally if new
    /// SAT variables have been added since the cache was built.
    ///
    /// Always skips bound axiom generation (same as `new_skip_bound_axioms`).
    /// Only registers NEW theory atoms (those added since the previous
    /// iteration by split encoding). `sort_atom_index()` is only called
    /// when new atoms were actually registered. This eliminates ~403K
    /// redundant `register_atom()` calls (707 atoms * 570 iterations) on
    /// benchmarks like simple_startup_7nodes.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new_with_cached_data(
        theory: &'a mut T,
        var_to_term: &'a HashMap<u32, TermId>,
        term_to_var: &'a HashMap<TermId, u32>,
        theory_atoms: &'a [TermId],
        theory_atom_set: &'a HashSet<TermId>,
        cached: &mut super::CachedExtensionData,
    ) -> Self {
        // #8467 capability handshake (#euf-lazy-explain): see new_inner.
        theory.set_lazy_propagation_supported(true);

        // #8256: Only register NEW theory atoms added since the last iteration.
        // In the persistent arm, the theory solver retains all registered atoms
        // across soft_reset_warm() calls. The fast path in register_atom_impl()
        // still does 5-6 HashMap lookups + dirty var reseeding per atom, which
        // for 707 atoms * 570 iterations = ~403K redundant calls. By tracking
        // the previous atom count and only registering the tail, we eliminate
        // this entirely when no new split atoms are added (the common case).
        let prev_count = cached.prev_registered_atom_count;
        let new_atoms = &theory_atoms[prev_count..];
        if !new_atoms.is_empty() {
            for &atom in new_atoms {
                theory.register_atom(atom);
            }
            theory.sort_atom_index();
        }
        cached.prev_registered_atom_count = theory_atoms.len();

        // Extend cached bitsets for any new SAT variables from split encoding.
        cached.extend_for_new_vars(var_to_term, theory_atom_set);

        // #8177: Build JIT dispatch table for O(1) theory atom lookups.
        #[cfg(feature = "jit")]
        let jit_dispatch_table = {
            let mut table = ay_jit::TheoryDispatchTable::new();
            let var_atoms = var_to_term
                .iter()
                .filter(|(_, term_id)| theory_atom_set.contains(*term_id))
                .map(|(&var_id, &term_id)| (var_id, term_id.index() as u32));
            // Collect ITE guards from cached bitset + branch guard arrays.
            let mut ite_guards_for_jit = Vec::new();
            for (&var_id, &term_id) in var_to_term.iter() {
                if !theory_atom_set.contains(&term_id) {
                    continue;
                }
                let idx = var_id as usize;
                let word_idx = idx / 64;
                if word_idx < cached.ite_guarded_bitset.len()
                    && (cached.ite_guarded_bitset[word_idx] >> (idx % 64)) & 1 != 0
                {
                    let (cond_var, is_then) = cached.ite_branch_guards[idx];
                    ite_guards_for_jit.push((var_id, cond_var, is_then));
                }
            }
            table.compile(var_atoms, &ite_guards_for_jit);
            if !table.is_empty() {
                Some(table)
            } else {
                None
            }
        };

        let native_theory_propagation_dispatch = NativeTheoryPropagationDispatch::evaluate(
            theory.native_theory_propagation_profile(),
            theory_atoms.len(),
            NativeTheoryPropagationControl::Disabled,
        );
        let mut eager_stats = DpllEagerStats::default();
        native_theory_propagation_dispatch.record(&mut eager_stats);

        // Dense (sat_var, atom) seed index for bulk phase seeding (see field
        // doc). Rebuilt per construction from the current atom set — cheap
        // relative to the per-decision seeding it accelerates, and the atom set
        // may have grown via split encoding since the cached iteration.
        let seed_index: Vec<(u32, TermId)> = theory_atoms
            .iter()
            .filter_map(|&atom| term_to_var.get(&atom).map(|&sat_var| (sat_var, atom)))
            .collect();

        Self {
            theory,
            terms: None,
            var_to_term,
            term_to_var,
            theory_atoms,
            theory_atom_set,
            last_trail_pos: 0,
            theory_level: 0,
            debug: crate::debug_dpll_enabled(),
            diagnostic_trace: None,
            proof: None,
            theory_conflict_count: 0,
            theory_propagation_count: 0,
            partial_clause_count: 0,
            pending_split: None,
            pending_bound_refinements: Vec::new(),
            level_trail_positions: Vec::new(),
            has_checked: false,
            theory_decision_idx: Cell::new(0),
            pending_axiom_clauses: Vec::new(),
            pending_axiom_terms: Vec::new(),
            pending_axiom_farkas: Vec::new(),
            expr_split_seen_count: 0,
            bound_refinement_handoff: BoundRefinementHandoff::FinalCheckOnly,
            zero_propagation_streak: 0,
            deferred_atom_count: 0,
            eager_stats,
            processed_expr_splits: None,
            theory_var_bitset: std::mem::take(&mut cached.theory_var_bitset),
            seed_index,
            last_seed_epoch: Cell::new(None),
            wander_latched: Cell::new(false),
            wander_phase_clear_pending: Cell::new(false),
            ite_branch_guards: std::mem::take(&mut cached.ite_branch_guards),
            ite_guarded_bitset: std::mem::take(&mut cached.ite_guarded_bitset),
            ite_condition_bitset: std::mem::take(&mut cached.ite_condition_bitset),
            ite_condition_var_to_term: std::mem::take(&mut cached.ite_condition_var_to_term),
            ite_deferred_atoms: Vec::new(),
            can_propagate_scan_pos: Cell::new(0),
            verify_memo: None,
            disable_theory_check: cached.disable_theory_check,
            total_bcp_checks: 0,
            total_bcp_conflicts: 0,
            total_bcp_propagations: 0,
            total_bcp_productive_prop_calls: 0,
            deferred_theory_mode: false,
            consecutive_tiny_conflicts: 0,
            full_trail_deferral_active: false,
            theory_decision_call_count: Cell::new(0),
            pending_theory_atoms_for_batch: Cell::new(0),
            atoms_since_last_check: 0,
            full_state_guard_rejections: 0,
            full_state_guard_checks: 0,
            #[cfg(feature = "jit")]
            jit_dispatch_table,
            native_theory_propagation_dispatch,
            semantic_verify_sample_counter: 0,
            semantic_verify_warned: false,
            semantic_verify_interval: 0,
            verify_euf_cache: None,
            verify_mixed_cache: None,
            verify_array_memo: HashMap::default(),
            verify_array_sem_counter: 0,
            verify_prop_memo: None,
            // Set post-construction by `with_solve_deadline` on the paths that
            // carry the executor's wall-clock budget (CHC/PDR, CLI `:timeout`).
            solve_deadline: None,
            // Set post-construction by `with_support_axioms` from DpllT's combined
            // (dt ++ ematching) conflict-verification support set.
            support_axioms: Vec::new(),
        }
    }

    /// Return the cached extension data (bitsets and ITE guards) for reuse
    /// across split-loop iterations (#8256).
    ///
    /// Takes ownership of the heavy fields via `mem::take`, leaving empty
    /// vecs in self. Must be called before dropping the extension.
    pub(crate) fn take_cached_data(&mut self) -> super::CachedExtensionData {
        super::CachedExtensionData {
            theory_var_bitset: std::mem::take(&mut self.theory_var_bitset),
            ite_branch_guards: std::mem::take(&mut self.ite_branch_guards),
            ite_guarded_bitset: std::mem::take(&mut self.ite_guarded_bitset),
            ite_condition_bitset: std::mem::take(&mut self.ite_condition_bitset),
            ite_condition_var_to_term: std::mem::take(&mut self.ite_condition_var_to_term),
            last_full_rebuild_num_vars: self.var_to_term.len(),
            // Preserve the registered atom count so next iteration knows which
            // atoms are already registered in the persistent theory solver.
            prev_registered_atom_count: self.theory_atoms.len(),
            disable_theory_check: self.disable_theory_check,
        }
    }

    /// Internal constructor shared by `new_with_construction_timings` and
    /// `new_skip_bound_axioms`.
    #[allow(clippy::too_many_arguments)]
    fn new_inner(
        theory: &'a mut T,
        var_to_term: &'a HashMap<u32, TermId>,
        term_to_var: &'a HashMap<TermId, u32>,
        theory_atoms: &'a [TermId],
        theory_atom_set: &'a HashSet<TermId>,
        terms: Option<&'a TermStore>,
        diagnostic_trace: Option<&'a crate::diagnostic_trace::DpllDiagnosticWriter>,
        construction_timings: Option<&mut DpllConstructionTimings>,
        skip_bound_axiom_generation: bool,
    ) -> Self {
        let mut construction_timings = construction_timings;

        // #8467 capability handshake (#euf-lazy-explain): this extension
        // implements the full lazy-justification protocol (reason_data pass-
        // through in propagate_impl, explain_lazy_reason, rejected-propagation
        // notification), so theories may emit lazy propagations here. The
        // legacy DpllT::check_theory loop never declares support, keeping
        // capability-gated theories on eager reasons there.
        theory.set_lazy_propagation_supported(true);

        // Register all theory atoms with the theory solver for bound propagation.
        // This allows the theory to build an index of atoms per variable,
        // enabling same-variable chain propagation (#4919 RC2).
        {
            let _register_timer = construction_timings
                .as_mut()
                .map(|timings| PhaseTimer::new(&mut timings.extension_register_atoms));
            for &atom in theory_atoms {
                theory.register_atom(atom);
            }

            // Sort atom_index before generating bound axioms (#4919).
            theory.sort_atom_index();
        }

        let (pending_axiom_clauses, pending_axiom_terms, pending_axiom_farkas) =
            if skip_bound_axiom_generation || crate::theory_debug_flags::no_bound_axioms() {
                // #8103: Skip bound axiom generation on split-loop iterations > 0.
                // All base axioms were generated on iteration 0 and are already in
                // the SAT solver. retain_new_axioms() would filter them all out.
                // This eliminates O(axioms * LRA_solver_creation) per iteration.
                (Vec::new(), Vec::new(), Vec::new())
            } else {
                let _axiom_timer = construction_timings
                    .as_mut()
                    .map(|timings| PhaseTimer::new(&mut timings.extension_bound_axioms));

                // Generate bound ordering axioms (#4919).
                // Reference: Z3 mk_bound_axioms — encodes bound implications as SAT
                // binary clauses so BCP handles them instead of the theory solver.
                let axiom_term_pairs = theory.generate_bound_axiom_terms();
                let mut pending_axiom_clauses = Vec::with_capacity(axiom_term_pairs.len());
                let mut pending_axiom_terms = Vec::with_capacity(axiom_term_pairs.len());
                let mut pending_axiom_farkas: Vec<Option<FarkasAnnotation>> =
                    Vec::with_capacity(axiom_term_pairs.len());
                for (t1, p1, t2, p2) in axiom_term_pairs {
                    if let (Some(&v1), Some(&v2)) = (term_to_var.get(&t1), term_to_var.get(&t2)) {
                        let l1 = if p1 {
                            Literal::positive(Variable::new(v1))
                        } else {
                            Literal::negative(Variable::new(v1))
                        };
                        let l2 = if p2 {
                            Literal::positive(Variable::new(v2))
                        } else {
                            Literal::negative(Variable::new(v2))
                        };
                        pending_axiom_clauses.push(vec![l1, l2]);
                        pending_axiom_terms.push((t1, p1, t2, p2));
                        pending_axiom_farkas.push(None); // filled during validation below
                    }
                }

                // Validate bound axioms (#6242, #6564): verify each clause
                // (t1^p1 ∨ t2^p2) is a tautology by checking that
                // ¬(t1^p1) ∧ ¬(t2^p2) is UNSAT in a fresh LRA solver. Unsound
                // axioms are removed to prevent false-UNSAT.
                //
                // Previously debug-only; promoted to all builds (#6564) because
                // the axiom generator can produce unsound axioms that cause
                // release-only false-UNSAT. Runs once at construction time;
                // acceptable overhead.
                // #6686: Extract Farkas certificates from the validation check.
                // These are attached to proof steps so carcara can verify
                // `la_generic :args (c1 c2)` on bound-axiom theory lemmas.
                if let Some(terms) = terms {
                    let mut valid_clauses = Vec::with_capacity(pending_axiom_clauses.len());
                    let mut valid_terms = Vec::with_capacity(pending_axiom_terms.len());
                    let mut valid_farkas: Vec<Option<FarkasAnnotation>> =
                        Vec::with_capacity(pending_axiom_terms.len());
                    let mut rejected = 0usize;
                    // Phase 3 Fix 3 (Layer C): reuse ONE validation solver
                    // across all axiom pairs via soft_reset instead of a
                    // fresh LraSolver per pair (#8256 observed 33K fresh
                    // instances on labyrinth-class problems).
                    use ay_core::{TheoryResult, TheorySolver};
                    use ay_lra::LraSolver;
                    let mut check_lra = LraSolver::new(terms);
                    // #certora-axiom-validate-rebuild: the reused validation
                    // solver ACCUMULATES registered atoms/vars/rows across
                    // pairs (soft_reset clears assertions, not structure), so
                    // every per-pair check paid O(accumulated vars) in
                    // implied-bounds overlays and soft_reset paid O(vars) in
                    // value drops — quadratic in the axiom count, and the
                    // dominant construction cost on large Certora QF_UFLIA
                    // files (70% of CPU samples inside this loop). Rebuilding
                    // a fresh solver every N pairs bounds the accumulation at
                    // O(N) while keeping the #8256 fresh-instance churn
                    // amortized to 1/N. Verdicts are unchanged: each pair's
                    // tautology check depends only on its own two asserted
                    // literals (rows from other pairs carry no asserted
                    // bounds), exactly as with the original fresh-per-pair
                    // scheme.
                    const AXIOM_VALIDATION_REBUILD_PERIOD: usize = 256;
                    for (i, (t1, p1, t2, p2)) in pending_axiom_terms.iter().copied().enumerate() {
                        if i > 0 && i % AXIOM_VALIDATION_REBUILD_PERIOD == 0 {
                            check_lra = LraSolver::new(terms);
                        }
                        check_lra.soft_reset();
                        // #8373: abstract non-arithmetic operands (e.g. `select(arr,i)`
                        // array reads inside an Int-sorted bound-axiom pair) as opaque
                        // Nelson-Oppen variables instead of marking them "unsupported"
                        // and downgrading Sat->Unknown (which fell through the `_` arm
                        // below and KEPT the axiom without a Farkas certificate). Opaque
                        // abstraction is a relaxation: a resulting Unsat still implies
                        // real Unsat (kept axiom stays a genuine tautology, now WITH a
                        // cert); a resulting Sat correctly rejects a non-tautological
                        // pair. Mirrors the incremental gate fix in
                        // pipeline_setup_macros.rs. Set after soft_reset so it survives
                        // whatever soft_reset_inner clears.
                        check_lra.set_combined_theory_mode(true);
                        // Assert negation of both literals: if UNSAT, clause is tautology
                        check_lra.assert_literal(t1, !p1);
                        check_lra.assert_literal(t2, !p2);
                        match check_lra.check() {
                            TheoryResult::UnsatWithFarkas(conflict) => {
                                valid_clauses.push(pending_axiom_clauses[i].clone());
                                valid_terms.push((t1, p1, t2, p2));
                                valid_farkas.push(conflict.farkas);
                            }
                            TheoryResult::Unsat(_) => {
                                valid_clauses.push(pending_axiom_clauses[i].clone());
                                valid_terms.push((t1, p1, t2, p2));
                                valid_farkas.push(None);
                            }
                            TheoryResult::Sat => {
                                rejected += 1;
                                tracing::warn!(
                                    term1 = ?t1,
                                    pol1 = p1,
                                    term2 = ?t2,
                                    pol2 = p2,
                                    "Rejected unsound bound axiom (#6242)"
                                );
                            }
                            _ => {
                                valid_clauses.push(pending_axiom_clauses[i].clone());
                                valid_terms.push((t1, p1, t2, p2));
                                valid_farkas.push(None);
                            }
                        }
                    }
                    if rejected > 0 {
                        tracing::warn!(
                            rejected,
                            total = pending_axiom_clauses.len(),
                            valid = valid_clauses.len(),
                            "Removed unsound bound axioms (#6242, #6564)"
                        );
                    }
                    pending_axiom_clauses = valid_clauses;
                    pending_axiom_terms = valid_terms;
                    pending_axiom_farkas = valid_farkas;
                }

                (
                    pending_axiom_clauses,
                    pending_axiom_terms,
                    pending_axiom_farkas,
                )
            };

        if !pending_axiom_clauses.is_empty() {
            tracing::info!(
                bound_axioms = pending_axiom_clauses.len(),
                theory_atoms = theory_atoms.len(),
                "Bound ordering axioms generated (#4919)"
            );
        }

        // Build dense bitset for O(1) theory-variable membership checks.
        // Each bit corresponds to a SAT variable ID. This replaces the
        // double hashmap lookup (var_to_term + theory_atom_set.contains)
        // in the hot trail-scan loop.
        let max_var_id = var_to_term.keys().copied().max().unwrap_or(0) as usize;
        let theory_var_bitset = {
            let num_words = (max_var_id + 64) / 64;
            let mut bitset = vec![0u64; num_words];
            for (&var_id, &term_id) in var_to_term {
                if theory_atom_set.contains(&term_id) {
                    let idx = var_id as usize;
                    bitset[idx / 64] |= 1u64 << (idx % 64);
                }
            }
            bitset
        };

        // Build the dense (sat_var, atom) seed index once. Same lookup the
        // phase-seeding loop used to perform per atom per seed, hoisted to a
        // single pass at construction. Preserving `theory_atoms` order keeps the
        // seed write order identical to the previous per-atom loop.
        let seed_index: Vec<(u32, TermId)> = theory_atoms
            .iter()
            .filter_map(|&atom| term_to_var.get(&atom).map(|&sat_var| (sat_var, atom)))
            .collect();

        // Build ITE relevancy guard map (#8125, #8065).
        // Scan all terms for Boolean ITE nodes `(ite cond then_t else_t)`
        // where `then_t` or `else_t` is a theory atom with a SAT variable.
        // For each such atom, record `(cond_sat_var, is_then_branch)`.
        //
        // This enables the propagator to skip asserting theory atoms from
        // inactive ITE branches during BCP, avoiding O(2^k) simplex overhead
        // on ITE-heavy formulas (sc-*, uart-*, simple_startup-*).
        //
        // #8065 Phase 2: Recursive branch scanning. After ITE lifting, nested
        // ITEs produce trees like `(ite c1 (ite c2 atom1 atom2) atom3)`. The
        // inner ITE's branches are theory atoms guarded by c2. But atom1 is
        // ALSO in the then-branch of the outer ITE (guarded by c1). We now
        // recursively walk Bool-sorted ITE branches to find theory atoms at
        // any depth, assigning the *outermost* guard first. This improves
        // deferral coverage for formulas with deeply nested ITEs.
        //
        // Multi-guard safety: if the same theory atom appears in branches of
        // multiple different ITE nodes (possible via hash-consing), the guard
        // is REMOVED. Keeping only the last-seen guard could cause incorrect
        // deferral when a different ITE's condition selects the atom's branch.
        // The fallback in check_impl() protects soundness, but incorrect
        // deferral during BCP wastes search effort. Clearing the guard avoids
        // this by letting multi-context atoms flow to the theory immediately.
        let num_guard_words = (max_var_id + 64) / 64;
        let mut ite_branch_guards: Vec<(u32, bool)> = vec![(0, false); max_var_id + 1];
        let mut ite_guarded_bitset = vec![0u64; num_guard_words];
        let mut ite_condition_bitset = vec![0u64; num_guard_words];
        let mut ite_condition_var_to_term: HashMap<u32, TermId> = HashMap::default();
        if let Some(term_store) = terms {
            // Helper: set or conflict-clear the guard for a branch atom.
            // Extracted as a standalone fn to allow recursive calls from
            // collect_branch_atoms without borrow conflicts.
            fn set_guard(
                ite_branch_guards: &mut [(u32, bool)],
                ite_guarded_bitset: &mut [u64],
                sat_var: u32,
                cond_id: u32,
                is_then: bool,
            ) {
                let idx = sat_var as usize;
                if idx >= ite_branch_guards.len() {
                    return;
                }
                let word_idx = idx / 64;
                let bit = 1u64 << (idx % 64);
                if word_idx < ite_guarded_bitset.len() && (ite_guarded_bitset[word_idx] & bit) != 0
                {
                    let (existing_cond, existing_branch) = ite_branch_guards[idx];
                    if existing_cond != cond_id || existing_branch != is_then {
                        // Conflicting guard: remove to prevent incorrect deferral.
                        ite_guarded_bitset[word_idx] &= !bit;
                    }
                } else if word_idx < ite_guarded_bitset.len() {
                    ite_branch_guards[idx] = (cond_id, is_then);
                    ite_guarded_bitset[word_idx] |= bit;
                }
            }

            /// Recursively collect theory atoms from a Bool-sorted ITE branch.
            /// Depth-limited to 8 levels to prevent pathological nesting.
            fn collect_branch_atoms(
                term_store: &TermStore,
                term_to_var: &HashMap<TermId, u32>,
                theory_atom_set: &HashSet<TermId>,
                ite_branch_guards: &mut [(u32, bool)],
                ite_guarded_bitset: &mut [u64],
                branch: &TermId,
                cond_sat_var: u32,
                is_then: bool,
                depth: u8,
            ) {
                if let Some(&sat_var) = term_to_var.get(branch) {
                    if theory_atom_set.contains(branch) {
                        set_guard(
                            ite_branch_guards,
                            ite_guarded_bitset,
                            sat_var,
                            cond_sat_var,
                            is_then,
                        );
                        return;
                    }
                }
                if depth < 8 {
                    if let TermData::Ite(_nested_cond, nested_then, nested_else) =
                        term_store.get(*branch)
                    {
                        if term_store.sort(*branch) == &ay_core::Sort::Bool {
                            collect_branch_atoms(
                                term_store,
                                term_to_var,
                                theory_atom_set,
                                ite_branch_guards,
                                ite_guarded_bitset,
                                nested_then,
                                cond_sat_var,
                                is_then,
                                depth + 1,
                            );
                            collect_branch_atoms(
                                term_store,
                                term_to_var,
                                theory_atom_set,
                                ite_branch_guards,
                                ite_guarded_bitset,
                                nested_else,
                                cond_sat_var,
                                is_then,
                                depth + 1,
                            );
                        }
                    }
                }
            }

            for term_id in term_store.term_ids() {
                if let TermData::Ite(cond, then_t, else_t) = term_store.get(term_id) {
                    // #8373: Resolve the ITE condition to a SAT variable,
                    // unwrapping Not if needed. For `(ite (not x_0) ...)`, the
                    // condition `(not x_0)` doesn't have its own SAT variable —
                    // it shares x_0's variable. We need to mark the INNER
                    // variable (x_0) in ite_condition_bitset so its assignment
                    // is forwarded to the theory. LRA's parse_linear_expr
                    // handles Not-wrapped conditions by checking
                    // asserted.get(inner).
                    // Resolve condition to (sat_var, term_to_forward, negated).
                    // For `(ite cond ...)`: sat_var = term_to_var[cond], term = *cond
                    // For `(ite (not x) ...)`: sat_var = term_to_var[x], term = x
                    //   (LRA's parse_linear_expr has a Not-fallback)
                    //
                    // SOUNDNESS (#919-class branch-deferral bug): when the
                    // condition is `(not x)`, the guard's SAT variable is `x`,
                    // but the branch-deferral test reads the RAW value of `x`
                    // and compares it to the stored `is_then_branch`. The raw
                    // value of `x` is the negation of the actual condition
                    // `(not x)`. If we recorded `is_then`/`is_else` relative to
                    // the original condition `(not x)`, the runtime test would
                    // be inverted and defer the *selected* branch's theory atom
                    // (dropping the active arithmetic constraint and yielding a
                    // false SAT, e.g. gasburner-prop3-7). We therefore track
                    // `cond_negated` and flip the branch polarity below so the
                    // stored `is_then_branch` always means "this branch is
                    // active when value(cond_sat_var) == is_then_branch".
                    let (cond_sat_var, cond_term_to_forward, cond_negated) =
                        if let Some(&sv) = term_to_var.get(cond) {
                            (sv, *cond, false)
                        } else if let TermData::Not(inner) = term_store.get(*cond) {
                            if let Some(&sv) = term_to_var.get(inner) {
                                (sv, *inner, true)
                            } else {
                                continue;
                            }
                        } else {
                            continue;
                        };
                    // #8003: Mark condition variable for prioritized decision.
                    // #8373: Mark condition for ALL ITEs (not just Bool-sorted),
                    // so that Boolean ITE conditions used in arithmetic-sorted
                    // ITEs like `(ite x_0 0.0 x_2)` are forwarded to the theory.
                    // Without this, LRA's parse_linear_expr cannot resolve the
                    // ITE condition and over-approximates as a fresh variable.
                    let cond_idx = cond_sat_var as usize;
                    let cond_word = cond_idx / 64;
                    if cond_word < ite_condition_bitset.len() {
                        ite_condition_bitset[cond_word] |= 1u64 << (cond_idx % 64);
                    }
                    // #8003: Record the condition's TermId for forwarding in
                    // propagation. Only needed for non-theory-atom conditions
                    // that aren't in var_to_term (e.g., xor, and, or used as
                    // ITE conditions in arithmetic).
                    if !var_to_term.contains_key(&cond_sat_var) {
                        ite_condition_var_to_term.insert(cond_sat_var, cond_term_to_forward);
                    }

                    // ITE branch guard analysis only applies to Bool-sorted ITEs
                    // where the branches are theory atoms that can be deferred.
                    if term_store.sort(term_id) != &ay_core::Sort::Bool {
                        continue;
                    }

                    // The then-branch is active when the actual condition is
                    // true; the else-branch when it is false. Express both in
                    // terms of the RAW guard variable value: if the condition
                    // is `(not x)`, the raw value of `x` is inverted relative
                    // to the condition, so flip the branch polarities.
                    let then_active_value = !cond_negated;
                    let else_active_value = cond_negated;
                    collect_branch_atoms(
                        term_store,
                        term_to_var,
                        theory_atom_set,
                        &mut ite_branch_guards,
                        &mut ite_guarded_bitset,
                        then_t,
                        cond_sat_var,
                        then_active_value,
                        0,
                    );
                    collect_branch_atoms(
                        term_store,
                        term_to_var,
                        theory_atom_set,
                        &mut ite_branch_guards,
                        &mut ite_guarded_bitset,
                        else_t,
                        cond_sat_var,
                        else_active_value,
                        0,
                    );
                }
            }
        }

        // #8177: Build JIT dispatch table for O(1) theory atom lookups.
        #[cfg(feature = "jit")]
        let jit_dispatch_table = {
            let mut table = ay_jit::TheoryDispatchTable::new();
            let var_atoms = var_to_term
                .iter()
                .filter(|(_, term_id)| theory_atom_set.contains(*term_id))
                .map(|(&var_id, &term_id)| (var_id, term_id.index() as u32));
            // Collect ITE guards from the bitset + branch guard arrays.
            let mut ite_guards_for_jit = Vec::new();
            for (&var_id, &term_id) in var_to_term {
                if !theory_atom_set.contains(&term_id) {
                    continue;
                }
                let idx = var_id as usize;
                let word_idx = idx / 64;
                if word_idx < ite_guarded_bitset.len()
                    && (ite_guarded_bitset[word_idx] >> (idx % 64)) & 1 != 0
                {
                    let (cond_var, is_then) = ite_branch_guards[idx];
                    ite_guards_for_jit.push((var_id, cond_var, is_then));
                }
            }
            table.compile(var_atoms, &ite_guards_for_jit);
            if !table.is_empty() {
                Some(table)
            } else {
                None
            }
        };

        let native_theory_propagation_dispatch = NativeTheoryPropagationDispatch::evaluate(
            theory.native_theory_propagation_profile(),
            theory_atoms.len(),
            NativeTheoryPropagationControl::Disabled,
        );
        let mut eager_stats = DpllEagerStats::default();
        native_theory_propagation_dispatch.record(&mut eager_stats);

        Self {
            theory,
            terms,
            var_to_term,
            term_to_var,
            theory_atoms,
            theory_atom_set,
            last_trail_pos: 0,
            theory_level: 0,
            debug: crate::debug_dpll_enabled(),
            diagnostic_trace,
            proof: None,
            theory_conflict_count: 0,
            theory_propagation_count: 0,
            partial_clause_count: 0,
            pending_split: None,
            pending_bound_refinements: Vec::new(),
            level_trail_positions: Vec::new(),
            has_checked: false,
            theory_decision_idx: Cell::new(0),
            pending_axiom_clauses,
            pending_axiom_terms,
            pending_axiom_farkas,
            expr_split_seen_count: 0,
            bound_refinement_handoff: BoundRefinementHandoff::FinalCheckOnly,
            zero_propagation_streak: 0,
            deferred_atom_count: 0,
            eager_stats,
            processed_expr_splits: None,
            theory_var_bitset,
            seed_index,
            last_seed_epoch: Cell::new(None),
            wander_latched: Cell::new(false),
            wander_phase_clear_pending: Cell::new(false),
            ite_branch_guards,
            ite_guarded_bitset,
            ite_condition_bitset,
            ite_condition_var_to_term,
            ite_deferred_atoms: Vec::new(),
            can_propagate_scan_pos: Cell::new(0),
            verify_memo: None,
            disable_theory_check: crate::theory_debug_flags::disable_theory_check(),
            total_bcp_checks: 0,
            total_bcp_conflicts: 0,
            total_bcp_propagations: 0,
            total_bcp_productive_prop_calls: 0,
            deferred_theory_mode: false,
            consecutive_tiny_conflicts: 0,
            full_trail_deferral_active: false,
            theory_decision_call_count: Cell::new(0),
            pending_theory_atoms_for_batch: Cell::new(0),
            atoms_since_last_check: 0,
            full_state_guard_rejections: 0,
            full_state_guard_checks: 0,
            #[cfg(feature = "jit")]
            jit_dispatch_table,
            native_theory_propagation_dispatch,
            semantic_verify_sample_counter: 0,
            semantic_verify_warned: false,
            semantic_verify_interval: 0,
            verify_euf_cache: None,
            verify_mixed_cache: None,
            verify_array_memo: HashMap::default(),
            verify_array_sem_counter: 0,
            verify_prop_memo: None,
            // Set post-construction by `with_solve_deadline` on the paths that
            // carry the executor's wall-clock budget (CHC/PDR, CLI `:timeout`).
            solve_deadline: None,
            // Set post-construction by `with_support_axioms` from DpllT's combined
            // (dt ++ ematching) conflict-verification support set.
            support_axioms: Vec::new(),
        }
    }

    /// Number of theory conflicts encountered during eager solving (#4705).
    #[must_use]
    pub(crate) fn num_theory_conflicts(&self) -> u64 {
        self.theory_conflict_count
    }

    /// Number of theory propagation clauses added during eager solving (#4705).
    #[must_use]
    pub(crate) fn num_theory_propagations(&self) -> u64 {
        self.theory_propagation_count
    }

    /// Number of partial clause events where `term_to_literal` dropped terms (#5000).
    #[must_use]
    pub(crate) fn num_partial_clauses(&self) -> u64 {
        self.partial_clause_count
    }

    /// Deterministic eager-extension counters accumulated on this instance.
    #[must_use]
    pub(crate) fn eager_stats(&self) -> &DpllEagerStats {
        &self.eager_stats
    }

    /// Drop already-added bound axioms when the eager split loop reuses the
    /// same SAT solver across fresh theory-extension instances.
    /// Snapshot the generated-and-validated bound axiom pairs and their
    /// Farkas certificates for the per-Executor bound-axiom cache
    /// (Fix 3 Layer A, #8857). Must be called before the pending axioms are
    /// consumed by `propagate()` / filtered by `retain_new_axioms()`.
    pub(crate) fn pending_axiom_snapshot(
        &self,
    ) -> (
        Vec<(TermId, bool, TermId, bool)>,
        Vec<Option<FarkasAnnotation>>,
    ) {
        (
            self.pending_axiom_terms.clone(),
            self.pending_axiom_farkas.clone(),
        )
    }

    pub(crate) fn retain_new_axioms(&mut self, seen_axioms: &mut HashSet<TheoryAxiomKey>) {
        if self.pending_axiom_terms.is_empty() {
            return;
        }

        let mut new_clauses = Vec::with_capacity(self.pending_axiom_clauses.len());
        let mut new_terms = Vec::with_capacity(self.pending_axiom_terms.len());
        let mut new_farkas = Vec::with_capacity(self.pending_axiom_farkas.len());
        for ((clause, (t1, p1, t2, p2)), farkas) in self
            .pending_axiom_clauses
            .drain(..)
            .zip(self.pending_axiom_terms.drain(..))
            .zip(self.pending_axiom_farkas.drain(..))
        {
            if seen_axioms.insert(TheoryAxiomKey::new(t1, p1, t2, p2)) {
                new_clauses.push(clause);
                new_terms.push((t1, p1, t2, p2));
                new_farkas.push(farkas);
            }
        }
        self.pending_axiom_clauses = new_clauses;
        self.pending_axiom_terms = new_terms;
        self.pending_axiom_farkas = new_farkas;
    }

    /// Take a pending split/lemma request stored during eager solving (#4919).
    /// Returns `None` if no split was requested.
    pub(crate) fn take_pending_split(&mut self) -> Option<ay_core::TheoryResult> {
        self.pending_split.take()
    }

    pub(crate) fn take_pending_bound_refinements(&mut self) -> Vec<BoundRefinementRequest> {
        std::mem::take(&mut self.pending_bound_refinements)
    }

    pub(super) fn record_pending_bound_refinements(
        &mut self,
        refinements: Vec<BoundRefinementRequest>,
    ) {
        for refinement in refinements {
            if !self.pending_bound_refinements.contains(&refinement) {
                self.pending_bound_refinements.push(refinement);
            }
        }
    }

    pub(crate) fn with_proof_tracking(
        mut self,
        tracker: &'a mut ProofTracker,
        negations: &'a HashMap<TermId, TermId>,
    ) -> Self {
        self.proof = Some(ProofContext { tracker, negations });
        self
    }

    /// Set the initial trail position for the extension (#8256).
    ///
    /// When using `continue_solving_with_extension()` after a budget-exhausted
    /// iteration, the theory solver already has all assertions from the
    /// previous iteration. Setting the trail position to the SAT solver's
    /// current trail length prevents the extension from replaying the entire
    /// trail through the theory solver, eliminating O(trail_length) per-atom
    /// assertion overhead per budget-exhausted continuation.
    ///
    /// Also sets `has_checked = true` so the extension doesn't force an
    /// unnecessary initial theory check, and `theory_level` to the current
    /// SAT decision level so no spurious push() calls are made.
    ///
    /// On backtrack, `level_trail_positions` is empty, so `last_trail_pos`
    /// falls back to 0 via `unwrap_or(0)`. This causes a full trail re-scan
    /// on the first post-backtrack propagate call, which is correct: the
    /// theory's pop() already undid the appropriate assertions, and the
    /// re-asserted atoms from levels 0 to new_level are already in the
    /// theory's `asserted` map (cheap occupied-entry update path).
    pub(crate) fn with_warm_trail_position(
        mut self,
        trail_len: usize,
        decision_level: u32,
    ) -> Self {
        self.last_trail_pos = trail_len;
        self.has_checked = true;
        self.theory_level = decision_level;
        // level_trail_positions is left empty. On backtrack, unwrap_or(0)
        // causes a full trail re-scan, which is correct and cheaper than
        // the warm-reset + full replay we're avoiding.
        self
    }

    pub(crate) fn with_inline_bound_refinement_replay(
        mut self,
        known_replays: &'a HashSet<BoundRefinementReplayKey>,
    ) -> Self {
        self.bound_refinement_handoff =
            BoundRefinementHandoff::StopAndReplayInline { known_replays };
        self
    }

    /// Install the executor's wall-clock deadline on the extension.
    ///
    /// Polled at the top of `propagate_impl()` (the BCP hot loop) so a diverging
    /// theory-propagation churn honors the deadline even when the SAT loop's
    /// coarse `should_stop` poll (every 100 conflicts / 1000 decisions) never
    /// fires inside a conflict-free, decision-free spin — the T3 CHC/PDR
    /// divergence (the development design notes).
    /// A deadline hit only ever degrades the solve to `Unknown` (fail-closed).
    /// `None` (the default) disables the poll entirely for plain no-timeout
    /// solves, so the hot loop pays nothing.
    pub(crate) fn with_solve_deadline(mut self, deadline: Option<ay_core::time::Instant>) -> Self {
        self.solve_deadline = deadline;
        self
    }

    /// Forward `DpllT`'s combined conflict-verification support set
    /// (`dt_verification_axioms ++ ematching_support_axioms`) into this eager
    /// extension. Each literal is true in every model of the problem, so the
    /// eager `check()`/`propagate()` conflict verifiers can assert them to
    /// reprove a genuinely-UNSAT conflict without ever laundering a spurious one.
    /// `Vec::new()` (the default) keeps the eager path byte-identical to before.
    pub(crate) fn with_support_axioms(mut self, axioms: Vec<TheoryLit>) -> Self {
        self.support_axioms = axioms;
        self
    }

    /// Wire the Executor-owned semantic conflict-verification memo (#4535)
    /// into this eager extension (#uflia-verify-memo).
    ///
    /// See the `verify_memo` field doc for the trust-true-only policy that
    /// keeps every failure path byte-identical. `None` (the default) keeps
    /// the eager path memo-free, exactly as before.
    pub(crate) fn with_verify_memo(
        mut self,
        memo: &'a mut crate::verification::ConflictSemanticVerifyMemo,
    ) -> Self {
        self.verify_memo = Some(memo);
        self
    }

    /// Wire the Executor-owned sampled propagation-verification memo
    /// (#verify-memo, `AY_VERIFY_MEMO=1`) into this eager extension.
    ///
    /// See the `verify_prop_memo` field doc for the trust-true-only policy.
    /// The memo is inert unless the env flag is armed; `None` (the default)
    /// keeps the eager path memo-free either way.
    pub(crate) fn with_verify_prop_memo(
        mut self,
        memo: &'a mut crate::verification::PropSemanticVerifyMemo,
    ) -> Self {
        self.verify_prop_memo = Some(memo);
        self
    }
}
