// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV incremental solve pipeline (push/pop persistent SAT solver).
//!
//! Extracted from `bv.rs` (#2998 code-health). Contains the incremental
//! BV solve path that maintains a persistent SAT solver across check-sat
//! calls, with scoped assertion activation and global definitional clauses.
//!
//! Non-incremental (single-shot) pipeline remains in `bv.rs`.

use std::sync::atomic::Ordering;

use ay_bv::BvSolver;
use ay_core::TermId;
use ay_sat::{Literal as SatLiteral, SatResult, Solver as SatSolver};

use crate::executor_types::{Result, SolveResult};
use crate::incremental_state::IncrementalBvState;

use super::super::Executor;
use super::bv::{install_bv_sat_interrupt, BvSolveConfig};
use super::bv_encoding;

#[path = "bv_incremental/resource_budget.rs"]
mod resource_budget;

impl Executor {
    /// Incremental BV solve: persistent SAT solver with push/pop scope management.
    ///
    /// Phases (per check-sat):
    /// 1. Tseitin encoding of new assertions (cached across calls)
    /// 2. BV bitblasting for BV predicates (=, bvult, etc.)
    /// 3. #858 predicate linking: equivalences (tseitin_var ↔ bv_lit)
    /// 4. Global definitional clauses, scoped assertion activation
    ///
    /// Key invariant: Definitional clauses (Tseitin defs, BV circuits, equivalences)
    /// are added GLOBALLY so cached term→var and term→bits remain valid after pop.
    /// Only assertion activation (unit clause on root literal) is scoped.
    pub(super) fn solve_bv_incremental_inner(
        &mut self,
        config: &BvSolveConfig,
        proof_enabled: bool,
    ) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        // Snapshot interrupt/deadline before borrowing incremental state (#3381).
        // Cannot use self.make_should_stop() here because the returned opaque
        // `impl Fn() -> bool` keeps an immutable borrow on `self` alive, which
        // conflicts with the mutable borrow of `self.incr_bv_state` below.
        // Instead, clone the Arc and copy the deadline directly.
        let sat_interrupt = self.solve_interrupt.clone();
        let sat_deadline = self.solve_deadline.get();
        // Snapshot `:rlimit` before the persistent solver is mutably borrowed.
        let bv_conflict_allowance = self.resource_limit;
        let interrupt_flag = sat_interrupt.clone();
        let deadline = self.solve_deadline.clone();
        let should_stop = move || {
            if let Some(ref flag) = interrupt_flag {
                if flag.load(Ordering::Relaxed) {
                    return true;
                }
            }
            deadline.expired()
        };
        let random_seed = self.current_random_seed();

        // Collect combined-theory axiom clauses generated in a separate borrow scope
        // (axiom generators need &self, which conflicts with &mut self.incr_bv_state).
        let mut all_axiom_clauses: Vec<ay_core::CnfClause> = Vec::new();

        // Pre-collect eager terms BEFORE borrowing incr_bv_state mutably (#8142).
        // collect_eager_bv_terms needs &self, which conflicts with &mut self.incr_bv_state.
        let eager_terms_for_delay =
            if !proof_enabled && (config.array_axioms || config.uf_congruence) {
                let eager = self.collect_eager_bv_terms(config, &[]);
                if eager.is_empty() {
                    None
                } else {
                    Some(eager)
                }
            } else {
                None
            };

        // Pre-collect Bool-sorted UF application arguments BEFORE borrowing
        // incr_bv_state mutably (#boolarg-congruence): collect_uf_bool_args
        // needs &self, which conflicts with the &mut self.incr_bv_state borrow
        // below. The literals are materialized right before Tseitin↔BV linking
        // so build_linking_batch bridges them to any Tseitin variables, and
        // the congruence generators can encode Bool argument differences as
        // 1-bit XORs (previously such pairs were dropped entirely — missing
        // congruence over Bool argument positions, a wrong-SAT class).
        let uf_bool_args = if config.uf_congruence || config.non_bv_congruence {
            self.collect_uf_bool_args(&[])
        } else {
            Vec::new()
        };

        // Initialize state if needed
        let state = self
            .incr_bv_state
            .get_or_insert_with(IncrementalBvState::new);
        // This state is reused for the WHOLE session, across pops included:
        // `IncrementalBvState::pop()` unwinds one SAT scope and destroys
        // nothing. See its doc comment for why that is safe by construction.

        // Sync variable allocations to avoid overlap with SAT scope selectors.
        // sync_tseitin_next_var() ensures Tseitin vars start beyond all SAT vars
        // (including scope selectors from push()), then sync_next_bv_var() ensures
        // BV vars start beyond Tseitin vars. Both are needed (#7031).
        state.sync_tseitin_next_var();
        state.sync_next_bv_var();

        // Preprocessing (variable substitution) is only applied in non-incremental mode.
        // Incremental encoding would need to track original -> preprocessed term mappings
        // and handle preprocessing results varying based on prior assertions (#1825).

        // Find new assertions that haven't been encoded yet
        let new_assertions: Vec<TermId> = self
            .ctx
            .assertions
            .iter()
            .filter(|&term| !state.encoded_assertions.contains_key(term))
            .copied()
            .collect();

        // Create Tseitin encoder from persistent state
        let mut tseitin =
            ay_core::Tseitin::from_state(&self.ctx.terms, std::mem::take(&mut state.tseitin_state));

        // Create BvSolver with cached term-to-bits and predicate_to_var mappings (#1452).
        // Enable delayed internalization for combined theories (#8142) with eager
        // term protection: BV terms that appear as array indices or UF arguments
        // are eagerly internalized, while bulk data-path operations can be delayed.
        let use_delayed_incr = !proof_enabled;
        let mut bv_solver = BvSolver::new(&self.ctx.terms);
        // Wire interrupt flag for cooperative cancellation during bitblasting (#8609).
        if let Some(ref flag) = self.solve_interrupt {
            bv_solver.set_interrupt(flag.clone());
        }
        if use_delayed_incr {
            bv_solver.set_delay_enabled(true);

            // Apply pre-collected eager terms for combined theories (#8142).
            if let Some(eager) = eager_terms_for_delay {
                bv_solver.set_eager_terms(eager);
            }
        }
        for (term, bits) in &state.term_to_bits {
            bv_solver.set_term_bits(*term, bits.clone());
        }
        bv_solver.set_next_var(state.next_bv_var);
        // Restore predicate_to_var cache to ensure re-bitblasting returns same CNF variables
        bv_solver.set_predicate_to_var(
            state
                .predicate_to_var
                .iter()
                .map(|(&k, &v)| (k, v))
                .collect(),
        );
        // Restore bool_to_var cache for BV `ite` conditions and other Bool-in-BV terms
        bv_solver.set_bool_to_var(state.bool_to_var.clone());
        // Restore bv_ite_conditions set (#1696)
        bv_solver.set_bv_ite_conditions(state.bv_ite_conditions.clone());
        // Restore delayed ops from previous check-sat calls (#7452).
        // If a prior scope returned UNSAT before building delayed circuits,
        // the cached term_to_bits entries need their DelayedBvOp metadata
        // to trigger circuit building when they appear in model checking.
        if !state.delayed_ops.is_empty() {
            bv_solver.set_delayed_ops(state.delayed_ops.clone());
        }

        // Encode new assertions: collect (term, root_lit, def_clauses)
        // Store root_lit in encoded_assertions for re-activation after pop (#1452)
        let mut encodings: Vec<(TermId, i32, Vec<ay_core::CnfClause>)> = Vec::new();
        for &term in &new_assertions {
            // Use Tseitin for Boolean structure (and, or, not, ite)
            let enc = tseitin.encode_assertion(term);
            encodings.push((term, enc.root_lit, enc.def_clauses.clone()));
            state.encoded_assertions.insert(term, enc.root_lit);
        }

        // Save Tseitin state and get the number of Tseitin variables
        state.tseitin_state = tseitin.into_state();
        let tseitin_num_vars = state.tseitin_state.next_var;

        // BV variables are offset by tseitin_num_vars to avoid overlap.
        // CRITICAL (#1453): bv_var_offset must remain stable across push/pop because:
        // - term_to_bits stores BV var numbers WITHOUT offset
        // - SAT clauses are added WITH offset applied
        // - Model extraction must use THE SAME offset used during encoding
        let var_offset = if let Some(offset) = state.bv_var_offset {
            offset
        } else {
            let offset = tseitin_num_vars as i32;
            state.bv_var_offset = Some(offset);
            offset
        };
        if state.next_bv_var < tseitin_num_vars {
            state.next_bv_var = tseitin_num_vars;
            bv_solver.set_next_var(state.next_bv_var);
        }

        // Materialize single-literal encodings for Bool-sorted UF arguments
        // BEFORE linking (#boolarg-congruence, see the pre-collect comment
        // above). Idempotent across check-sat calls via the restored
        // bool_to_var cache; new clauses are drained into the linking batch's
        // extra BV clauses and added globally with the other BV clauses.
        for &arg in &uf_bool_args {
            let _ = bv_solver.ensure_bool_literal(arg);
        }

        // --- Predicate + Bool linking (#858, #5457) ---
        let mut linking_batch = bv_encoding::build_linking_batch(
            &state.tseitin_state.var_to_term,
            &mut bv_solver,
            var_offset,
            &self.ctx.terms,
            Some(&state.linked_equivalence_terms),
        );
        for &term in linking_batch.newly_linked_terms() {
            state.linked_equivalence_terms.insert(term);
        }

        // Get BV clauses generated by bitblast_predicate
        let bv_clauses = linking_batch.take_extra_bv_clauses();
        let bv_num_vars = bv_solver.num_vars();
        state.next_bv_var = bv_num_vars + 1;

        // NOTE (#7892 model soundness): the BvSolver caches (term_to_bits,
        // predicate_to_var, bool_to_var, bv_ite_conditions) are deliberately
        // NOT saved into `state` here. The `materialize_array_bv_terms` /
        // `materialize_uf_arg_bv_terms` passes below allocate fresh bit
        // variables for UF-argument and array-index terms (e.g. plain BV vars
        // `x`, `y` that appear only inside `f(x)`, `f(y)`), and the congruence
        // axioms constrain exactly those bits. A pre-materialize snapshot
        // omitted them, so model extraction never read the SAT assignment for
        // those terms and model completion invented values that violated the
        // congruence axioms (a gate-refuted model on the pop-rebuild path).
        // The authoritative post-materialize snapshot happens right before
        // `drop(bv_solver)` and is merged into `state` after re-borrow.

        // --- Phase 9: Theory-specific axiom generation for combined theories (#7015) ---
        // The axiom generators (generate_array_bv_axioms, generate_euf_bv_axioms_debug)
        // are methods on &self, which conflicts with the mutable borrow of
        // self.incr_bv_state through `state`. To resolve, we save essential fields
        // from `state` to locals, let `state` drop (NLL), call the generators,
        // then re-borrow `state`.
        let has_new_assertions = !new_assertions.is_empty();
        let saved_next_bv_var = state.next_bv_var;
        let saved_pending_pushes = state.pending_pushes;
        let saved_persistent_sat = state.persistent_sat.take();
        let saved_tseitin_next_var = state.tseitin_state.next_var;
        let saved_bv_eq_congruence_pairs = if has_new_assertions && config.bv_eq_congruence {
            Some(state.emitted_bv_eq_congruence_pairs.clone())
        } else {
            None
        };
        let saved_array_tseitin_term_to_var = if has_new_assertions && config.array_axioms {
            Some(state.tseitin_state.term_to_var.clone())
        } else {
            None
        };
        // Non-BV-return UF congruence only needs the Tseitin term/var maps from
        // `state` here; the BV bits of the UF arguments are captured AFTER the
        // `materialize_*` passes below (see `non_bv_congruence_term_bits`). The
        // pre-materialize `state.term_to_bits` snapshot omitted bits for compound
        // BV arguments (e.g. an `ite` term used only as a constructor argument),
        // which the matching non-incremental path snapshots post-materialization.
        let saved_non_bv_congruence_inputs = if has_new_assertions && config.non_bv_congruence {
            Some((
                state.tseitin_state.term_to_var.clone(),
                state.tseitin_state.var_to_term.clone(),
            ))
        } else {
            None
        };
        // NLL: `state` (&mut self.incr_bv_state) borrow ends after last use above.

        // Materialize BV bits for array/UF terms before axiom generation (#7015 Step 4).
        // These call &self methods, which require dropping the `state` borrow.
        // Only generate axioms when new assertions exist — axiom clauses are global
        // and persist across push/pop, so re-generating for unchanged assertions
        // would produce duplicate clauses (#7015 dedup optimization).
        if has_new_assertions && config.array_axioms {
            self.materialize_array_bv_terms(&mut bv_solver, &[]);
            let extra = bv_solver.take_clauses();
            bv_encoding::offset_and_push_clauses(extra, var_offset, &mut all_axiom_clauses);
        }
        if has_new_assertions && config.uf_congruence {
            self.materialize_uf_arg_bv_terms(&mut bv_solver, &[]);
            let extra = bv_solver.take_clauses();
            bv_encoding::offset_and_push_clauses(extra, var_offset, &mut all_axiom_clauses);
        }

        // BV bits in the SAT solver are offset by the STABLE var_offset (from
        // state.bv_var_offset), not by the current tseitin_num_vars. After a
        // pop-rebuild-checksat cycle, tseitin_num_vars grows but var_offset stays
        // fixed. Axiom generators must use var_offset so their clauses reference
        // the correct SAT variables (#7881).
        let bv_offset_u32 = var_offset as u32;
        let mut running_offset = tseitin_num_vars.max(bv_offset_u32 + bv_solver.num_vars());

        // Array axiom clauses (ABV/AUFBV) — added GLOBALLY.
        if has_new_assertions && config.array_axioms {
            let array_axiom_result = self.generate_array_bv_axioms(
                &bv_solver,
                bv_offset_u32,
                running_offset,
                &[],
                saved_array_tseitin_term_to_var
                    .as_ref()
                    .expect("array Tseitin term map saved when array axioms are enabled"),
            );
            for clause in array_axiom_result.clauses {
                all_axiom_clauses.push(clause);
            }
            running_offset += array_axiom_result.num_vars;
        }

        // EUF congruence axiom clauses (UFBV/AUFBV) — added GLOBALLY.
        if has_new_assertions && config.uf_congruence {
            let euf_axiom_result = self.generate_euf_bv_axioms_debug(
                &bv_solver,
                bv_offset_u32,
                running_offset,
                self.debug_ufbv,
                &[],
            );
            for clause in euf_axiom_result.clauses {
                all_axiom_clauses.push(clause);
            }
            running_offset += euf_axiom_result.num_vars;
        }

        // BV equality congruence clauses are global. If no new assertions were
        // encoded for this check-sat, a same-scope recheck cannot introduce any
        // new equality pairs, so skip the full congruence scan entirely.
        let bv_eq_congruence_batch = if has_new_assertions && config.bv_eq_congruence {
            Some(bv_encoding::build_bv_eq_congruence_batch(
                &self.ctx.terms,
                &self.ctx.assertions,
                &bv_solver,
                var_offset,
                saved_bv_eq_congruence_pairs.as_ref(),
            ))
        } else {
            None
        };
        // POST-MATERIALIZE snapshot of every BvSolver cache (#7892, #7881).
        //
        // Two consumers need the bits allocated by `materialize_array_bv_terms`
        // / `materialize_uf_arg_bv_terms` above:
        //
        // 1. #pushscope-non-bv-congruence (completeness, sound):
        //    `generate_non_bv_euf_congruence` matches argument equality via
        //    these bits; a pre-materialize `state.term_to_bits` clone omitted
        //    bits for a compound argument (e.g. an `ite` BV term used only as a
        //    datatype constructor argument), so `build_arg_diff_vars` fell back
        //    to `Unencodable` and the congruence pair was silently skipped.
        //    The non-incremental path already snapshots `term_bits`
        //    post-materialization (bv/mod.rs Phase 9); this mirrors it.
        //
        // 2. Model extraction (#7892 soundness): the congruence axioms
        //    generated above constrain the freshly materialized bits of UF
        //    arguments / array indices (e.g. plain vars `x`, `y` that appear
        //    only inside `f(x)`, `f(y)`). `state.term_to_bits` — which model
        //    extraction reads — must contain those bits, or the emitted model
        //    silently drops the SAT solver's assignment for them and model
        //    completion invents values that violate congruence (the
        //    pop-rebuild wrong-model class caught by the independent gate).
        //
        // The snapshot is merged into `state` after the re-borrow below.
        let post_materialize_term_bits = bv_solver.term_to_bits().clone();
        let post_materialize_predicate_to_var = bv_solver.predicate_to_var().clone();
        let post_materialize_bool_to_var = bv_solver.bool_to_var().clone();
        let post_materialize_bv_ite_conditions = bv_solver.bv_ite_conditions().clone();

        let delayed_state_from_solver = bv_solver.take_delayed_state();
        let delay_div_cache_seed = delayed_state_from_solver.as_ref().map(|_| {
            (
                bv_solver.div_caches().0.clone(),
                bv_solver.div_caches().1.clone(),
                bv_solver.num_vars() + 1,
            )
        });
        drop(bv_solver);

        let mut non_bv_congruence_bailed = false;
        if let Some((saved_term_to_var, saved_var_to_term)) = saved_non_bv_congruence_inputs {
            // Non-BV-return UF congruence clauses encode equality over Bool/Int/UF
            // results using Tseitin vars. They must use the stable BV offset, not
            // the ever-growing current Tseitin frontier, or subsequent check-sat
            // calls will reference the wrong SAT variables (#7892).
            let tseitin_result = ay_core::TseitinResult::new(
                vec![],
                saved_term_to_var,
                saved_var_to_term,
                1,
                var_offset as u32,
            );
            let congruence_outcome = self.generate_non_bv_euf_congruence(
                &post_materialize_term_bits,
                &post_materialize_bool_to_var,
                &tseitin_result,
                running_offset,
                &mut all_axiom_clauses,
                &[],
            );
            // Item 4 Stage 2: a bailed (partial) congruence axiomatization
            // is sound for UNSAT only — SAT is degraded below.
            non_bv_congruence_bailed = congruence_outcome.bailed;
            running_offset += congruence_outcome.num_vars;
        }

        // Re-borrow state after axiom generation completes.
        let state = self
            .incr_bv_state
            .as_mut()
            .expect("incremental BV state must exist after axiom generation");
        state.persistent_sat = saved_persistent_sat;
        state.pending_pushes = saved_pending_pushes;

        // Merge the POST-materialize BvSolver caches into the persistent state
        // (#7892 model soundness — see the snapshot comment above). Model
        // extraction below reads `state.term_to_bits`, so the freshly
        // materialized UF-argument / array-index bits must be present, and the
        // next check-sat must reuse the same variables the axiom clauses
        // already reference.
        for (term, bits) in post_materialize_term_bits {
            state.term_to_bits.insert(term, bits);
        }
        for (term, lit) in post_materialize_predicate_to_var {
            state.predicate_to_var.insert(term, lit);
        }
        state.bool_to_var = post_materialize_bool_to_var;
        state.bv_ite_conditions = post_materialize_bv_ite_conditions;
        // `state.next_bv_var` is re-synced below (after solver creation) to
        // `sat_total + 1`, which already covers every variable the materialize
        // passes allocated (`total_vars >= running_offset >= bv_offset +
        // post-materialize BV vars`) — no separate bump is needed here.

        // Total SAT variables: Tseitin + BV + axiom vars
        let total_vars = (tseitin_num_vars as usize)
            .max(saved_next_bv_var as usize + var_offset as usize)
            .max(running_offset as usize);

        // Initialize persistent SAT solver if needed
        let mut solver = if let Some(s) = state.persistent_sat.take() {
            s
        } else {
            let mut sat = SatSolver::new(total_vars);
            sat.set_random_seed(random_seed);
            if self.progress_enabled {
                sat.set_progress_enabled(true);
            }
            if let Some(path) = &self.progress_json_path {
                if let Ok(obs) = ay_sat::json_observer::JsonProgressObserver::new_append(path) {
                    sat.set_observer(Some(Box::new(obs)));
                }
            }
            // Incremental BV theory state rebuilds fresh SAT solvers for
            // sub-queries. Avoid root preprocessing so clause identities remain
            // stable across push/pop and CHC replay paths.
            sat.set_preprocess_enabled(false);
            // Disable congruence closure for BV (#3661): structurally similar
            // encoding variables (e.g. carry bits) are semantically distinct.
            sat.set_congruence_enabled(false);
            // Adaptive reorder gate for large BV instances (#8118).
            if total_vars > 50_000 {
                sat.set_reorder_enabled(false);
            }
            if proof_enabled {
                sat.enable_clause_trace();
                sat.set_proof_bookkeeping_budget(Executor::search_proof_bookkeeping_budget_for(
                    &self.ctx,
                    self.proof_reconstruction_step_budget,
                ));
            }
            // Apply pending pushes from SMT push before solver existed
            for _ in 0..state.pending_pushes {
                sat.push();
            }
            state.pending_pushes = 0;
            sat
        };
        solver.ensure_num_vars(total_vars);

        // Sync next_var allocations after solver creation
        let sat_total = solver.total_num_vars() as u32;
        state.tseitin_state.next_var = saved_tseitin_next_var.max(sat_total + 1);
        state.next_bv_var = saved_next_bv_var.max(sat_total + 1);

        // Add Tseitin definitional clauses GLOBALLY (survive push/pop)
        for (_, _, ref def_clauses) in &encodings {
            bv_encoding::add_clauses_global(&mut solver, def_clauses);
        }

        // Add BV circuit clauses GLOBALLY (offset by tseitin_num_vars)
        bv_encoding::add_offset_clauses_global(&mut solver, &bv_clauses, var_offset);

        linking_batch.add_global_equivalence_clauses(&mut solver);

        // Add BV equality congruence axioms GLOBALLY (#5441, #6691 config-driven).
        if let Some(congruence_batch) = bv_eq_congruence_batch {
            bv_encoding::add_clauses_global(&mut solver, congruence_batch.clauses());
            for &pair in congruence_batch.newly_emitted_pairs() {
                state.emitted_bv_eq_congruence_pairs.insert(pair);
            }
        }

        // Add theory axiom clauses GLOBALLY (#7015 Step 4).
        // These were generated above in the `state`-dropped block.
        bv_encoding::add_clauses_global(&mut solver, &all_axiom_clauses);

        let mut delayed_state = delayed_state_from_solver;
        // Merge persistent delayed ops with newly created ones (#7452).
        // The fresh bv_solver may not have created new delayed ops for terms that
        // already had bits in term_to_bits (get_bits returns immediately).
        if delayed_state.is_none() && !state.delayed_ops.is_empty() {
            delayed_state = Some(ay_bv::DelayedBvState::new(
                state.delayed_ops.clone(),
                state.term_to_bits.clone(),
            ));
        }
        // CRITICAL: Store num_vars() + 1 to avoid variable reuse (same fix as non-incremental path).
        // Also ensure the delayed loop's BV vars don't overlap with scope selector variables
        // in the SAT solver. Push allocates a scope selector at `solver.total_num_vars()`, so
        // BV next_var must map to SAT indices beyond all existing vars (including selectors).
        // BV var v maps to SAT index (v + var_offset - 1), so safe_bv_next = total - offset + 1.
        let mut delay_div_caches = if let Some((ucache, scache, bv_next)) = delay_div_cache_seed {
            let safe_bv_next =
                (solver.total_num_vars() as u32).saturating_sub(var_offset.max(0) as u32) + 1;
            Some((ucache, scache, bv_next.max(safe_bv_next)))
        } else {
            None
        };

        // Add assertion activation clauses in the current SCOPE for assertions that
        // are not already active from this scope or an ancestor (#1452).
        // `IncrementalBvState::pop` drops the activation records deeper than the
        // new frontend depth, so the next solve re-activates the survivors once.
        // This is AY's form of Bitwuzla's `top_level = level == 0` split: depth 0
        // gets a permanent unit, depth d>0 a `+selector_d`-guarded one entered by
        // assuming `¬selector_d`. Nothing scoped becomes a permanent clause.
        for &assertion in &self.ctx.assertions {
            if let Some(&root_lit) = state.encoded_assertions.get(&assertion) {
                let needs_activation = state
                    .assertion_activation_scope
                    .get(&assertion)
                    .is_none_or(|&depth| depth > state.scope_depth);
                if needs_activation {
                    solver.add_clause(vec![crate::cnf_lit_to_sat(root_lit)]);
                    state
                        .assertion_activation_scope
                        .insert(assertion, state.scope_depth);
                }
            }
        }

        state.sat_num_vars = solver.user_num_vars();
        state.persistent_sat = Some(solver);
        // Snapshot the incremental BV view before borrowing the persistent SAT
        // solver mutably; both SAT model storage and UNSAT proof export need
        // the same persistent term-bits and Tseitin mappings.
        let solve_term_bits = state.term_to_bits.clone();
        let solve_bool_to_var = state.bool_to_var.clone();
        let solve_tseitin_result = ay_core::TseitinResult::new(
            vec![],
            state.tseitin_state.term_to_var.clone(),
            state.tseitin_state.var_to_term.clone(),
            1,
            state.tseitin_state.next_var.saturating_sub(1),
        );

        let solver = state
            .persistent_sat
            .as_mut()
            .expect("incremental BV must store persistent SAT solver before solve");
        let _deadline_guard = install_bv_sat_interrupt(solver, sat_interrupt, sat_deadline);

        resource_budget::arm_persistent_sat_conflict_budget(solver, bv_conflict_allowance);

        // Iterate solve, model check, and global clause repair for delayed ops.
        const MAX_DELAY_ITERATIONS: usize = 32;
        let mut delay_iteration = 0;
        let mut solve_result;
        // Track max BV vars allocated by tmp_bv during delayed circuit building.
        // Must be saved back to state.next_bv_var after the solver borrow is released,
        // so that sync_tseitin_next_var on the NEXT check-sat doesn't allocate Tseitin
        // variables that overlap with BV circuit variables in the SAT solver (#7015).
        let mut delay_max_bv_next_var = 0u32;

        loop {
            solve_result = solver.solve_interruptible(&should_stop).into_inner();
            collect_sat_stats!(self, &solver);

            // Check delayed operations if SAT and we have delayed ops (#7015)
            if let SatResult::Sat(ref model) = solve_result {
                if let Some(ref mut ds) = delayed_state {
                    if ds.has_unresolved() && delay_iteration < MAX_DELAY_ITERATIONS {
                        delay_iteration += 1;

                        // Unified check: per-op escalation from cheap axioms to full circuit.
                        let (cheap_clauses, needs_circuit) = ds.check(model, var_offset);
                        for clause in &cheap_clauses {
                            let lits: Vec<SatLiteral> = clause
                                .literals()
                                .iter()
                                .map(|&lit| {
                                    crate::cnf_lit_to_sat(bv_encoding::offset_cnf_lit(
                                        lit, var_offset,
                                    ))
                                })
                                .collect();
                            solver.add_clause_global(lits);
                        }

                        if !needs_circuit.is_empty() {
                            let mut tmp_bv = BvSolver::new(&self.ctx.terms);
                            tmp_bv.set_term_to_bits(ds.term_to_bits().clone());
                            if let Some((ref ucache, ref scache, ref mut next_var)) =
                                delay_div_caches
                            {
                                tmp_bv.set_div_caches(ucache.clone(), scache.clone());
                                tmp_bv.set_next_var(*next_var);
                            }
                            tmp_bv.set_delayed_ops(ds.delayed_ops().to_vec());
                            for &idx in &needs_circuit {
                                let circuit_clauses = tmp_bv.build_delayed_circuit(idx);
                                let new_bv_vars = tmp_bv.num_vars();
                                let new_total = (var_offset as usize + new_bv_vars as usize)
                                    .max(solver.total_num_vars());
                                solver.ensure_num_vars(new_total);
                                for clause in &circuit_clauses {
                                    let lits: Vec<SatLiteral> = clause
                                        .literals()
                                        .iter()
                                        .map(|&lit| {
                                            crate::cnf_lit_to_sat(bv_encoding::offset_cnf_lit(
                                                lit, var_offset,
                                            ))
                                        })
                                        .collect();
                                    solver.add_clause_global(lits);
                                }
                                let bv_extra = tmp_bv.take_clauses();
                                for clause in &bv_extra {
                                    let lits: Vec<SatLiteral> = clause
                                        .literals()
                                        .iter()
                                        .map(|&lit| {
                                            crate::cnf_lit_to_sat(bv_encoding::offset_cnf_lit(
                                                lit, var_offset,
                                            ))
                                        })
                                        .collect();
                                    solver.add_clause_global(lits);
                                }
                            }
                            // Track max BV vars for state update after loop
                            delay_max_bv_next_var =
                                delay_max_bv_next_var.max(tmp_bv.num_vars() + 1);
                            // Advance next_var to prevent variable collisions
                            // on the next loop iteration (#7015 regression fix).
                            if let Some((_, _, ref mut next_var)) = delay_div_caches {
                                *next_var = tmp_bv.num_vars() + 1;
                            }
                            drop(tmp_bv);
                        }

                        // Re-solve if anything was added
                        if !cheap_clauses.is_empty() || !needs_circuit.is_empty() {
                            continue;
                        }
                    }
                }
            }

            break; // No delayed violations (or UNSAT/Unknown) — exit loop
        }

        // Capture both flags before the match block. Propagation is deferred to
        // after `solver` (borrowed from self.incr_bv_state) is released.
        // `sat_gave_reason` must be saved here because `finalize_bv_unknown()`
        // consumes `pending_sat_unknown_reason` via `.take()`, which would make
        // the post-match check always see `is_none() == true` (#6691 audit).
        let is_unknown = matches!(solve_result, SatResult::Unknown);
        let sat_gave_reason = self.pending_sat_unknown_reason.is_some();

        // Item 4 Stage 2 soundness gate: SAT under a bailed partial non-BV
        // congruence axiomatization degrades to Unknown (UNSAT stays valid —
        // partial axioms are a subset of the full axiomatization).
        if non_bv_congruence_bailed && matches!(solve_result, SatResult::Sat(_)) {
            return self.finalize_bv_congruence_bail();
        }

        // Store model if SAT
        let result = match solve_result {
            SatResult::Sat(ref model) => {
                let sat_model: Vec<bool> = model.clone();
                let mut bv_model = Self::extract_bv_model_from_bits(
                    &sat_model,
                    &solve_term_bits,
                    var_offset,
                    &self.ctx.terms,
                );
                // Carry Bool-in-BV variable assignments (ite conditions) into
                // the model (#bv-ite-bool-model). Without this, a Bool variable
                // bit-blasted only inside a BV `ite` prints as default `false`,
                // contradicting the mux branch the SAT solver satisfied.
                Self::seed_bv_bool_assignments_from_bitblast(
                    &sat_model,
                    &solve_bool_to_var,
                    var_offset,
                    &self.ctx.terms,
                    &mut bv_model,
                );
                match ay_bv::validate_bv_assertions(
                    &self.ctx.terms,
                    &self.ctx.assertions,
                    &bv_model,
                ) {
                    Ok(checked) => {
                        self.last_statistics
                            .set_int("model_validation.bv.checked", checked as u64);
                    }
                    Err(error) => {
                        return self.finalize_bv_model_validation_failure(error);
                    }
                }
                self.solve_and_store_model_full(
                    SatResult::Sat(sat_model),
                    &solve_tseitin_result,
                    None,
                    None,
                    None,
                    None,
                    Some(bv_model),
                    None,
                    None,
                    None,
                )
            }
            SatResult::Unsat(_) => {
                // Extract clause trace before calling finalize (NLL: releases
                // the solver borrow from self.incr_bv_state).
                let trace = if proof_enabled {
                    solver.snapshot_clause_trace()
                } else {
                    None
                };
                self.finalize_bv_unsat(trace, &solve_tseitin_result.var_to_term, proof_enabled)
            }
            SatResult::Unknown => self.finalize_bv_unknown(),
            #[allow(unreachable_patterns)]
            _ => unreachable!("BUG: SatResult variant not handled in BV incremental path"),
        };

        // Propagate interrupt/timeout reason to executor (#3381, #6691).
        // Deferred past the match block because `solver` borrows from
        // self.incr_bv_state, preventing &mut self calls while live.
        // Skip when the SAT solver already provided its own reason (saved
        // in `sat_gave_reason` before finalize_bv_unknown consumed pending).
        if is_unknown && !sat_gave_reason {
            self.propagate_bv_unknown_reason(true);
        }

        // Update state.next_bv_var to account for delayed circuit variables (#7015).
        // The delayed loop's tmp_bv allocates BV vars beyond what bv_solver tracked.
        // Without this update, sync_tseitin_next_var on the NEXT check-sat may allocate
        // Tseitin variables in the SAT position range occupied by BV circuit vars
        // (bv_var + var_offset), causing variable collisions and spurious UNSAT.
        if delay_max_bv_next_var > 0 {
            if let Some(ref mut state) = self.incr_bv_state {
                state.next_bv_var = state.next_bv_var.max(delay_max_bv_next_var);
            }
        }

        // Save delayed ops to state for persistence across check-sat calls (#7452).
        // Without this, cached term_to_bits entries for delayed operations lack their
        // constraining circuits on subsequent check-sat calls after pop.
        if let Some(ref ds) = delayed_state {
            if let Some(ref mut state) = self.incr_bv_state {
                state.delayed_ops = ds.delayed_ops().to_vec();
            }
        }

        result
    }
}
