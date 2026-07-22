// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lazy arm of the incremental split-loop pipeline.
//!
//! Extracted from `pipeline_incremental_split_macros.rs` (#6680).
//! Contains the lazy theory-check path: SAT solves to completion,
//! then theory checks the full model. Used by LIA and combined theories
//! that don't yet benefit from eager propagation.

/// Lazy arm implementation for `solve_incremental_split_loop_pipeline!`.
macro_rules! pipeline_incremental_split_lazy_arm {
    ($self:ident,
        tag: $tag:expr,
        persistent_sat_field: $sat_field:ident,
        tseitin_field: $tseitin_field:ident,
        encoded_field: $encoded_field:ident,
        activation_scope_field: $activation_scope_field:ident,
        create_theory: $create_theory:expr,
        extract_models: |$theory_var:ident| $extract:expr,
        max_splits: $max_splits:expr,
        pre_theory_import: |$import_theory:ident, $import_lc:ident, $import_hc:ident, $import_ds:ident| $import_expr:expr,
        post_theory_export: |$export_theory:ident| $export_expr:expr
        $(, pre_iter_check: |$pic_self:ident| $pic_expr:expr)?
        $(, per_round_shadow: |$sh_result:ident, $sh_lits:ident, $sh_atoms:ident, $sh_lemmas:ident| $sh_expr:expr)?
        $(, max_string_lemma_requests: $max_slr:expr,
           handle_string_lemma: |$sl_lemma:ident, $sl_negations:ident| $sl_handler:expr)?
    ) => {{
#[cfg(not(kani))]
        // #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
#[cfg(kani)]
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
        use ay_core::{TermId, Tseitin, TseitinEncodedAssertion};
        use ay_sat::{Literal as SatLiteral, SatResult, Solver as SatSolver, Variable as SatVariable};
        use $crate::executor_types::{SolveResult, UnknownReason};
        use $crate::incremental_state::{collect_active_theory_atoms_cached, IncrementalTheoryState};
        use $crate::executor::theories::freeze_var_if_needed;
        use $crate::executor::theories::split_incremental::{
            map_conflict_to_blocking_clause,
            BlockingClauseResult,
        };

        // #8636: Build should_stop closure before borrowing incr_theory_state
        // so the SAT solver respects caller-set interrupt flags and deadlines.
        let _islp_should_stop = $self.make_should_stop();

        let proof_enabled = $self.produce_proofs_enabled();
        let random_seed = $self.current_random_seed();
        let should_record_random_seed = match $self.incr_theory_state.as_ref() {
            Some(state) => state.$sat_field.is_none(),
            None => true,
        };
        if should_record_random_seed {
            $self.record_applied_sat_random_seed_for_test(random_seed);
        }

        // Initialize or get incremental state.
        // Take ownership so $self remains borrowable by the string-lemma handler.
        // Restored to $self.incr_theory_state at macro exit.
        let _ = $self
            .incr_theory_state
            .get_or_insert_with(IncrementalTheoryState::new);
        let mut state = $self.incr_theory_state.take()
            .expect("invariant: incr_theory_state initialized by get_or_insert_with above");
        collect_theory_stats!(incremental: $self, state);

        pipeline_incremental_setup!(
            $self, state, proof_enabled, random_seed, $tag,
            sat_field: $sat_field,
            tseitin_field: $tseitin_field,
            encoded_field: $encoded_field,
            activation_scope_field: $activation_scope_field,
            solver_init: {
                if let Some(ref mut sat) = state.$sat_field {
                    for _ in 0..state.scope_depth {
                        sat.push();
                    }
                }
            },
            out: (new_assertion_set, solver, tseitin, base_var_to_term, base_term_to_var, pending_activations)
        );
        state.$sat_field = Some(solver);

        // Save Tseitin state back
        state.$tseitin_field = tseitin.into_state();
        // Proof ledger clone + context registration (#5814 Packet A)
        let (mut _islp_local_clausification_proofs, mut _islp_local_original_clause_theory_proofs) =
            pipeline_clone_local_proof_ledgers!(state, proof_enabled);
        pipeline_register_proof_context!($self, proof_enabled, $tag);

        // Collect theory atoms in active assertions only. The global
        // Bool-UF-arg scan reuses the persistent high-water-mark cache (#N).
        let base_active_atoms = collect_active_theory_atoms_cached(
            &$self.ctx.terms,
            &$self.ctx.assertions,
            Some(&mut state.bool_uf_arg_cache),
        );
        // Reuse scratch allocation from previous check-sat call (#8573).
        state.scratch_var_to_term.clone_from(&base_var_to_term);
        let mut local_var_to_term: HashMap<u32, TermId> =
            std::mem::take(&mut state.scratch_var_to_term);
        let solver = state
            .$sat_field
            .as_mut()
            .expect(concat!("incremental ", $tag, " should initialize persistent SAT solver"));
        // SMT push/pop owns the persistent solver's outer scopes via
        // IncrementalTheoryState::{push,pop}. The lazy split loop adds exactly
        // one private frame per check-sat, and every exit-path pop below
        // balances only that local frame.
        solver.push();
        // #6853: Apply deferred activation clauses inside the private push scope.
        pipeline_apply_pending_activations!(
            solver, pending_activations, proof_enabled, state
        );
        for &term in &base_active_atoms {
            if let Some(&var) = base_term_to_var.get(&term) {
                freeze_var_if_needed(solver, SatVariable::new(var));
            }
        }

        // Bound axiom injection (#6579): shared macro (#5814 Packet 1)
        pipeline_inject_bound_axioms!(
            $self, solver, base_active_atoms, base_term_to_var,
            $create_theory, proof_enabled, $tag,
            _islp_local_clausification_proofs, _islp_local_original_clause_theory_proofs,
            state
        );

        // Local variable maps grow as splits are added
        let mut local_term_to_var: HashMap<TermId, u32> = base_term_to_var;
        let mut local_next_var: u32 = u32::try_from(solver.user_num_vars() + solver.scope_depth())
            .expect("SAT solver variable count does not fit in u32");
        let base_vars: HashSet<u32> = base_var_to_term.keys().copied().collect();
        let mut _islp_added_split_clauses: HashSet<
            $crate::executor::theories::split_incremental::SplitClauseKey,
        > = HashSet::default();
        let mut _islp_model_eq_tracker = $crate::executor::theories::split_incremental::ModelEqualityTracker::new(
            $crate::executor::theories::split_incremental::model_equality::MODEL_EQ_MAX_ROUNDS_SPLIT,
        );

        // Learned state persisted across theory instances
        let mut _islp_learned_cuts: Vec<ay_lia::StoredCut> = Vec::new();
        let mut _islp_seen_hnf_cuts: HashSet<ay_lia::HnfCutKey> = HashSet::default();
        let mut _islp_dioph_state = ay_lia::DiophState::default();
        let mut _islp_theory_lemmas: Vec<ay_core::TheoryLemma> = Vec::new();

        // Split value trends for unbounded oscillation detection
        let mut _islp_last_split_values: $crate::executor::theories::solve_harness::SplitOscillationMap = HashMap::default();

        // Per-theory statistics saved from the most recent theory instance (#6579).
        let mut _islp_last_theory_stats: Vec<(&'static str, u64)> = Vec::new();

        // Split-loop timing (#6503). dpll_create/replay_splits stay zero (no rebuild).
        let mut _islp_timing = $crate::SplitLoopTimingStats::default();
        let _islp_total_start = ay_core::time::Instant::now();

        // Structural snapshot for fast theory reconstruction (#6590).
        // On the first iteration, the snapshot is None and register_atom parses
        // all atoms from scratch. On subsequent iterations, the snapshot provides
        // a pre-populated atom cache so register_atom skips parsing.
        let mut _islp_theory_snapshot: Option<Box<dyn std::any::Any>> = None;

        // Theory-guided phase hints (#8067): saved across iterations so the
        // SAT solver uses LP-model-consistent polarity on each `solve()` call.
        // In the lazy path the theory only exists after SAT finds a model, so
        // we collect phase hints from the theory before it is dropped and apply
        // them before the next `solve()`.  This matches Z3's PS_CACHING mode.
        let mut _islp_saved_phase_hints: Vec<(u32, bool)> = Vec::new();

        // #relevancy-lazy-routing: bounded lazy-DETOUR caps (UFLIA hybrid
        // only; every other caller leaves the executor field `None` — zero
        // behavior change). Absolute targets snapshot the persistent solver's
        // counters HERE so the cap bounds this whole attempt's work across
        // all split rounds, not per round. The 32x decision companion bounds
        // conflict-light decision churn the conflict cap alone cannot.
        let _islp_detour_conflict_cap: Option<u64> = $self
            .split_lazy_detour_conflict_budget
            .map(|n| solver.num_conflicts().saturating_add(n));
        let _islp_detour_decision_cap: Option<u64> = $self
            .split_lazy_detour_conflict_budget
            .map(|n| solver.num_decisions().saturating_add(n.saturating_mul(32)));

        // String lemma tracking (#6688): only present when handle_string_lemma is provided.
        $(
            let mut _islp_string_lemma_requests: usize = 0;
            let _islp_max_string_lemma_requests: usize = $max_slr;
            let mut _islp_string_lemma_clauses: Vec<Vec<TermId>> = Vec::new();
        )?

        // Proof tracking setup (#6660, #6735): build negation map once and
        // sync only newly encoded terms.
        let mut _islp_negations = $crate::incremental_proof_cache::IncrementalNegationCache::seed(
            &mut $self.ctx.terms,
            local_var_to_term.values().copied(),
            proof_enabled,
        );
        let mut _islp_theory_lemma_seen =
            $crate::incremental_proof_cache::TheoryLemmaSeenSet::default();

        // M-A2 lazy-persistent-combiner shadow (ARRAY-PROCEDURE-CLOSER-BLUEPRINT
        // §5 A2): per-round buffer of the theory literals synced into the fresh
        // combiner this round, replayed onto the create-once + warm-reset
        // persistent shadow combiner. Debug-only and only DECLARED when a
        // `per_round_shadow` hook was supplied (AUFLIA); folds out entirely in
        // release and does not exist at all for non-shadow callers (LIA, etc.).
        // The `stringify!` references the optional group's `$sh_expr` metavar so
        // the repetition is well-formed; it never evaluates the hook body.
        $(
            #[cfg(debug_assertions)]
            let mut _islp_shadow_lits: Vec<(TermId, bool)> =
                { let _ = stringify!($sh_expr); Vec::new() };
        )?
        let _islp_result: $crate::executor_types::Result<SolveResult> = 'split_loop: {
            for _iteration in 0..$max_splits {
                // Pre-iteration check (interrupt/deadline)
                $(
                    {
                        // Note: $pic_self is NOT bound to $self to avoid borrow conflicts
                        // with `state`. The caller's closure should capture what it needs
                        // before the macro invocation.
                        let $pic_self = &();
                        if $pic_expr {
                            let _ = solver.pop();
                            break 'split_loop Ok(SolveResult::Unknown);
                        }
                    }
                )?

                state.round_trips += 1;
                _islp_timing.dpll.round_trips += 1;

                debug_assert!(
                    !solver.has_empty_clause(),
                    "BUG: persistent SAT solver has_empty_clause=true BEFORE \
                     solve() in split loop iteration {}. Scope depth: {}, \
                     active scopes: {}. This indicates a stale UNSAT state \
                     from a previous check-sat that was not cleared on pop.",
                    _iteration,
                    solver.scope_depth(),
                    solver.scope_depth(),
                );
                // #8067: Apply saved theory phase hints before SAT solve.
                // On the first iteration this is empty; on subsequent iterations
                // it contains LP-model-consistent polarities from the previous
                // theory check, guiding the SAT solver toward theory-consistent
                // assignments and reducing unnecessary theory conflicts.
                for &(var_idx, phase) in &_islp_saved_phase_hints {
                    solver.set_var_phase(SatVariable::new(var_idx), phase);
                }
                // #8636: Check interrupt/deadline at top of each refinement iteration.
                if _islp_should_stop() {
                    $self.last_unknown_reason = Some($crate::executor_types::UnknownReason::Interrupted);
                    $self.last_result = Some(SolveResult::Unknown);
                    let _ = solver.pop();
                    break 'split_loop Ok(SolveResult::Unknown);
                }
                // #array-deadline-forward: forward the executor's live
                // per-solve deadline so inprocessing/L0-GC phases honor the
                // caller's wall budget (see the assume arm).
                solver.set_solve_deadline($self.solve_deadline.get());
                // Deterministic resource budgets (#8749 `:rlimit` +
                // #ground-determinism defaults). Bound this refinement's SAT
                // solve; with the split cap this guarantees
                // machine-independent termination on otherwise-diverging
                // theory loops (e.g. NIA).
                solver.set_conflict_budget(
                    $crate::pipeline_fns::effective_conflict_allowance(
                        $self.resource_limit,
                        $self.ground_budget_enabled,
                    )
                    .map(|n| solver.num_conflicts().saturating_add(n)),
                );
                solver.set_decision_budget(
                    $crate::pipeline_fns::effective_decision_allowance(
                        $self.decision_limit,
                        $self.ground_budget_enabled,
                    )
                    .map(|n| solver.num_decisions().saturating_add(n)),
                );
                // #relevancy-lazy-routing: clamp this round's deterministic
                // budgets to the bounded lazy-DETOUR caps (see the attempt-
                // entry snapshot above). Exhaustion surfaces as the solver's
                // ResourceBudget Unknown, which the `SatResult::Unknown` arm
                // below turns into a split-loop break — the detour can never
                // outlive its budget by more than one (budget-zero, hence
                // cheap) round. Trajectory-only: the caller treats the
                // resulting `Unknown` as "detour failed" and falls back.
                if let Some(_islp_cap) = _islp_detour_conflict_cap {
                    solver.set_conflict_budget(Some(
                        solver.conflict_budget().map_or(_islp_cap, |b| b.min(_islp_cap)),
                    ));
                }
                if let Some(_islp_cap) = _islp_detour_decision_cap {
                    solver.set_decision_budget(Some(
                        solver.decision_budget().map_or(_islp_cap, |b| b.min(_islp_cap)),
                    ));
                }
                // Relevancy brancher (#relevancy-lazy-routing): Scheme-A
                // CNF-frontier decision restriction for this round's plain SAT
                // solve. Two sources, env override always wins (AY_RELEVANCY=0
                // kills, =1/2 forces on):
                //   - `split_lazy_relevancy_hard`: set by the UFLIA hybrid's
                //     lazy fallback — relevancy ON in HARD mode (engage every
                //     decision; the design prototype's regime). The eager first
                //     attempt already served baseline-easy instances, so the
                //     hard restriction is safe here.
                //   - env-only (other lazy lanes): soft mode with the warm-up /
                //     wander-ratio trip-wire (Increment 1 semantics), default OFF.
                // Decisions-only either way — BCP and the model gate are
                // untouched. See the development design notes
                let _islp_relevancy_on = SatSolver::relevancy_env_override()
                    .unwrap_or($self.split_lazy_relevancy_hard);
                solver.set_relevancy_branching(_islp_relevancy_on);
                solver.set_relevancy_hard(
                    _islp_relevancy_on && $self.split_lazy_relevancy_hard,
                );
                // The lazy arm never wants the eager attempt's wander-abort
                // trip-wire (the persistent solver may still carry it).
                solver.arm_wander_abort(false);
                let _islp_sat_start = ay_core::time::Instant::now();
                let sat_result = solver.solve_interruptible(&_islp_should_stop).into_inner();
                _islp_timing.dpll.sat_solve += _islp_sat_start.elapsed();
                if let Some(r) = solver.last_unknown_reason() {
                    $self.last_unknown_reason = Some($crate::executor::Executor::map_sat_unknown_reason(r));
                }
                collect_sat_stats!($self, solver);
                collect_theory_stats!(incremental: $self, state);

                match sat_result {
                    SatResult::Sat(model) => {
                        _islp_negations.sync_pending(&mut $self.ctx.terms);
                        let mut theory = $create_theory;

                        // M-A2 shadow: reset this round's synced-literal buffer.
                        $(
                            #[cfg(debug_assertions)]
                            { let _ = stringify!($sh_expr); _islp_shadow_lits.clear(); }
                        )?

                        // Import structural snapshot from previous iteration (#6590).
                        // This pre-populates atom_cache so register_atom skips parsing.
                        if let Some(snapshot) = _islp_theory_snapshot.take() {
                            <_ as ay_core::TheorySolver>::import_structural_snapshot(&mut theory, snapshot);
                        }

                        {
                            let $import_theory = &mut theory;
                            let $import_lc = &mut _islp_learned_cuts;
                            let $import_hc = &mut _islp_seen_hnf_cuts;
                            let $import_ds = &mut _islp_dioph_state;
                            $import_expr;
                        }

                        // Register theory atoms (#6579, bypasses TheoryExtension).
                        for &atom in &base_active_atoms {
                            ay_core::TheorySolver::register_atom(&mut theory, atom);
                        }
                        for lemma in &_islp_theory_lemmas {
                            ay_core::TheorySolver::note_applied_theory_lemma(
                                &mut theory,
                                &lemma.clause,
                            );
                        }

                        // Sync model to theory
                        for (var, term) in $crate::iter_var_to_term_sorted(&local_var_to_term) {
                            let is_dynamic_split = !base_vars.contains(&var);
                            let is_active = is_dynamic_split || base_active_atoms.contains(&term);
                            if $crate::is_theory_atom(&$self.ctx.terms, term) && is_active {
                                // Register dynamic split atoms created in prior
                                // iterations; base atoms already registered above.
                                if is_dynamic_split {
                                    ay_core::TheorySolver::register_atom(&mut theory, term);
                                }
                                // #relevancy-lazy-routing: when the relevancy
                                // brancher ran this round's SAT solve, hand the
                                // theory the SPARSE assignment — only atoms the
                                // SAT core actually ASSIGNED. Don't-care atoms
                                // (left unassigned by the frontier-empty SAT
                                // signal) are SKIPPED, not defaulted: asserting
                                // the completed model's polarity for every
                                // don't-care equality swamps the theory with
                                // obligations the formula never required (the
                                // sparse hand-off is the design's §5.2 collapse
                                // mechanism). Sound by the same argument as the
                                // #6188 skip below: the fail-closed validation
                                // gate re-checks every assertion against the
                                // final materialized model.
                                let value = if _islp_relevancy_on {
                                    match solver.value(SatVariable::new(var)) {
                                        Some(v) => v,
                                        None => continue,
                                    }
                                } else {
                                    match model.get(var as usize).copied() {
                                        Some(v) => v,
                                        None => match solver.value(SatVariable::new(var)) {
                                            Some(v) => v,
                                            // Unassigned theory atom — skip rather than
                                            // defaulting to false (#6188).
                                            None => continue,
                                        },
                                    }
                                };
                                ay_core::TheorySolver::assert_literal(&mut theory, term, value);
                                // M-A2 shadow: record the exact (atom, value)
                                // asserted into the fresh combiner this round so
                                // the persistent shadow combiner replays an
                                // identical assignment (see per_round_shadow).
                                $(
                                    #[cfg(debug_assertions)]
                                    { let _ = stringify!($sh_expr); _islp_shadow_lits.push((term, value)); }
                                )?
                                if std::env::var_os("AY_DEBUG_LAZY_SYNC").is_some() {
                                    let arg_detail =
                                        if let ay_core::term::TermData::App(_, args) =
                                            $self.ctx.terms.get(term)
                                        {
                                            args.iter()
                                                .map(|&x| format!("{:?}", $self.ctx.terms.get(x)))
                                                .collect::<Vec<_>>()
                                                .join(" | ")
                                        } else {
                                            String::new()
                                        };
                                    safe_eprintln!(
                                        "[lazy-sync] iter={} term={} {:?} value={} args=[{}]",
                                        _iteration,
                                        term.0,
                                        $self.ctx.terms.get(term),
                                        value,
                                        arg_detail
                                    );
                                }
                            }
                        }
                        theory.replay_learned_cuts();
                        // #qf-auflia-fc-diseq-sync: see the eager arm.
                        let _islp_synced_diseq_facts =
                            $crate::pipeline_fns::assert_top_level_arith_diseq_facts(
                                &$self.ctx.terms,
                                &$self.ctx.assertions,
                                &mut theory,
                            );

                        // DEBUG(#6683): count asserted atoms
                        if _iteration < 3 {
                            let _dbg_asserted: Vec<_> = $crate::iter_var_to_term_sorted(&local_var_to_term)
                                .filter(|(var, term)| {
                                    let is_dynamic = !base_vars.contains(var);
                                    let is_active = is_dynamic || base_active_atoms.contains(term);
                                    $crate::is_theory_atom(&$self.ctx.terms, *term) && is_active
                                })
                                .map(|(var, term)| {
                                    let val = model.get(var as usize).copied()
                                        .or_else(|| solver.value(SatVariable::new(var)));
                                    (term.0, val)
                                })
                                .collect();
                            if crate::debug_dpll_enabled() {
                                safe_eprintln!(
                                    "[{}] iter={} asserted_atoms={} base_active={}",
                                    $tag, _iteration, _dbg_asserted.len(), base_active_atoms.len()
                                );
                            }
                        }

                        // Inc0-0c: round counter + per-round LIA check-call
                        // delta (AY_LIA_INSTRUMENT-gated, write-only).
                        ay_lia::instrument::bump_split_round();
                        let _islp_instr_checks_before =
                            ay_lia::instrument::check_calls_now();
                        let _islp_theory_start = ay_core::time::Instant::now();
                        let theory_result = ay_core::TheorySolver::check(&mut theory);
                        _islp_timing.dpll.theory_check += _islp_theory_start.elapsed();

                        // AY_UFLIA_PHASE=2 per-round timeline (measurement-only).
                        if $crate::uflia_phase_round_debug() {
                            safe_eprintln!(
                                "[uflia-round] tag={} iter={} sat_cum={:.2}s theory_cum={:.2}s theory_this={:.3}s result={} conflicts={} decisions={} lia_checks_this={}",
                                $tag,
                                _iteration,
                                _islp_timing.dpll.sat_solve.as_secs_f64(),
                                _islp_timing.dpll.theory_check.as_secs_f64(),
                                _islp_theory_start.elapsed().as_secs_f64(),
                                // Inc0-0c round anatomy: name the split/model-eq
                                // variants previously lumped as "other".
                                match &theory_result {
                                    ay_core::TheoryResult::Sat => "sat",
                                    ay_core::TheoryResult::Unsat(_) => "unsat",
                                    ay_core::TheoryResult::UnsatWithFarkas(_) => "unsat-farkas",
                                    ay_core::TheoryResult::NeedSplit(_) => "need-split",
                                    ay_core::TheoryResult::NeedDisequalitySplit(_) => "need-diseq-split",
                                    ay_core::TheoryResult::NeedModelEquality(_) => "need-model-eq",
                                    ay_core::TheoryResult::NeedModelEqualities(_) => "need-model-eqs",
                                    ay_core::TheoryResult::NeedLemmas(_) => "need-lemmas",
                                    ay_core::TheoryResult::NeedStringLemma(_) => "need-string-lemma",
                                    ay_core::TheoryResult::Unknown => "unknown",
                                    _ => "other",
                                },
                                solver.num_conflicts(),
                                solver.num_decisions(),
                                ay_lia::instrument::check_calls_now()
                                    .saturating_sub(_islp_instr_checks_before)
                            );
                        }

                        // M-A2 lazy-persistent-combiner SHADOW hook
                        // (ARRAY-PROCEDURE-CLOSER-BLUEPRINT §5 A2). Debug-only,
                        // only present for AUFLIA. Runs AFTER the authoritative
                        // fresh check() so the fresh verdict (`theory_result`) is
                        // available to diff against. The hook drives a
                        // create-once + warm-reset persistent combiner over the
                        // SAME synced literals and compares verdict + reason-set;
                        // it NEVER mutates `theory_result` or any authoritative
                        // state (fresh stays authoritative). Folds out in release.
                        $(
                            #[cfg(debug_assertions)]
                            {
                                let $sh_result: &ay_core::TheoryResult = &theory_result;
                                let $sh_lits: &Vec<(TermId, bool)> = &_islp_shadow_lits;
                                let $sh_atoms: &HashSet<TermId> = &base_active_atoms;
                                let $sh_lemmas: &Vec<ay_core::TheoryLemma> = &_islp_theory_lemmas;
                                $sh_expr;
                            }
                        )?

                        // DEBUG(#6683): trace theory results + conflict details
                        if crate::debug_dpll_enabled()
                            && (_iteration < 10 || _iteration % 1000 == 0)
                        {
                            match &theory_result {
                                ay_core::TheoryResult::Unsat(ref ct) => {
                                    safe_eprintln!(
                                        "[{}] split_iter={} dpll_iter={} UNSAT conflict_len={} terms={:?}",
                                        $tag, _iteration, state.round_trips, ct.len(),
                                        ct.iter().map(|l| (l.term.0, l.value)).collect::<Vec<_>>()
                                    );
                                }
                                ay_core::TheoryResult::UnsatWithFarkas(ref cf) => {
                                    safe_eprintln!(
                                        "[{}] split_iter={} dpll_iter={} UnsatWithFarkas conflict_len={} terms={:?}",
                                        $tag, _iteration, state.round_trips, cf.literals.len(),
                                        cf.literals.iter().map(|l| (l.term.0, l.value)).collect::<Vec<_>>()
                                    );
                                }
                                other => {
                                    safe_eprintln!(
                                        "[{}] split_iter={} dpll_iter={} theory_result={:?}",
                                        $tag, _iteration, state.round_trips, std::mem::discriminant(other)
                                    );
                                }
                            }
                        }

                        // #8067: Collect theory phase hints before the theory is dropped.
                        // The simplex model is still valid from the check() call above,
                        // so suggest_phase() returns LP-consistent polarities.
                        _islp_saved_phase_hints.clear();
                        for (&term, &var_idx) in local_term_to_var.iter() {
                            // #8785: Do not let LP-model phase hints overwrite
                            // the explicit branch bias for split atoms created
                            // inside this refinement loop. Expression splits
                            // are introduced exactly when the current LP model
                            // has E == F, so both corrective branches
                            // (E <= F-1 and E >= F+1, or strict real variants)
                            // evaluate false against that model. Saving those
                            // false hints erases the split handler's
                            // deterministic branch preference and forces CDCL
                            // to rediscover an ordering through many LRA
                            // conflicts. Base atoms still keep theory phase
                            // guidance.
                            if !base_vars.contains(&var_idx) {
                                continue;
                            }
                            if let Some(phase) = ay_core::TheorySolver::suggest_phase(&theory, term) {
                                _islp_saved_phase_hints.push((var_idx, phase));
                            }
                        }

                        // Save per-theory statistics before dispatch may drop theory (#6579).
                        _islp_last_theory_stats = ay_core::TheorySolver::collect_statistics(&theory);

                        // Export structural snapshot for the next iteration (#6590).
                        // This saves the atom cache so the next theory creation skips parsing.
                        _islp_theory_snapshot = <_ as ay_core::TheorySolver>::export_structural_snapshot(&theory);

                        // Inc0-0d: quantify the G1 discard — how many theory
                        // propagations this round's combiner derived that die
                        // with it (the material Inc1 would harvest). Gated on
                        // AY_LIA_INSTRUMENT; runs AFTER the snapshot export and
                        // only on non-Sat rounds (the Sat path still reads the
                        // check()-time model for extraction, which a propagate()
                        // simplex refresh could perturb). Instrumented runs are
                        // diagnostics; unset ⇒ this block is a single relaxed
                        // load, byte-identical.
                        if ay_lia::instrument::enabled_pub()
                            && !matches!(theory_result, ay_core::TheoryResult::Sat)
                        {
                            let _islp_round_props =
                                ay_core::TheorySolver::propagate(&mut theory).len() as u64;
                            let _islp_round_pending =
                                ay_core::TheorySolver::drain_pending_propagations(&mut theory)
                                    .len() as u64;
                            ay_lia::instrument::add_round_props_discarded(
                                _islp_round_props,
                                _islp_round_pending,
                            );
                        }
                        pipeline_incremental_split_lazy_dispatch_theory_result!(
                            'split_loop, $self, solver, state,
                            tag: $tag,
                            theory,
                            theory_result: theory_result,
                            export_theory: |$export_theory| $export_expr,
                            local_term_to_var, local_var_to_term, local_next_var,
                            _islp_added_split_clauses, _islp_last_split_values, _islp_model_eq_tracker,
                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state, _islp_theory_lemmas, _islp_theory_lemma_seen,
                            _islp_negations, proof_enabled,
                            _islp_local_clausification_proofs, _islp_local_original_clause_theory_proofs,
                            sat_handler: {
                                pipeline_store_sat_model!(
                                    'split_loop, $self, solver, model,
                                    local_term_to_var, local_var_to_term, local_next_var,
                                    _islp_timing, theory, $theory_var, $extract,
                                    pre_store: { let _ = solver.pop(); }
                                );
                            },
                            remaining_arms: {
                                ay_core::TheoryResult::NeedStringLemma(_islp_sl) => {
                                    $(
                                        _islp_string_lemma_requests += 1;
                                        if _islp_string_lemma_requests >= $max_slr {
                                            let _ = solver.pop();
                                            $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                                            $self.last_result = Some(SolveResult::Unknown);
                                            break 'split_loop Ok(SolveResult::Unknown);
                                        }
                                        pipeline_export_theory_state!(
                                            theory, $export_theory, $export_expr,
                                            _islp_learned_cuts, _islp_seen_hnf_cuts, _islp_dioph_state
                                        );
                                        drop(theory);
                                        let $sl_lemma = _islp_sl;
                                        let $sl_negations = &mut _islp_negations;
                                        let (_islp_new_sl_clauses, _islp_sl_stall): (Vec<Vec<TermId>>, bool) = $sl_handler;
                                        if _islp_sl_stall {
                                            let _ = solver.pop();
                                            $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                                            $self.last_result = Some(SolveResult::Unknown);
                                            break 'split_loop Ok(SolveResult::Unknown);
                                        }
                                        for _sl_clause in &_islp_new_sl_clauses {
                                            $crate::executor::theories::split_incremental::apply_string_lemma_incremental(
                                                &$self.ctx.terms, solver,
                                                &mut local_term_to_var, &mut local_var_to_term,
                                                &mut local_next_var, &mut _islp_negations, _sl_clause,
                                            );
                                            if proof_enabled {
                                                let _ = $self.proof_tracker.add_theory_lemma(
                                                    _sl_clause.to_vec(),
                                                );
                                            }
                                        }
                                        _islp_negations.sync_pending(&mut $self.ctx.terms);
                                        _islp_string_lemma_clauses.extend(_islp_new_sl_clauses);
                                        continue;
                                    )?
                                    let _ = solver.pop();
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    break 'split_loop Ok(SolveResult::Unknown);
                                }
                                ay_core::TheoryResult::Unknown => {
                                    let _ = solver.pop();
                                    $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                                    $self.last_result = Some(SolveResult::Unknown);
                                    break 'split_loop Ok(SolveResult::Unknown);
                                }
                                other => unreachable!("unhandled TheoryResult variant in split loop: {other:?}"),
                            }
                        );
                    }
                    SatResult::Unsat(_) => {
                        // SLIA soundness guard (#6273, #6688): if string lemma
                        // clauses were added, SAT UNSAT may be caused by the
                        // guard literals over-constraining the solver. Return
                        // Unknown instead of claiming UNSAT.
                        $(
                            let _ = $max_slr; // anchor syntax variable for $()?
                            if !_islp_string_lemma_clauses.is_empty() {
                                let _ = solver.pop();
                                $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
                                $self.last_result = Some(SolveResult::Unknown);
                                break 'split_loop Ok(SolveResult::Unknown);
                            }
                        )?
                        // UNSAT proof capture + pop: shared macro (#5814 Packet 3)
                        pipeline_build_unsat_proof_with_pop!(
                            'split_loop, $self, solver,
                            local_var_to_term, _islp_negations, proof_enabled,
                            _islp_local_clausification_proofs, _islp_local_original_clause_theory_proofs
                        );
                    }
                    SatResult::Unknown => {
                        $self.last_model = None;
                        let _ = solver.pop();
                        if $self.last_unknown_reason.is_none() {
                            $self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        }
                        $self.last_result = Some(SolveResult::Unknown);
                        break 'split_loop Ok(SolveResult::Unknown);
                    }
                    #[allow(unreachable_patterns)]
                    _ => unreachable!(),
                }
            }

            // Too many splits - return unknown
            let _ = solver.pop();
            if $self.last_unknown_reason.is_none() {
                $self.last_unknown_reason = Some(UnknownReason::SplitLimit);
            }
            $self.last_result = Some(SolveResult::Unknown);
            Ok(SolveResult::Unknown)
        };

        state.scratch_var_to_term = local_var_to_term;
        pipeline_split_epilogue!(
            $self, _islp_timing, _islp_total_start,
            _islp_last_theory_stats, _islp_result,
            eager: {},
            restore: { $self.incr_theory_state = Some(state); }
        )
    }};
}
