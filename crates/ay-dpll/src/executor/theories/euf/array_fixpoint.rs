// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array+EUF solve entry points and axiom fixpoint loops.

use super::super::super::Executor;
use super::{reachable_term_set, ArrayAxiomMode};
use crate::combined_solvers::combiner::{
    CrossTheoryEqualityReplay, EufArrayNotifyReplayState, TheoryCombiner,
};
use crate::executor::theories::solve_harness::TheoryModels;
use crate::executor::theories::MAX_SPLITS_ARRAY_EUF;
use crate::executor_types::{Result, SolveResult};
use crate::preprocess::PreprocessingPass;
// #8529: Use deterministic hash sets in all builds.
use ay_arrays::{ArrayPropagatedEqualityReplay, ExactSelectModelEqKey};
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{Sort, TermId};

#[derive(Clone, Copy)]
struct ArrayAxiomPlan {
    eager_row: bool,
    eager_row2b: bool,
    assertion_budget: Option<usize>,
}

/// Whether `root` contains a symbolic array-default application.
///
/// The ArrayEUF scalar-alias fast path restores Int substitutions through the
/// arithmetic model, but its Bool recovery can only evaluate Boolean structure
/// whose leaves are already SAT/LIA-backed. A Bool `(default a)` eliminated as
/// `p -> (default a)` has no surviving SAT literal in the all-true fast path,
/// so accepting that substitution would restore the original assertion with an
/// unpinned `p` and default term. Keep this shape on the normal ArrayEUF solve,
/// which constructs the committed default literal and array interpretation.
fn contains_symbolic_array_default(terms: &ay_core::TermStore, root: TermId) -> bool {
    let mut stack = vec![root];
    let mut seen = HashSet::default();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermData::App(sym, args) = terms.get(term) {
            if sym.name() == "default"
                && args.len() == 1
                && matches!(terms.sort(args[0]), Sort::Array(_))
            {
                return true;
            }
        }
        stack.extend(terms.children(term));
    }
    false
}

impl ArrayAxiomPlan {
    fn from_mode(mode: ArrayAxiomMode) -> Self {
        match mode {
            ArrayAxiomMode::EagerAll => Self {
                eager_row: true,
                eager_row2b: true,
                assertion_budget: None,
            },
            ArrayAxiomMode::LazyRow2FinalCheck => Self {
                eager_row: true,
                eager_row2b: false,
                // Fixed built-in budget (200): validated default for the lazy
                // ROW2 final-check route; batteries-included, no env override.
                assertion_budget: Some(200),
            },
        }
    }
}

impl Executor {
    /// Run exact finite-array closure over an owned, preprocessed assertion
    /// window, returning that window with every generated axiom appended.
    ///
    /// Combined routes build their final solver input in a local `Vec` and only
    /// install it immediately before dispatch. A route-independent eager pass
    /// cannot see equalities created by their legacy ROW/fixpoint preprocessing,
    /// while running before store-flat substitution retains dead aliases. This
    /// scoped swap makes the exact pass a post-preprocessing operation without
    /// leaking the temporary assertion view into the public scope.
    pub(in crate::executor) fn close_finite_arrays_in_owned_assertion_window(
        &mut self,
        assertions: Vec<TermId>,
        extra_roots: &[TermId],
    ) -> Vec<TermId> {
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, assertions);
        let _ = self.add_finite_index_array_closure_with_roots(extra_roots);
        std::mem::replace(&mut self.ctx.assertions, saved_assertions)
    }

    /// Whether the active assertion/assumption roots contain an explicit
    /// symbolic array-default term.  Such terms require the carrier-sensitive
    /// default fixpoint even when the BV path's select-count throttle would
    /// otherwise skip general array saturation.
    pub(in crate::executor) fn has_symbolic_array_default_in_roots(
        &self,
        extra_roots: &[TermId],
    ) -> bool {
        self.ctx
            .assertions
            .iter()
            .chain(extra_roots)
            .copied()
            .any(|root| contains_symbolic_array_default(&self.ctx.terms, root))
    }

    /// Solve using combined EUF + Arrays theory.
    ///
    /// Uses `solve_incremental_split_loop_pipeline!` with `eager_extension: true`
    /// so array ROW2 axioms discovered during `check()` are injected inline via
    /// `ExtCheckResult::AddClauses` instead of requiring O(N) full SAT re-solve
    /// round-trips through the outer loop (#6546 Packet 6).
    pub(crate) fn solve_array_euf(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        // Push/pop incremental mode: use the persistent no-split incremental
        // pipeline that only processes scoped assertions, avoiding phantom
        // axioms from dead terms in the append-only TermStore (#6726).
        if self.incremental_mode {
            let _ = self.add_finite_index_array_closure();
            self.add_const_store_array_extensionality();
            // Const/store extensionality over an infinite outer carrier can
            // synthesize an equality between array-valued cells whose nested
            // carrier is finite. Close that newly exposed final surface before
            // the persistent encoder snapshots it.
            let _ = self.add_finite_index_array_closure();
            let result = self.solve_array_euf_incremental();
            return self.fail_close_incomplete_finite_array_sat(result);
        }

        // Snapshot the user-facing assertions before destructive in-place
        // substitution (store-flat inlining, alias substitution) rewrites them.
        // The trivially-true fast path below discards `last_model`; restoring
        // these originals lets the model-output layer resolve get-value/get-model
        // queries (e.g. `(= a (store ...))`, `(= i 5)`) from the committed
        // equalities instead of returning default 0/empty values (#5450).
        let pre_solve_assertions = self.ctx.assertions.clone();

        // SOUNDNESS (#dt-set-ite-lift wrong-sat): Shannon-expand
        // `(select (ite c A B) i)` -> `(ite c (select A i) (select B i))` so the
        // inner `select`-over-`store` reaches the ROW axioms (a Bool/array-valued
        // ite over which the array fixpoint otherwise treats `select(ite …)` as an
        // opaque atom). The QF_UF/AUFLIA routes already lift; this array-EUF route
        // did not.
        self.ctx.assertions = self.ctx.terms.lift_arithmetic_ite_all(&self.ctx.assertions);

        // Normalize assertion grouping up front so array axiom generation sees
        // the same surface for `(assert (and ...))` and multiple `(assert ...)`
        // forms (#6885).
        let mut flatten_pass = crate::preprocess::FlattenAnd::new();
        flatten_pass.apply(&mut self.ctx.terms, &mut self.ctx.assertions);

        // #6820: Inline store-flat array equalities before axiom generation.
        // Store-flat benchmarks (storecomm_*_sf_*, storeinv_*_sf_*, swap_*_sf_*)
        // assert chains of (= a_N (store a_{N-1} idx val)). Substituting each
        // a_N with its store expression converts select(a_N, k) into
        // select(store(...), k), which directly triggers ROW axioms.
        let pre_subst_len = self.ctx.assertions.len();
        super::super::solve_harness::substitute_store_flat_equalities(
            &mut self.ctx.terms,
            &mut self.ctx.assertions,
        );
        // Collapse pure top-level array-variable aliases `(= a1 a0)`
        // (#auflia-alias wrong-UNSAT). VariableSubstitution skips Array sorts, so
        // such an alias survives into the eager array-axiom scan, which ranges
        // over the WHOLE term store (QF reachability scoping is off here) and
        // over-relates `select`/`store` terms built on BOTH names across several
        // array (dis)equalities — a spurious cross-assertion conflict / false
        // theorem (the arr_lia561 store-distinct + alias family). Substituting
        // the non-canonical name by the representative is equisatisfiable (a
        // top-level `(= a b)` forces them equal in every model) and removes the
        // duplicate name so the spurious relation cannot form.
        // Soundness gate (#bug1b-alias-quant): the alias collapse is only
        // equisatisfiable for quantifier-free problems. Once a universal has been
        // instantiated/Skolemized, dropping a top-level `(= a c)` whose array
        // still occurs in the resulting ground terms is NOT equisatisfiable and
        // yields spurious UNSAT (`forall x. select c x = f x` with `(= a c)` →
        // z3 sat, ay unsat). Skip it when the original problem had a quantifier —
        // a completeness-only forgone simplification, never a false-accept.
        let array_alias_pairs = if self.original_problem_had_quantifiers {
            Vec::new()
        } else {
            super::super::solve_harness::substitute_array_var_aliases(
                &mut self.ctx.terms,
                &mut self.ctx.assertions,
            )
        };
        for (from, to) in array_alias_pairs {
            self.recorded_var_substitutions.insert(from, to);
        }
        // When store-flat substitution removed defining equalities, scope the
        // axiom fixpoint to terms reachable from the surviving assertions.
        // Without this, dead array variables (still in the TermStore) generate
        // thousands of spurious axioms.
        let store_flat_scoped = self.ctx.assertions.len() < pre_subst_len;
        // #8785: The AUFLIA fast path routes formulas without substantive
        // arithmetic to ArrayEUF. Preserve that route, but substitute supported
        // non-array aliases such as `(= i 3)` before array axiom seeding so
        // ROW1/ROW2 can see concrete store/select index matches. This path has
        // recovery below for Int/Bool aliases; leave unsupported substitutions
        // out of the solve path rather than producing incomplete models.
        let mut array_alias_var_subst = crate::preprocess::VariableSubstitution::new_skip_arrays();
        let mut alias_assertions = self.ctx.assertions.clone();
        let alias_seed_changed =
            array_alias_var_subst.apply(&mut self.ctx.terms, &mut alias_assertions);
        let alias_substitutions_supported =
            array_alias_var_subst
                .substitutions()
                .iter()
                .all(|(&from, &to)| match self.ctx.terms.sort(from) {
                    Sort::Int => true,
                    Sort::Bool => !contains_symbolic_array_default(&self.ctx.terms, to),
                    _ => false,
                });
        if alias_seed_changed && alias_substitutions_supported {
            self.ctx.assertions = alias_assertions;
            // Record eliminated-variable definitions for model completion at
            // finalize time (model/completion.rs).
            self.record_var_substitutions(&array_alias_var_subst);
        } else {
            array_alias_var_subst = crate::preprocess::VariableSubstitution::new_skip_arrays();
        }

        // Exact finite-index array coverage must run on the POST-substitution
        // surface. Expanding first embeds every store-flat definition inside a
        // generated biconditional, making the subsequent substitution retain
        // the alias and multiplying a cheap SSA chain by its whole finite
        // domain. The route-independent pre-dispatch pass defers QF_AX/DtAx to
        // this site for the same reason.
        let _ = self.add_finite_index_array_closure();

        // Restricted extensionality for `const-array = store-chain` over an
        // infinite index domain (#array-const-store-ext). This also belongs
        // after substitution so dead store-flat aliases do not seed axioms.
        self.add_const_store_array_extensionality();

        // Enable reachability scoping when store-flat substitution removed
        // defining equalities (dead array vars) OR when finite-domain
        // expansion / skolemization left ghost quantifier `Var` terms in the
        // store. In the ghost case, scoping is what keeps the array fixpoint
        // from treating a now-free bound variable (e.g. `(select a v)` from an
        // expanded `(forall ((v Bool)) …)`) as an extensionality / ROW witness
        // index — sharing one free `Var` across many array (dis)equalities
        // over-constrains the problem and yields a spurious UNSAT (false
        // theorem). The reachable set excludes such unreachable ghosts while
        // legitimate fixpoint-created witnesses (idx >= start_len) and
        // assertion-reachable terms stay in scope. (#dis514 wrong-unsat)
        //
        // Perf: the cheap `store_has_free_var` tag scan gates the more
        // expensive `reachable_term_set` DFS so quantifier-free problems (no
        // `Var` terms at all — the common case) skip the ghost check entirely.
        let scoped = store_flat_scoped || self.store_has_free_var();
        if scoped {
            let start_len = self.ctx.terms.len();
            let reachable = reachable_term_set(&self.ctx.terms, &self.ctx.assertions);
            // Re-confirm a genuine unreachable ghost before committing the scope
            // when the only trigger was a `Var` term (store-flat scoping is
            // unconditional). If every `Var` is reachable, no ghost exists and we
            // leave the (full) scope unrestricted.
            if store_flat_scoped || self.has_unreachable_var_ghost(&reachable) {
                self.array_axiom_scope = Some((reachable, start_len));
            }
        }

        // #qfax-t3-atom-space: decide the arrays BCP-lane mode on the same
        // assertion surface the fixpoint below sees. The storeinv shape —
        // a top-level POSITIVE store-store equality (`(= (store …) (store …))`,
        // both PDPAR'05 storeinv and storeinv_invalid assert the interleaved
        // chains equal) — keeps the legacy BCP-time arrays lanes: those files
        // lean on the singleton-support steering
        // (`singleton_support_propagations`), and the corpus A/B measured
        // 3-20x conflict growth there with the lanes off. Every other QF_AX
        // shape (storecomm/swap: only NEGATED store-chain equalities plus
        // variable-defining `(= a (store …))` equalities) demotes the lanes —
        // the eager ROW instance surface + EUF congruence + SAT BCP carry the
        // search, and the lanes were measured as ~60% of on-CPU time with
        // zero conflicts contributed (t3 reds: 17.9s->2.9s;
        // unknown@T:60->unsat ~30s; 0 verdict changes + 1 unknown->unsat
        // across the 300-file corpus sweep). `--dpll-force-qfax-arr-bcp-lanes`
        // restores the legacy lanes unconditionally (safety valve, mirrors
        // --dpll-no-prop-feedback). Completeness/soundness are owned by the full
        // `check()` + final_check ladder either way (see the
        // `arrays_bcp_lanes` field docs in combiner.rs).
        let arrays_bcp_lanes = self.has_top_level_positive_store_store_equality()
            || ay_core::theory_disable_flags().force_qfax_arr_bcp_lanes;
        if ay_core::misc_cli_flags().qfax_lanes_debug {
            eprintln!("[qfax_lanes] arrays_bcp_lanes={arrays_bcp_lanes}");
        }

        // Use the full array axiom fixpoint (extensionality + ROW2b + store
        // decomposition) for QF_AX. The lighter fixpoint_5 with ROW2b budget=0
        // misses upward select propagation needed for storeinv cross-swap _nf_
        // patterns where let-expanded nested stores have no intermediate variable
        // equalities (#4304, #6282).
        //
        // #6546 Packet 4: eager ROW1+ROW2, lazy ROW2b. The fully lazy
        // mode (LazyRowFinalCheck) was tested in W4:3050 and regressed all
        // storeinv sizes. EagerAll was tested in W4:3055 and still timed out
        // on size7 — the bottleneck is the DPLL(T) refinement loop overhead,
        // not the eager clause surface.
        self.run_array_axiom_fixpoint_at(0, ArrayAxiomMode::LazyRow2FinalCheck);

        // The legacy ROW pass can itself expose array-valued cell equalities.
        // Re-enter the idempotent exact closure on that final assertion surface
        // so nested finite arrays are closed before either the trivial-SAT exit
        // or DPLL(T) sees the window.
        let _ = self.add_finite_index_array_closure();

        // #8635: If the caller interrupted or the deadline expired during the
        // fixpoint loop, return Unknown immediately instead of proceeding to
        // the DPLL(T) pipeline.
        if self.should_abort_theory_loop() {
            if scoped {
                self.array_axiom_scope = None;
            }
            return Ok(SolveResult::Unknown);
        }

        // Clear the temporary scope so the DPLL(T) lazy axiom path isn't
        // restricted.
        if scoped {
            self.array_axiom_scope = None;
        }

        // Fast path: if all assertions were eliminated by store-flat
        // substitution and axiom generation (e.g., select(store(a,i,v),i)=v
        // simplified to true, defining equality dropped), return SAT
        // immediately. The pipeline's TheoryExtension scans the full TermStore
        // and generates spurious NeedModelEquality for dead terms, causing
        // false Unknown with max_splits=1.
        {
            let true_term = self.ctx.terms.true_term();
            if self.ctx.assertions.is_empty() || self.ctx.assertions.iter().all(|&a| a == true_term)
            {
                if !self.finite_array_expansion.is_complete() {
                    self.ctx.assertions = pre_solve_assertions;
                    let _ = self.revoke_provisional_sat_if_finite_array_incomplete(true);
                    return Ok(SolveResult::Unknown);
                }
                // Restore the user-facing assertions so the model-output layer
                // can resolve get-value/get-model from the committed equalities
                // (store-flat/alias substitution rewrote them in place) (#5450).
                self.ctx.assertions = pre_solve_assertions;
                // Recover the values of variables eliminated by alias
                // substitution (e.g. `(= i 5)` -> `i = 5`) into a LIA model so
                // Int get-value queries print the asserted value, not 0.
                let lia_model = if array_alias_var_subst.substitutions().is_empty() {
                    None
                } else {
                    let mut lia_model = ay_lia::LiaModel {
                        values: Default::default(),
                    };
                    // Direct original equalities carry stronger authority than
                    // the generic zero used to complete an unconstrained
                    // opaque array observation. Recover `x = 5`, transfer it
                    // through `x = default(a)`, and only then replay the
                    // eliminated `x -> default(a)` definition.
                    super::super::lia::recover_lia_equalities_from_assertions(
                        &self.ctx.terms,
                        &self.ctx.assertions,
                        &mut lia_model,
                    );
                    super::super::lia::backfill_opaque_app_values_from_equalities(
                        &self.ctx.terms,
                        &self.ctx.assertions,
                        &mut lia_model,
                    );
                    super::super::lia::recover_substituted_lia_values(
                        &self.ctx.terms,
                        &array_alias_var_subst,
                        &mut lia_model,
                    );
                    Some(lia_model)
                };
                let bool_overrides = lia_model
                    .as_ref()
                    .map(|lia| {
                        super::super::lia::recover_substituted_bool_values(
                            &self.ctx.terms,
                            &array_alias_var_subst,
                            &lia.values,
                        )
                    })
                    .unwrap_or_default();
                // Always provide a model object (not just when substitutions
                // exist): the SAT postcondition requires a model whenever the
                // restored assertions are not all `true`, and the empty model
                // still lets the output layer resolve array/selector values from
                // the restored assertions.
                let mut model = crate::executor::model::Model::empty();
                model.bool_overrides = bool_overrides.into_iter().collect();
                model.lia_model = lia_model;
                self.last_model = Some(model);
                self.last_model_validated = true;
                return Ok(SolveResult::Sat);
            }
        }

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        // Datatype registry for the combiner's D0 clash/acyclicity final-check
        // pass (DESIGN_lazy_dt.md stage D0). Empty (pass disabled) for
        // datatype-free problems; the DT+Array route (`solve_dt_ax`) and the
        // pure-DT `_DT_AX` widening both land here with datatypes present.
        let dt_info: Vec<(String, Vec<String>)> = self
            .ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_owned(), ctors.to_vec()))
            .collect();
        // Constructor selector signatures for the combiner's D1 lazy
        // tester/selector propagation pass (DESIGN_lazy_dt.md stage D1).
        // Registered only on this lane (blocksworld's actual routing:
        // solve_dt_ax -> solve_with_dt_axioms -> solve_array_euf).
        let dt_sel_info: Vec<(String, Vec<String>)> = dt_info
            .iter()
            .flat_map(|(_, ctors)| ctors.iter())
            .map(|ctor| {
                let sels: Vec<String> = self
                    .ctx
                    .constructor_selector_info(ctor)
                    .map(|info| info.iter().map(|(n, _)| n.clone()).collect())
                    .unwrap_or_default();
                (ctor.clone(), sels)
            })
            .collect();
        // Lazy-lane D2 split registry (stage D2): present ONLY while
        // `try_solve_dt_lazy` drives this pipeline; every other route sees
        // `None` and keeps its exact pre-D2 behavior.
        let dt_lazy_splits = self.dt_lazy_splits.clone();
        let result = self.with_isolated_incremental_state(None, |this| {
            // #8594: Persist array solver dedup sets across theory instances.
            // The non-persistent eager arm creates a fresh TheoryCombiner each
            // iteration, losing the requested_interface_eqs and requested_model_eqs
            // dedup sets. Without persistence, check_interface_equalities() and
            // check_row2_upward_with_guidance() re-request the same equalities
            // every iteration, exhausting the model equality round budget without
            // progress (storechain_colliding_qf_ax_7654 returns Unknown instead
            // of SAT).
            let mut _persistent_array_interface_eqs: ay_core::kani_compat::DetHashSet<(
                TermId,
                TermId,
            )> = ay_core::kani_compat::DetHashSet::default();
            let mut _persistent_array_model_eqs: ay_core::kani_compat::DetHashSet<(
                TermId,
                TermId,
            )> = ay_core::kani_compat::DetHashSet::default();
            let mut _persistent_array_exact_select_model_eqs: ay_core::kani_compat::DetHashSet<
                ExactSelectModelEqKey,
            > = ay_core::kani_compat::DetHashSet::default();
            let mut _persistent_euf_array_notify_edges = EufArrayNotifyReplayState::default();
            let mut _persistent_array_equality_replays: Vec<ArrayPropagatedEqualityReplay> =
                Vec::new();
            let mut _persistent_cross_theory_equality_replays: Vec<CrossTheoryEqualityReplay> =
                Vec::new();
            solve_incremental_split_loop_pipeline!(this,
                tag: "ArrayEUF",
                persistent_sat_field: persistent_sat,
                create_theory: {
                    let mut tc = TheoryCombiner::array_euf(&this.ctx.terms);
                    tc.set_interrupt(this.solve_interrupt.clone());
                    tc.set_deadline(this.solve_deadline.get());
                    // #qfax-t3-atom-space: demote BCP-time arrays lanes for
                    // non-storeinv shapes (computed above the fixpoint).
                    tc.set_arrays_bcp_lanes(arrays_bcp_lanes);
                    tc.register_datatypes(&dt_info);
                    tc.register_datatype_selectors(&dt_info, &dt_sel_info);
                    if let Some((dts, bases)) = &dt_lazy_splits {
                        tc.register_datatype_splits(dts, bases);
                    }
                    tc
                },
                extract_models: |theory| {
                    theory.scope_euf_model_to_roots(&this.ctx.assertions);
                    let (euf, arr) = theory.extract_euf_array_models();
                    theory.clear_euf_model_scope();
                    TheoryModels {
                        euf: Some(euf),
                        array: Some(arr),
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_ARRAY_EUF,
                pre_theory_import: |theory, _lc, _hc, _ds| {
                    // #8594: Import persisted array dedup sets into the fresh theory.
                    theory.import_array_requested_interface_eqs(&_persistent_array_interface_eqs);
                    theory.import_array_requested_model_eqs(&_persistent_array_model_eqs);
                    theory.import_array_exact_select_model_eq_keys(
                        &_persistent_array_exact_select_model_eqs,
                    );
                    theory.import_array_equality_replays(&_persistent_array_equality_replays);
                    theory.import_cross_theory_equality_replays(
                        &_persistent_cross_theory_equality_replays,
                    );
                    theory.import_euf_array_notify_replay_state(
                        &_persistent_euf_array_notify_edges,
                    );
                },
                post_theory_export: |theory| {
                    // #8594: Export array dedup sets before the theory is dropped.
                    _persistent_array_interface_eqs = theory.export_array_requested_interface_eqs();
                    _persistent_array_model_eqs = theory.export_array_requested_model_eqs();
                    _persistent_array_exact_select_model_eqs =
                        theory.export_array_exact_select_model_eq_keys();
                    theory.prune_current_euf_array_notify_replay_edges(
                        &mut _persistent_euf_array_notify_edges,
                    );
                    theory.prune_current_array_equality_replays(
                        &mut _persistent_array_equality_replays,
                    );
                    theory.prune_current_cross_theory_equality_replays(
                        &mut _persistent_cross_theory_equality_replays,
                    );
                    theory.append_current_euf_array_notify_replay_edges(
                        &mut _persistent_euf_array_notify_edges,
                    );
                    theory.append_current_array_equality_replays(
                        &mut _persistent_array_equality_replays,
                    );
                    theory
                        .append_current_cross_theory_equality_replays(
                            &mut _persistent_cross_theory_equality_replays,
                        );
                    (vec![], Default::default(), Default::default())
                },
                eager_extension: true,
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.expired()
                        // RSS discipline (#array-deadline-forward): poll the
                        // process-wide memory ceiling at split-loop
                        // boundaries too — repeated QF_AX subset re-solves
                        // grow the term store monotonically and the
                        // competition harness pairs the internal limit with
                        // a zero-grace external RSS watchdog. Protective
                        // only (Unknown), no-op when no ceiling is set.
                        || ay_sys::process_memory_exceeded()
                },
                // #8596: Pure ArrayEUF has no arithmetic solver. Triangle axioms
                // create (x <= y) atoms with no theory interpretation, causing
                // spurious EUF bool-congruence conflicts and false UNSAT.
                skip_arith_triangle: true
            )
        });

        let result = self.fail_close_incomplete_finite_array_sat(result);

        if matches!(result, Ok(SolveResult::Sat))
            && !array_alias_var_subst.substitutions().is_empty()
        {
            if let Some(ref mut model) = self.last_model {
                let lia_model = model.lia_model.get_or_insert_with(|| ay_lia::LiaModel {
                    values: Default::default(),
                });
                super::super::lia::recover_lia_equalities_from_assertions(
                    &self.ctx.terms,
                    &pre_solve_assertions,
                    lia_model,
                );
                super::super::lia::backfill_opaque_app_values_from_equalities(
                    &self.ctx.terms,
                    &pre_solve_assertions,
                    lia_model,
                );
                super::super::lia::recover_substituted_lia_values(
                    &self.ctx.terms,
                    &array_alias_var_subst,
                    lia_model,
                );
                let bool_overrides = super::super::lia::recover_substituted_bool_values(
                    &self.ctx.terms,
                    &array_alias_var_subst,
                    &lia_model.values,
                );
                model.bool_overrides.extend(bool_overrides);
            }
        }

        result
    }

    /// Solve QF_AX incrementally using SAT scope selectors (#6726).
    ///
    /// Maintains a persistent SAT solver and TseitinState that retain
    /// learned clauses and term-to-var mappings across check-sat calls.
    /// Uses SAT scope selectors (push/pop) for correct scoping, so only
    /// active assertions produce axioms — dead terms from popped scopes
    /// are never visible to the theory combiner.
    fn solve_array_euf_incremental(&mut self) -> Result<SolveResult> {
        // #8635: Early exit if already interrupted/timed out.
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        if self.active_store_select_value_contradiction() {
            self.last_result = Some(SolveResult::unsat());
            return Ok(SolveResult::unsat());
        }

        let model_roots = self.ctx.assertions.clone();
        // See solve_array_euf: D0 datatype pass registry (empty = disabled).
        let dt_info: Vec<(String, Vec<String>)> = self
            .ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_owned(), ctors.to_vec()))
            .collect();
        // See solve_array_euf: D1 selector registry (stage D1).
        let dt_sel_info: Vec<(String, Vec<String>)> = dt_info
            .iter()
            .flat_map(|(_, ctors)| ctors.iter())
            .map(|ctor| {
                let sels: Vec<String> = self
                    .ctx
                    .constructor_selector_info(ctor)
                    .map(|info| info.iter().map(|(n, _)| n.clone()).collect())
                    .unwrap_or_default();
                (ctor.clone(), sels)
            })
            .collect();
        // See solve_array_euf: lazy-lane D2 split registry (stage D2).
        let dt_lazy_splits = self.dt_lazy_splits.clone();
        solve_incremental_theory_pipeline!(self,
            tag: "ArrayEUF",
            create_theory: {
                let mut tc = TheoryCombiner::array_euf(&self.ctx.terms);
                tc.set_interrupt(self.solve_interrupt.clone());
                tc.set_deadline(self.solve_deadline.get());
                tc.register_datatypes(&dt_info);
                tc.register_datatype_selectors(&dt_info, &dt_sel_info);
                if let Some((dts, bases)) = &dt_lazy_splits {
                    tc.register_datatype_splits(dts, bases);
                }
                tc
            },
            extract_models: |theory| {
                theory.scope_euf_model_to_roots(&model_roots);
                let (euf, arr) = theory.extract_euf_array_models();
                theory.clear_euf_model_scope();
                TheoryModels {
                    euf: Some(euf),
                    array: Some(arr),
                    ..TheoryModels::default()
                }
            },
            track_theory_stats: true,
            set_unknown_on_error: false
        )
    }

    fn active_store_select_value_contradiction(&self) -> bool {
        let mut store_aliases = Vec::new();
        for &assertion in &self.ctx.assertions {
            if let Some((array, index, value)) = self.store_alias_assertion(assertion) {
                store_aliases.push((array, index, value));
            }
        }

        for &assertion in &self.ctx.assertions {
            let Some((positive, array, index, value)) = self.select_value_assertion(assertion)
            else {
                continue;
            };
            for &(alias, store_index, store_value) in &store_aliases {
                if alias != array || !self.terms_match(index, store_index) {
                    continue;
                }
                let values_match = self.terms_match(value, store_value);
                if (positive && !values_match) || (!positive && values_match) {
                    return true;
                }
            }
        }
        false
    }

    fn store_alias_assertion(&self, assertion: TermId) -> Option<(TermId, TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        self.store_alias_sides(args[0], args[1])
            .or_else(|| self.store_alias_sides(args[1], args[0]))
    }

    fn store_alias_sides(&self, array: TermId, store: TermId) -> Option<(TermId, TermId, TermId)> {
        if !matches!(self.ctx.terms.get(array), TermData::Var(_, _))
            || !matches!(self.ctx.terms.sort(array), Sort::Array(_))
        {
            return None;
        }
        let TermData::App(sym, args) = self.ctx.terms.get(store) else {
            return None;
        };
        if sym.name() == "store" && args.len() == 3 {
            Some((array, args[1], args[2]))
        } else {
            None
        }
    }

    fn select_value_assertion(&self, assertion: TermId) -> Option<(bool, TermId, TermId, TermId)> {
        if let Some((array, index, value)) = self.select_value_equality(assertion) {
            return Some((true, array, index, value));
        }
        let TermData::Not(inner) = self.ctx.terms.get(assertion) else {
            return None;
        };
        self.select_value_equality(*inner)
            .map(|(array, index, value)| (false, array, index, value))
    }

    fn select_value_equality(&self, assertion: TermId) -> Option<(TermId, TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        self.select_value_sides(args[0], args[1])
            .or_else(|| self.select_value_sides(args[1], args[0]))
    }

    fn select_value_sides(
        &self,
        select: TermId,
        value: TermId,
    ) -> Option<(TermId, TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(select) else {
            return None;
        };
        if sym.name() == "select" && args.len() == 2 {
            Some((args[0], args[1], value))
        } else {
            None
        }
    }

    fn terms_match(&self, lhs: TermId, rhs: TermId) -> bool {
        lhs == rhs || self.ctx.terms.get(lhs) == self.ctx.terms.get(rhs)
    }

    /// Run the array axiom fixpoint with extensionality + store decomposition (#6282).
    ///
    /// `dedup_protect` is the number of assertions at the front of
    /// `self.ctx.assertions` that must not be removed by deduplication.
    /// Callers that later `drain(dedup_protect..)` to extract newly-added axioms
    /// pass their snapshot length here so that `retain` cannot shrink the
    /// assertion list below that index (#6340).
    ///
    /// `mode` controls whether ROW/ROW2b axioms are generated eagerly or
    /// deferred to the runtime `ArraySolver` (#6546).
    pub(in crate::executor) fn run_array_axiom_fixpoint_at(
        &mut self,
        dedup_protect: usize,
        mode: ArrayAxiomMode,
    ) {
        let mut plan = ArrayAxiomPlan::from_mode(mode);
        if let Some(b) = plan.assertion_budget {
            plan.assertion_budget = Some(b * self.qfax_budget_multiplier);
        }
        self.run_array_axiom_fixpoint_at_plan(dedup_protect, plan, &[]);
    }

    #[cfg(test)]
    pub(in crate::executor) fn run_array_axiom_fixpoint_lazy_row_final_check_for_tests(
        &mut self,
        dedup_protect: usize,
    ) {
        self.run_array_axiom_fixpoint_at_plan(
            dedup_protect,
            ArrayAxiomPlan {
                eager_row: false,
                eager_row2b: false,
                assertion_budget: None,
            },
            &[],
        );
    }

    /// Run the array axiom fixpoint with extra root terms included in the
    /// reachable set for scope filtering (#6736). Used by check-sat-assuming
    /// paths where assumption terms contain array operations that need axioms
    /// but are not in `self.ctx.assertions`.
    fn run_array_axiom_fixpoint_at_plan(
        &mut self,
        dedup_protect: usize,
        plan: ArrayAxiomPlan,
        assumption_roots: &[TermId],
    ) {
        self.row_seeded_terms.clear();

        // In incremental mode, scope axiom generation to terms reachable from
        // current assertions (and assumption roots, if any). This prevents
        // phantom axioms from dead terms in popped scopes (#6726). Terms
        // created during the fixpoint (idx >= start_len) always pass the
        // scope check.
        if self.incremental_mode {
            let start_len = self.ctx.terms.len();
            let reachable = if assumption_roots.is_empty() {
                reachable_term_set(&self.ctx.terms, &self.ctx.assertions)
            } else {
                // Include assumption terms in the reachable set so
                // assumption-only array operations get axioms (#6736).
                let mut roots =
                    Vec::with_capacity(self.ctx.assertions.len() + assumption_roots.len());
                roots.extend_from_slice(&self.ctx.assertions);
                roots.extend_from_slice(assumption_roots);
                reachable_term_set(&self.ctx.terms, &roots)
            };
            self.array_axiom_scope = Some((reachable, start_len));
        }

        // #6820: Reset store-eq cache for this fixpoint invocation.
        // Store equalities are stable across inner rounds (they come from
        // the original formula), so we collect them once on the first scan.
        self.reset_array_congruence_caches();

        let eager_row = plan.eager_row;
        // #6546: Gated eager ROW2b. The default LazyRow2FinalCheck mode keeps
        // ROW2b lazy (eager_row2b=false) to avoid blowing up storecomm-family
        // benchmarks. However, storeinv_nf cross-swap benchmarks use unnamed
        // nested stores whose upward-select propagation is never triggered by
        // the runtime ArraySolver's event-driven queues, leaving the DPLL(T)
        // search with a model that satisfies ROW1/ROW2 locally but violates
        // extensionality globally — i.e. false SAT.
        //
        // Detect the storeinv_nf signature (an array pair with both a negatable
        // (= A B) atom AND an explicit select-diseq witness) and flip ROW2b on
        // with a small bounded budget. The bound is large enough to unroll a
        // 7-level chain (storeinv_nf_size7 has 7 store levels × ~2 selects each)
        // while still capping worst-case growth so regressions on non-storeinv
        // benchmarks are bounded. The `has_explicit_select_disequality_witness`
        // gate is the same predicate that the `already_diseq` fence in
        // `add_array_extensionality_axioms` uses, so it does not fire on the
        // false-UNSAT fence test `storeinv_invalid_t1_nf_00004` (which has no
        // top-level select-disequality witness in the negated case).
        // #perf1-storeinv / #perf5-qfax-storeinv: index-guided witness ROW
        // unroll. When the storeinv/swap chain+witness shape is detected, emit
        // the DECISIVE lemma set directly — 2 guarded ROW instances per store
        // level per witness index (see `add_witness_guided_chain_row_axioms`) —
        // instead of the legacy budget-scaled eager-ROW2b + store-base
        // decomposition surface, whose unfocused O(n²) clauses made the CDCL
        // search double per chain level (storeinv_nf_size9 6.1s → ~0.1s) and
        // never reached the raw-diseq QF_AX contradiction (unknown → unsat).
        // On truncation (`false`) the legacy path stays on unchanged.
        let witness_guided_rows = self.add_witness_guided_chain_row_axioms();
        let has_storeinv_witness = !witness_guided_rows
            && (self.has_storeinv_extensionality_witness()
            // #qf-ax-negated-swap: the swap/storeinv `_np_nf_` shape — one
            // top-level negated equality between two deep store chains, no
            // explicit select witness — needs the same eager-ROW2b rescue so
            // the fabricated `__ay_ext_diff` select unrolls down both chains.
            // Without it the lazy ArraySolver misses upward select propagation
            // and certifies a witness-less disequality: false SAT.
            || self.has_negated_deep_store_chain_array_equality());
        let eager_row2b = plan.eager_row2b || has_storeinv_witness;
        // Budget is per-inner-fixpoint; the outer loop can refresh it up to
        // 20 times. 256 is enough to unroll 9-level storeinv chains while
        // still capping worst-case growth if the gate misfires.
        // Batteries-included best-by-default: 256 unrolls 9-level storeinv
        // chains while capping worst-case growth if the gate misfires. No env
        // override (no-env-vars law) — this is the former unset default.
        let row2b_gate_budget: usize = 256 * self.qfax_budget_multiplier;
        if self.qfax_budget_multiplier > 1 && ay_core::misc_cli_flags().debug_ladder {
            eprintln!("[ladder] tier-2 fixpoint active, row2b_budget={row2b_gate_budget}");
        }
        // #6820: Budget controls to prevent exponential growth in the eager
        // axiom fixpoint. Storecomm-family benchmarks (N stores, same base)
        // cause O(N²) congruence axioms × ROW feedback loops. The DPLL(T)
        // ArraySolver handles any remaining axioms lazily via event-driven
        // queues.
        let fixpoint_start_terms = self.ctx.terms.len();
        // Best-by-default term budget; no env override (former unset default).
        let fixpoint_term_budget: usize = 10_000 * self.qfax_budget_multiplier;
        // #6820, #6367: For LazyRow2FinalCheck (QF_AUFLIA combined solver),
        // cap the clause (assertion) count. Excessive eager clauses slow
        // SAT solving by creating too many boolean variables for the DPLL
        // search. The DPLL(T) ArraySolver handles remaining axioms lazily
        // via event-driven queues, so a lower budget is safe.
        //
        // Budget history: 800 (#6820) -> 200 (#6367). The reduction from
        // 800 to 200 improves storeinv_nf_size9 from 535ms to 104ms (5.1x)
        // by reducing eager axiom term count from 2177 to 868 and JIT
        // dispatch atoms proportionally.
        //
        // #8804: Scale the budget when the storeinv extensionality witness
        // fires. The fixed 200-axiom budget bails out after ~4 outer rounds
        // on deep storeinv chains (_t3_*_sf_ai_00008+), which is shallower
        // than the chain depth. Without a deeper unroll the arrays theory
        // never sees the contradiction at the chain base (a1 = a2) and the
        // model builder invents an inconsistent witness, returning false
        // SAT. Scale proportionally to the detected chain depth so we only
        // pay for deeper unrolls when the storeinv signature is present.
        // Non-storeinv QF_AUFLIA benchmarks keep the original tight budget.
        let assertion_budget = match plan.assertion_budget {
            Some(base_budget) if has_storeinv_witness => {
                let chain_depth = self.max_top_level_store_store_equality_depth();
                // Roughly 120 axioms per chain level (sbd + ext +
                // store-value-cong + ROW clauses), with a floor of the
                // original budget so size<=4 chains are unaffected.
                let scaled = chain_depth.saturating_mul(120).max(base_budget);
                // Hard cap to bound worst-case if a pathological input
                // reports a very deep chain. 20 levels × 120 = 2400, which
                // is below the 10k fixpoint term budget so the term-budget
                // backstop still bounds the fixpoint cost.
                Some(scaled.min(2400))
            }
            other => other,
        };

        // #8635: Check interrupt/deadline between fixpoint iterations so
        // the array axiom loop responds to caller-set cancellation.
        let should_stop = self.make_should_stop();

        // #7890: Interleaved assertion budget check — enforce clause budget
        // within the inner fixpoint, not just between outer rounds. Without
        // this, a single outer round on QF_ALIA benchmarks with deep store
        // chains (ios_*, qlock-*, pointer-safe-*) can generate 10k+ clauses
        // from add_array_row_clauses and add_array_congruence_axioms before
        // the outer-loop budget check fires. The DPLL(T) ArraySolver handles
        // remaining axioms lazily via event-driven queues, so breaking early
        // is safe for LazyRow2FinalCheck (which has a finite assertion_budget).
        let assertion_budget_base = self.ctx.assertions.len();
        let assertion_growth_cap = assertion_budget.map(|b| assertion_budget_base + b);

        // #8785: Summary counters — emit final axiom tallies when
        // `--debug auflia-fix-summary` is set (the `AY_DEBUG_AUFLIA_FIX_SUMMARY`
        // env var still works as a fallback; see the tally site below).
        // Cheaper than per-axiom dumps and captures the shape of what the SAT solver consumes.
        let mut total_ext_axioms = 0_usize;
        let mut total_sv_axioms = 0_usize;
        let mut total_os_axioms = 0_usize;
        let mut total_sd_axioms = 0_usize;
        let mut total_ac_axioms = 0_usize;
        let mut total_row_axioms = 0_usize;
        let mut total_sbd_axioms = 0_usize;
        let mut total_seeded_row_terms = 0_usize;
        let mut total_seeded_row2b_terms = 0_usize;
        for _outer in 0..20_usize {
            if should_stop() {
                break;
            }
            let n = self.ctx.terms.len();
            // Array-default congruence: `a = b ⟹ default(a) = default(b)`.
            // Principled completion of extensionality for positive equalities
            // between arrays whose defaults are structurally determined (const /
            // store-over-const). Refutes spurious SAT on shapes like
            // `store(const 0, k, v) = const 1` that the single-Skolem
            // extensionality witness cannot catch. Independent of the
            // `select`-over-`ite` Shannon-lift in `solve_array_euf` (which only
            // rewrites `(select (ite …) i)` so the inner store reaches ROW); both
            // coexist. See `add_array_default_congruence_axioms` for the
            // soundness argument.
            self.add_array_default_congruence_axioms();
            self.add_array_default_store_axioms();
            let _assertions_before_ext = self.ctx.assertions.len();
            self.add_array_extensionality_axioms_up_to(fixpoint_start_terms);
            total_ext_axioms += self.ctx.assertions.len() - _assertions_before_ext;
            if ay_core::debug_channel_active(ay_core::DebugChannel::AufliaFix) {
                let added = self.ctx.assertions.len() - _assertions_before_ext;
                eprintln!(
                    "[auflia_fix] outer={} add_array_extensionality_axioms added {} axioms, term_count={}",
                    _outer,
                    added,
                    self.ctx.terms.len(),
                );
                for i in _assertions_before_ext..self.ctx.assertions.len() {
                    let t = self.ctx.assertions[i];
                    eprintln!(
                        "[auflia_fix]   ext axiom #{}: data={:?}",
                        t.0,
                        self.ctx.terms.get(t)
                    );
                }
            }
            {
                let mut row2b_used = 0_usize;
                for _round in 0..20_usize {
                    if should_stop() {
                        break;
                    }
                    let inner_n = self.ctx.terms.len();
                    let _aa0 = self.ctx.assertions.len();
                    self.add_store_value_congruence_axioms();
                    total_sv_axioms += self.ctx.assertions.len() - _aa0;
                    if ay_core::debug_channel_active(ay_core::DebugChannel::AufliaFix) {
                        let d = self.ctx.assertions.len() - _aa0;
                        if d > 0 {
                            eprintln!(
                                "[auflia_fix] outer={} round={} store_value_cong added {} axioms, terms={}",
                                _outer,
                                _round,
                                d,
                                self.ctx.terms.len(),
                            );
                            for i in _aa0.._aa0 + d.min(4) {
                                let t = self.ctx.assertions[i];
                                eprintln!(
                                    "[auflia_fix]   sv axiom #{}: data={:?}",
                                    t.0,
                                    self.ctx.terms.get(t)
                                );
                            }
                        }
                    }
                    if let Some(cap) = assertion_growth_cap {
                        if self.ctx.assertions.len() > cap {
                            break;
                        }
                    }
                    let _aa1 = self.ctx.assertions.len();
                    self.add_store_other_side_congruence_axioms();
                    total_os_axioms += self.ctx.assertions.len() - _aa1;
                    if ay_core::debug_channel_active(ay_core::DebugChannel::AufliaFix) {
                        let d = self.ctx.assertions.len() - _aa1;
                        if d > 0 {
                            eprintln!(
                                "[auflia_fix] outer={} round={} store_other_side_cong added {} axioms, terms={}",
                                _outer,
                                _round,
                                d,
                                self.ctx.terms.len(),
                            );
                            for i in _aa1.._aa1 + d.min(4) {
                                let t = self.ctx.assertions[i];
                                eprintln!(
                                    "[auflia_fix]   os axiom #{}: data={:?}",
                                    t.0,
                                    self.ctx.terms.get(t)
                                );
                            }
                        }
                    }
                    if let Some(cap) = assertion_growth_cap {
                        if self.ctx.assertions.len() > cap {
                            break;
                        }
                    }
                    let _aa2 = self.ctx.assertions.len();
                    self.add_store_disjunctive_index_axioms();
                    total_sd_axioms += self.ctx.assertions.len() - _aa2;
                    if ay_core::debug_channel_active(ay_core::DebugChannel::AufliaFix) {
                        let d = self.ctx.assertions.len() - _aa2;
                        if d > 0 {
                            eprintln!(
                                "[auflia_fix] outer={} round={} store_disj_index added {} axioms, terms={}",
                                _outer,
                                _round,
                                d,
                                self.ctx.terms.len(),
                            );
                            for i in _aa2.._aa2 + d.min(4) {
                                let t = self.ctx.assertions[i];
                                eprintln!(
                                    "[auflia_fix]   sd axiom #{}: data={:?}",
                                    t.0,
                                    self.ctx.terms.get(t)
                                );
                            }
                        }
                    }
                    if let Some(cap) = assertion_growth_cap {
                        if self.ctx.assertions.len() > cap {
                            break;
                        }
                    }
                    self.add_shadowed_store_equality_axioms();
                    if let Some(cap) = assertion_growth_cap {
                        if self.ctx.assertions.len() > cap {
                            break;
                        }
                    }
                    // #8596: Array congruence axioms bridge `a = store(...)` with
                    // `select(a, k)` to create `select(store(...), k)`. Without
                    // this, the ROW axiom generator never sees select-through-store
                    // patterns when the select is on a variable `a` that equals a
                    // store expression. This is critical for const-array + store
                    // formulas where model equality index atoms (x = y) must be
                    // generated eagerly for the SAT solver to find the satisfying
                    // assignment. Previously only the pure ArrayEUF path called
                    // add_array_congruence_axioms; the AUFLIA fixpoint path
                    // (run_array_axiom_fixpoint_at_plan) skipped it, causing false
                    // UNSAT on QF_AUFLIA benchmarks like const-array model equality.
                    let _aa3 = self.ctx.assertions.len();
                    self.add_array_congruence_axioms();
                    total_ac_axioms += self.ctx.assertions.len() - _aa3;
                    if ay_core::debug_channel_active(ay_core::DebugChannel::AufliaFix) {
                        let d = self.ctx.assertions.len() - _aa3;
                        if d > 0 {
                            eprintln!(
                                "[auflia_fix] outer={} round={} array_congruence added {} axioms, terms={}",
                                _outer,
                                _round,
                                d,
                                self.ctx.terms.len(),
                            );
                        }
                    }
                    if let Some(cap) = assertion_growth_cap {
                        if self.ctx.assertions.len() > cap {
                            break;
                        }
                    }
                    let _before_seed = self.ctx.terms.len();
                    let _seeded_row_terms = self.seed_array_row_terms();
                    total_seeded_row_terms += self.ctx.terms.len() - _before_seed;
                    if ay_core::debug_channel_active(ay_core::DebugChannel::AufliaFix) {
                        let d = self.ctx.terms.len() - _before_seed;
                        if d > 0 {
                            eprintln!(
                                "[auflia_fix] outer={} round={} seed_row_terms added {} terms (total={})",
                                _outer,
                                _round,
                                d,
                                self.ctx.terms.len(),
                            );
                        }
                    }
                    // (#6282 Phase A) Keep ROW2b budget at 1000.
                    // Reducing below 1000 causes regressions on SAT
                    // instances (test_store_permutation_distinct_indices_sat_5086).
                    //
                    // #6546: When the gate flipped `eager_row2b` on (and the
                    // outer plan did not ask for it), clamp to a much smaller
                    // budget — storeinv_nf only needs to unroll one upward
                    // select per store level, so 64 is generous for 7-level
                    // chains while capping worst-case regression on unrelated
                    // benchmarks that happen to trip the gate.
                    let row2b_cap = if plan.eager_row2b {
                        1000
                    } else {
                        row2b_gate_budget
                    };
                    if row2b_used < row2b_cap {
                        let remaining = row2b_cap - row2b_used;
                        let _seeded_row2b_terms = self.seed_array_row2b_terms(remaining);
                        total_seeded_row2b_terms += _seeded_row2b_terms;
                        if eager_row2b {
                            row2b_used += self.add_array_row2b_clauses(remaining);
                        }
                    }
                    if eager_row {
                        // ROW1 clauses (i = k → select(store(a,i,v),k) = v) are always
                        // generated eagerly on mixed-theory paths, but the pure
                        // ArrayEUF route can defer them to the runtime ArraySolver.
                        // ROW2b (upward) is only eager in EagerAll mode.
                        // #7890: Pass the remaining assertion-budget cap so a single
                        // call to add_array_row_clauses cannot by itself blow past
                        // the growth cap. Benchmarks like cs_fib-2 have ~200 select
                        // terms × ~50 stores → 10k+ ROW clauses from a single call,
                        // which would otherwise slip through the inner-loop cap
                        // (checked only after the call returns).
                        let row_cap = assertion_growth_cap.unwrap_or(usize::MAX);
                        let _aa4 = self.ctx.assertions.len();
                        self.add_array_row_clauses_with_cap(row_cap);
                        total_row_axioms += self.ctx.assertions.len() - _aa4;
                        if ay_core::debug_channel_active(ay_core::DebugChannel::AufliaFix) {
                            let d = self.ctx.assertions.len() - _aa4;
                            if d > 0 {
                                eprintln!(
                                    "[auflia_fix] outer={_outer} round={_round} row_clauses added {d} axioms",
                                );
                                for i in _aa4.._aa4 + d.min(6) {
                                    let t = self.ctx.assertions[i];
                                    eprintln!(
                                        "[auflia_fix]   row axiom #{}: data={:?}",
                                        t.0,
                                        self.ctx.terms.get(t)
                                    );
                                }
                            }
                        }
                        if let Some(cap) = assertion_growth_cap {
                            if self.ctx.assertions.len() > cap {
                                break;
                            }
                        }
                    }
                    if self.ctx.terms.len() == inner_n {
                        break;
                    }
                    // #6820: Bail out of the inner fixpoint if we've exceeded
                    // the term budget. The remaining axioms will be generated
                    // lazily by the DPLL(T) ArraySolver.
                    if self.ctx.terms.len() - fixpoint_start_terms > fixpoint_term_budget {
                        break;
                    }
                }
                // Dedup only axioms added after dedup_protect (#6340).
                // Seed `seen` with the protected prefix so new duplicates of
                // existing assertions are still removed, but the prefix itself
                // is never touched — callers rely on stable indices 0..dedup_protect.
                let mut seen: HashSet<TermId> = self.ctx.assertions[..dedup_protect]
                    .iter()
                    .copied()
                    .collect();
                let mut tail = self.ctx.assertions.split_off(dedup_protect);
                tail.retain(|a| seen.insert(*a));
                self.ctx.assertions.extend(tail);
            }
            let _assertions_before_sbd = self.ctx.assertions.len();
            // Store-store base decomposition is needed for storeinv-style proof
            // chains with an asserted store-store equality. On storecomm-style
            // SAT witnesses, the only store-store equality atoms are generated
            // bridges from eager congruence/ROW expansion; decomposing those
            // speculative atoms fabricates extensionality witnesses that can
            // close a false UNSAT before runtime theory checks run (#8785).
            if has_storeinv_witness {
                self.add_store_store_base_decomposition_axioms();
            }
            total_sbd_axioms += self.ctx.assertions.len() - _assertions_before_sbd;
            if ay_core::debug_channel_active(ay_core::DebugChannel::AufliaFix) {
                let added = self.ctx.assertions.len() - _assertions_before_sbd;
                eprintln!(
                    "[auflia_fix] outer={_outer} store_store_base_decomp added {added} axioms",
                );
                for i in _assertions_before_sbd..self.ctx.assertions.len() {
                    let t = self.ctx.assertions[i];
                    if i < _assertions_before_sbd + 10 {
                        eprintln!(
                            "[auflia_fix]   sbd axiom #{}: data={:?}",
                            t.0,
                            self.ctx.terms.get(t)
                        );
                    }
                }
            }
            if self.ctx.terms.len() == n {
                break;
            }
            // #6820: Also bail outer loop on term budget.
            if self.ctx.terms.len() - fixpoint_start_terms > fixpoint_term_budget {
                break;
            }
            // #6820, #7890: Bail on assertion (clause) budget after dedup.
            // For LazyRow2FinalCheck, excessive clauses slow SAT solving;
            // the runtime ArraySolver handles remaining axioms lazily.
            // #7890: Use growth-from-base cap so the budget reflects the
            // number of axioms ADDED by this fixpoint, not the absolute
            // assertion count (which may already include many preprocessed
            // assertions on QF_ALIA benchmarks). This keeps the budget
            // meaningful regardless of how many assertions exist at entry.
            if let Some(cap) = assertion_growth_cap {
                if self.ctx.assertions.len() > cap {
                    break;
                }
            }
        }

        // #8785: Final axiom tally. Helpful for diagnosing which axiom family
        // drives assertion growth on storecomm_invalid / AUFLIA false-UNSAT.
        // #8834: Prefer the `--debug auflia-fix-summary` CLI flag. The env
        // var `AY_DEBUG_AUFLIA_FIX_SUMMARY` still works via the cached env-var
        // fallback in `debug_channel_active`, which emits a one-shot
        // deprecation warning when invoked through the ay CLI entrypoint.
        if ay_core::debug_channel_active(ay_core::DebugChannel::AufliaFixSummary) {
            eprintln!(
                "[auflia_fix_summary] ext={} sv={} os={} sd={} ac={} row={} sbd={} seeded_row_terms={} seeded_row2b_terms={} final_terms={} final_assertions={}",
                total_ext_axioms,
                total_sv_axioms,
                total_os_axioms,
                total_sd_axioms,
                total_ac_axioms,
                total_row_axioms,
                total_sbd_axioms,
                total_seeded_row_terms,
                total_seeded_row2b_terms,
                self.ctx.terms.len(),
                self.ctx.assertions.len(),
            );
        }

        self.row_seeded_terms.clear();
        self.array_axiom_scope = None;
    }

    /// Run the full eager array axiom fixpoint at a given dedup_protect offset.
    pub(in crate::executor) fn run_array_axiom_full_fixpoint_at(&mut self, dedup_protect: usize) {
        self.run_array_axiom_fixpoint_at(dedup_protect, ArrayAxiomMode::EagerAll);
    }

    /// Run the full eager array axiom fixpoint with extra root terms for
    /// assumption-aware scope filtering (#6736).
    ///
    /// In incremental mode, assumption terms are not in `self.ctx.assertions`
    /// and would be excluded from the reachable set that scopes axiom
    /// generation. This variant includes `assumption_roots` in the reachable
    /// set so array operations appearing only in assumptions get proper axioms.
    pub(in crate::executor) fn run_array_axiom_full_fixpoint_at_with_roots(
        &mut self,
        dedup_protect: usize,
        assumption_roots: &[TermId],
    ) {
        self.run_array_axiom_fixpoint_at_plan(
            dedup_protect,
            ArrayAxiomPlan::from_mode(ArrayAxiomMode::EagerAll),
            assumption_roots,
        );
    }

    /// Run the full eager array axiom fixpoint, deduplicating all assertions.
    pub(in crate::executor) fn run_array_axiom_full_fixpoint(&mut self) {
        self.run_array_axiom_fixpoint_at(0, ArrayAxiomMode::EagerAll);
    }

    /// Run the Array+EUF fixpoint (store congruence + array congruence + ROW).
    ///
    /// Includes `add_array_congruence_axioms` which creates `select(B,k)` from
    /// `select(A,k)` when `A = B`. Used by the pure array and BV paths, which do
    /// not need the store-store base decomposition used by the combined solvers.
    pub(in crate::executor) fn run_array_axiom_fixpoint_5(&mut self) {
        self.run_array_axiom_fixpoint_inner(true, &[]);
    }

    /// Run the Array+EUF fixpoint with extra root terms for assumption-aware
    /// scope filtering (#6736). Used by QF_AX check-sat-assuming paths where
    /// assumption terms contain array operations that need congruence axioms
    /// but are not in `self.ctx.assertions`.
    pub(in crate::executor) fn run_array_axiom_fixpoint_5_with_roots(
        &mut self,
        assumption_roots: &[TermId],
    ) {
        self.run_array_axiom_fixpoint_inner(true, assumption_roots);
    }

    fn run_array_axiom_fixpoint_inner(
        &mut self,
        include_congruence: bool,
        assumption_roots: &[TermId],
    ) {
        // Scope filtering for incremental mode (#6726).
        if self.incremental_mode {
            let start_len = self.ctx.terms.len();
            let reachable = if assumption_roots.is_empty() {
                reachable_term_set(&self.ctx.terms, &self.ctx.assertions)
            } else {
                let mut roots =
                    Vec::with_capacity(self.ctx.assertions.len() + assumption_roots.len());
                roots.extend_from_slice(&self.ctx.assertions);
                roots.extend_from_slice(assumption_roots);
                reachable_term_set(&self.ctx.terms, &roots)
            };
            self.array_axiom_scope = Some((reachable, start_len));
        }

        self.reset_array_congruence_caches();

        // Unified fixpoint: all axiom generators including ROW2b run together.
        // ROW2b (upward select propagation) creates new select terms that feed
        // into congruence and ROW1/ROW2 generators in subsequent rounds.
        // Deep store chains (storeinv with 7-level nesting, #6282) require
        // multiple rounds to chain through all levels.
        //
        // Budget limits ROW2b axiom count per fixpoint invocation to prevent
        // O(selects × stores) blowup on large formulas.
        let fixpoint_start_terms = self.ctx.terms.len();
        // #8140: Term budget prevents runaway expansion on benchmarks with
        // deep store chains and symbolic indices (bubble_sort, wchains).
        // When the fixpoint bails on this budget, the expand_select_store
        // pass and ROW axioms in generate_array_bv_axioms provide
        // sufficient array reasoning for the BV eager pipeline. For
        // QF_AX/QF_AUFLIA paths that use this fixpoint, the DPLL(T)
        // ArraySolver handles remaining axioms lazily.
        // Best-by-default term budget; no env override (former unset default).
        let fixpoint_term_budget: usize = 10_000 * self.qfax_budget_multiplier;
        let row2b_budget = 0_usize;
        let mut row2b_used = 0_usize;

        // #8635: Check interrupt/deadline between fixpoint iterations.
        let should_stop = self.make_should_stop();

        for _round in 0..20_usize {
            if should_stop() {
                break;
            }
            let n = self.ctx.terms.len();
            // Keep array-default propagation in the lightweight QF_AX/BV
            // driver too.  In particular, equality aliases must expose a
            // relevant `default(store(..))` before the carrier-sensitive store
            // axioms can fire.
            self.add_array_default_congruence_axioms();
            self.add_array_default_store_axioms();
            self.add_store_value_congruence_axioms();
            self.add_store_other_side_congruence_axioms();
            self.add_store_disjunctive_index_axioms();
            self.add_shadowed_store_equality_axioms();
            if include_congruence {
                self.add_array_congruence_axioms();
            }
            self.add_array_row_lemmas();
            // ROW2b upward propagation (#6282): for select(A, j) where A is
            // the base of store(A, i, v) = B, create select(B, j) and assert
            // (= i j) ∨ (= select(A,j) select(B,j)).
            if row2b_used < row2b_budget {
                let remaining = row2b_budget - row2b_used;
                row2b_used += self.add_array_row2b_upward_lemmas(remaining);
            }
            if self.ctx.terms.len() == n {
                break;
            }
            // #8140: Bail if the fixpoint generated too many terms.
            if self.ctx.terms.len() - fixpoint_start_terms > fixpoint_term_budget {
                break;
            }
        }
        // Deduplicate assertions.
        #[cfg(not(kani))]
        let mut seen: HashSet<TermId> =
            ay_core::kani_compat::det_hash_set_with_capacity(self.ctx.assertions.len());
        #[cfg(kani)]
        let mut seen: HashSet<TermId> = HashSet::default();
        self.ctx.assertions.retain(|a| seen.insert(*a));

        self.array_axiom_scope = None;
    }
}

#[cfg(test)]
mod array_default_alias_tests {
    use super::contains_symbolic_array_default;
    use ay_core::{Sort, TermStore};

    #[test]
    fn detects_direct_and_nested_symbolic_bool_defaults() {
        let mut terms = TermStore::new();
        let array = terms.mk_var("a", Sort::array(Sort::Int, Sort::Bool));
        let default = terms.mk_array_default(array);
        let negated = terms.mk_not(default);
        let plain = terms.mk_var("p", Sort::Bool);

        assert!(contains_symbolic_array_default(&terms, default));
        assert!(contains_symbolic_array_default(&terms, negated));
        assert!(!contains_symbolic_array_default(&terms, plain));
    }
}
