// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Datatype (DT) theory solving and DT+X combined routes.

use super::super::super::Executor;
use crate::executor_types::{Result, SolveResult};
use crate::preprocess::PreprocessingPass;
// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TheoryLemmaKind, TheoryLit, TheorySolver};
use ay_dt::DtSolver;

mod lazy_proof_state;

/// Budget for post-`Sat` model-e-graph recheck lemma rounds per
/// `solve_with_dt_axioms` call (fail-closed Unknown past it; #dt-model-recheck).
const DT_MODEL_RECHECK_MAX_ROUNDS: u32 = 32;

/// Outcome of [`Executor::dt_model_egraph_recheck`].
enum DtModelRecheck {
    /// No datatype clash/cycle among the accepted model's TRUE datatype
    /// equalities: the model respects the D0 rules.
    Clean,
    /// A verified datatype conflict was found; its tautology clause(s) were
    /// appended to the assertions. The caller must RE-SOLVE (the previous
    /// `Sat` must not be returned).
    LemmasInjected,
    /// A datatype conflict exists but no new clause can be emitted (already
    /// emitted this solve, or its explanation failed independent fresh-EUF
    /// re-derivation). The model must not be accepted; the caller returns a
    /// sound `Unknown` (fail-closed).
    Inconclusive,
}

/// Replace a speculative AUFLIA term universe with the exact owned entry
/// universe. Taking the snapshot by value is load-bearing: `TermStore::clone`
/// mints a new rollback identity, so cloning here would break every checkpoint
/// bound to the saved store and briefly allocate a third full term universe.
fn restore_dt_auflia_entry_terms(current: &mut ay_core::TermStore, entry: ay_core::TermStore) {
    *current = entry;
}

/// Executor-owned state that a discarded lazy-DT sub-solve may mutate.
///
/// The public query does not restart between the lazy attempt and its eager
/// fallback. Restoring only assertions/terms is therefore insufficient: a
/// validation bypass, refinement lemma, model-repair latch, or TermId-keyed
/// memo from the failed attempt can change what the eager authority accepts.
/// Keep the transaction boundary explicit and shared by both lazy lanes.
struct DtLazyAttemptState {
    last_assumptions: Option<Vec<TermId>>,
    last_assumption_core: Option<Vec<TermId>>,
    last_core_term_to_name: Option<HashMap<TermId, String>>,
    nra_algebraic_model: HashMap<TermId, ay_nra::RealAlgebraicValue>,
    model_validation_delegated_assertions: HashSet<TermId>,
    dt_solver_added_axiom_terms: HashSet<TermId>,
    row_seeded_terms: HashSet<TermId>,
    recorded_var_substitutions: HashMap<TermId, TermId>,
    array_default_epsilon_by_sort: HashMap<Sort, TermId>,
    array_default_diag_by_sort: HashMap<Sort, String>,
    qfax_refinement_clause: Option<Vec<(TermId, bool)>>,
    last_rejected_array_assertion: Option<TermId>,
    cegar_pending_lemma: Option<TermId>,
    cegar_rounds_remaining: u32,
    cegar_emitted_lemmas: HashSet<TermId>,
    array_ext_shadow: crate::executor::ArrayExtShadow,
    array_ext_witness_cache: crate::executor::ArrayExtWitnessCache,
    array_axiom_scope: Option<(HashSet<TermId>, usize)>,
    dt_lazy_splits: Option<(Vec<(String, Vec<String>, bool)>, Vec<(TermId, Vec<TermId>)>)>,
    active_support_axioms: Vec<TheoryLit>,
    conflict_semantic_verify_memo: crate::verification::ConflictSemanticVerifyMemo,
    prop_semantic_verify_memo: crate::verification::PropSemanticVerifyMemo,
    named_assert_rewrites: HashMap<TermId, TermId>,
    // `lemma_cache` is intentionally absent. Both lazy lanes call
    // `dt_lazy_lemma_cache_isolation_available` before capture, excluding
    // persistence and any pre-existing entries; the attempted solve therefore
    // cannot retain speculative TermIds there. This avoids cloning a bounded
    // but potentially large lemma/dedup ledger.
    uflia_repair_candidates: Vec<crate::executor::model::Model>,
    uflia_repair_conflict_tables: Vec<String>,
    last_degrade_was_datatype_array: bool,
    nested_array_row_reduction_unsat: bool,
    uflia_congruence_lane: bool,
    uflia_congruence_gate_rejected: bool,
    qfax_retry_done: bool,
    uflia_congruence_retry_done: bool,
    uflia_model_repair_done: bool,
    sat_validated_by_mod_div_or_branch: bool,
    defer_model_validation: bool,
    skip_model_eval: bool,
    read_pin_repair_done: bool,
    dt_array_injectivity_gate_bypass: bool,
    original_problem_had_quantifiers: bool,
    in_nested_array_residue_probe: bool,
    residue_probe_failures: u32,
    mod_div_or_branch_rescue_depth: u8,
}

impl DtLazyAttemptState {
    fn capture(executor: &Executor) -> Self {
        Self {
            last_assumptions: executor.last_assumptions.clone(),
            last_assumption_core: executor.last_assumption_core.clone(),
            last_core_term_to_name: executor.last_core_term_to_name.clone(),
            nra_algebraic_model: executor.nra_algebraic_model.values().clone(),
            model_validation_delegated_assertions: executor
                .model_validation_delegated_assertions
                .clone(),
            dt_solver_added_axiom_terms: executor.dt_solver_added_axiom_terms.clone(),
            row_seeded_terms: executor.row_seeded_terms.clone(),
            recorded_var_substitutions: executor.recorded_var_substitutions.clone(),
            array_default_epsilon_by_sort: executor.array_default_epsilon_by_sort.clone(),
            array_default_diag_by_sort: executor.array_default_diag_by_sort.clone(),
            qfax_refinement_clause: executor.qfax_refinement_clause.clone(),
            last_rejected_array_assertion: executor.last_rejected_array_assertion,
            cegar_pending_lemma: executor.cegar_pending_lemma,
            cegar_rounds_remaining: executor.cegar_rounds_remaining,
            cegar_emitted_lemmas: executor.cegar_emitted_lemmas.clone(),
            array_ext_shadow: executor.array_ext_shadow.clone(),
            array_ext_witness_cache: executor.array_ext_witness_cache.clone(),
            array_axiom_scope: executor.array_axiom_scope.clone(),
            dt_lazy_splits: executor.dt_lazy_splits.clone(),
            active_support_axioms: executor.active_support_axioms.clone(),
            conflict_semantic_verify_memo: executor.conflict_semantic_verify_memo.clone(),
            prop_semantic_verify_memo: executor.prop_semantic_verify_memo.clone(),
            named_assert_rewrites: executor.named_assert_rewrites.clone(),
            uflia_repair_candidates: executor.uflia_repair_candidates.clone(),
            uflia_repair_conflict_tables: executor.uflia_repair_conflict_tables.clone(),
            last_degrade_was_datatype_array: executor.last_degrade_was_datatype_array,
            nested_array_row_reduction_unsat: executor.nested_array_row_reduction_unsat,
            uflia_congruence_lane: executor.uflia_congruence_lane,
            uflia_congruence_gate_rejected: executor.uflia_congruence_gate_rejected,
            qfax_retry_done: executor.qfax_retry_done,
            uflia_congruence_retry_done: executor.uflia_congruence_retry_done,
            uflia_model_repair_done: executor.uflia_model_repair_done,
            sat_validated_by_mod_div_or_branch: executor.sat_validated_by_mod_div_or_branch,
            defer_model_validation: executor.defer_model_validation,
            skip_model_eval: executor.skip_model_eval,
            read_pin_repair_done: executor.read_pin_repair_done,
            dt_array_injectivity_gate_bypass: executor.dt_array_injectivity_gate_bypass,
            original_problem_had_quantifiers: executor.original_problem_had_quantifiers,
            in_nested_array_residue_probe: executor.in_nested_array_residue_probe,
            residue_probe_failures: executor.residue_probe_failures,
            mod_div_or_branch_rescue_depth: executor.mod_div_or_branch_rescue_depth,
        }
    }

    /// Move the entry state back without allocating after arbitrary inner growth.
    /// The proof-coupled witness cache is returned for the caller to commit only
    /// after the proof/term rollback succeeds.
    fn restore(self, executor: &mut Executor) -> crate::executor::ArrayExtWitnessCache {
        executor.last_assumptions = self.last_assumptions;
        executor.last_assumption_core = self.last_assumption_core;
        executor.last_core_term_to_name = self.last_core_term_to_name;
        executor.restore_nra_values(self.nra_algebraic_model);
        executor.model_validation_delegated_assertions = self.model_validation_delegated_assertions;
        executor.dt_solver_added_axiom_terms = self.dt_solver_added_axiom_terms;
        executor.row_seeded_terms = self.row_seeded_terms;
        executor.recorded_var_substitutions = self.recorded_var_substitutions;
        executor.array_default_epsilon_by_sort = self.array_default_epsilon_by_sort;
        executor.array_default_diag_by_sort = self.array_default_diag_by_sort;
        executor.qfax_refinement_clause = self.qfax_refinement_clause;
        executor.last_rejected_array_assertion = self.last_rejected_array_assertion;
        executor.cegar_pending_lemma = self.cegar_pending_lemma;
        executor.cegar_rounds_remaining = self.cegar_rounds_remaining;
        executor.cegar_emitted_lemmas = self.cegar_emitted_lemmas;
        executor.array_ext_shadow = self.array_ext_shadow;
        executor.array_axiom_scope = self.array_axiom_scope;
        executor.dt_lazy_splits = self.dt_lazy_splits;
        executor.active_support_axioms = self.active_support_axioms;
        executor.conflict_semantic_verify_memo = self.conflict_semantic_verify_memo;
        executor.prop_semantic_verify_memo = self.prop_semantic_verify_memo;
        executor.named_assert_rewrites = self.named_assert_rewrites;
        executor.uflia_repair_candidates = self.uflia_repair_candidates;
        executor.uflia_repair_conflict_tables = self.uflia_repair_conflict_tables;
        executor.last_degrade_was_datatype_array = self.last_degrade_was_datatype_array;
        executor.nested_array_row_reduction_unsat = self.nested_array_row_reduction_unsat;
        executor.uflia_congruence_lane = self.uflia_congruence_lane;
        executor.uflia_congruence_gate_rejected = self.uflia_congruence_gate_rejected;
        executor.qfax_retry_done = self.qfax_retry_done;
        executor.uflia_congruence_retry_done = self.uflia_congruence_retry_done;
        executor.uflia_model_repair_done = self.uflia_model_repair_done;
        executor.sat_validated_by_mod_div_or_branch = self.sat_validated_by_mod_div_or_branch;
        executor.defer_model_validation = self.defer_model_validation;
        executor.skip_model_eval = self.skip_model_eval;
        executor.read_pin_repair_done = self.read_pin_repair_done;
        executor.dt_array_injectivity_gate_bypass = self.dt_array_injectivity_gate_bypass;
        executor.original_problem_had_quantifiers = self.original_problem_had_quantifiers;
        executor.in_nested_array_residue_probe = self.in_nested_array_residue_probe;
        executor.residue_probe_failures = self.residue_probe_failures;
        executor.mod_div_or_branch_rescue_depth = self.mod_div_or_branch_rescue_depth;
        self.array_ext_witness_cache
    }
}

impl Executor {
    fn dt_lazy_lemma_cache_isolation_available(&self) -> bool {
        !self.lemma_persistence && self.lemma_cache.is_empty()
    }

    /// Record injected DT axioms as proof-tracker theory lemmas, upgrading
    /// `Generic` to a strict-checkable typed kind exactly when the checker's
    /// OWN recognizer accepts the recorded clause (#trust-count→0, C1.iv).
    ///
    /// Each probe calls an `ay_proof` recognizer that IS the strict validator
    /// (`validate_*(..).is_ok()`; checker/datatype_axiom.rs), fed the SAME
    /// registries the mint-time strict check receives
    /// (`datatype_decls_for_strict_proof` /
    /// `ctor_selector_decls_for_strict_proof`), so a lemma is tagged only when
    /// strict mode will independently re-validate that exact clause —
    /// classifier and checker cannot drift (the `promote_datatype_distinct_lemmas`
    /// / `push_array_axiom_assertion_site` precedent). The enabled probes stay
    /// limited to the established C1.iv/C5 families. Everything outside those
    /// lanes — including array∘DT bridge implications, guard-resolved and direct
    /// acyclicity clauses, forced guard-unit literals, depth axioms, value-eq
    /// congruence biconditionals, same-constructor structural disequalities,
    /// and the (F1)/(F2) BARE injectivity field-equality units — is recorded
    /// `Generic` so publication fails closed.
    ///
    /// The recorded lemma is the unit clause `[axiom]` where the axiom may be
    /// an `or`/`=>` term; the DT validators or-flatten internally
    /// (`flatten_clause_literals`), so probing the exact recorded clause
    /// performs the same flattened comparison the euf.rs precedent makes
    /// explicitly — and guarantees the probe sees precisely what the checker
    /// will later validate.
    fn record_dt_axiom_theory_lemmas(&mut self, axioms: &[TermId]) {
        let dt_decls = self.datatype_decls_for_strict_proof();
        let ctor_selectors = self.ctor_selector_decls_for_strict_proof();
        for &axiom in axioms {
            let clause = [axiom];
            // Family (A) selector projection `sel_i(C(a..)) = a_i`.
            if ay_proof::recognize_datatype_selector_project(
                &self.ctx.terms,
                &clause,
                &ctor_selectors,
            ) {
                let _ = self.proof_tracker.add_theory_lemma_with_kind(
                    vec![axiom],
                    TheoryLemmaKind::DatatypeSelectorProject,
                );
            // Family (D) constructor coverage `(or (is-C1 x) .. (is-Ck x))`
            // over a non-constructor scrutinee (unit `(is-C x)` for a
            // single-constructor datatype). Probed BEFORE the tester lane:
            // the tester validator's general exhaustiveness lane accepts the
            // k>=2 disjunctions too, so this probe only moves clauses between
            // two strict-checkable kinds — to the one that names the family —
            // and never widens what escapes `Generic` by mislabeling (C5).
            } else if ay_proof::recognize_datatype_exhaustive(&self.ctx.terms, &clause, &dt_decls) {
                let _ = self
                    .proof_tracker
                    .add_theory_lemma_with_kind(vec![axiom], TheoryLemmaKind::DatatypeExhaustive);
            // Family (C) guarded constructor reconstruction
            // `(or (not (is-C x)) (= x (C (sel_1 x) .. (sel_k x))))` (the
            // emitted `mk_implies` desugars to this disjunction). Selector
            // list + field order are re-derived from the registries by the
            // recognizer=validator, so a permuted or truncated chain stays
            // `Generic` (C5).
            } else if ay_proof::recognize_datatype_constructor_reconstruct(
                &self.ctx.terms,
                &clause,
                &dt_decls,
                &ctor_selectors,
            ) {
                let _ = self.proof_tracker.add_theory_lemma_with_kind(
                    vec![axiom],
                    TheoryLemmaKind::DatatypeConstructorReconstruct,
                );
            // Families (B)/(B') tester evaluation `is-C(C(..))` /
            // `(not (is-C' (C ..)))` (the `= true/false` forms fold to these at
            // `mk_eq`), plus whatever else the tester validator itself accepts
            // (nullary-sibling exhaustiveness form). The `_with_selectors`
            // variant matches the checker dispatch exactly:
            // `check_proof_strict_with_datatypes` always supplies both
            // registries (checker/mod.rs `DatatypeTesterEval` arm).
            } else if ay_proof::recognize_datatype_tester_eval_with_selectors(
                &self.ctx.terms,
                &clause,
                &dt_decls,
                &ctor_selectors,
            ) {
                let _ = self
                    .proof_tracker
                    .add_theory_lemma_with_kind(vec![axiom], TheoryLemmaKind::DatatypeTesterEval);
            } else {
                let _ = self.proof_tracker.add_explicit_trust_lemma(vec![axiom]);
            }
        }
    }

    /// Solve using DT (datatypes) theory for QF_DT logic.
    ///
    /// Implements DPLL(T) with datatype theory solver. The solver handles:
    /// - Constructor clash detection: C1(a) = C2(b) where C1 != C2 → CONFLICT
    /// - Injectivity: C(a1,...,an) = C(b1,...,bn) → a1=b1 ∧ ... ∧ an=bn
    /// - Selector semantics: sel_i(C(a_1,...,a_n)) = a_i
    ///
    /// Proof tracking is handled natively by `solve_incremental_theory_pipeline!`
    /// (#6705).
    pub(in crate::executor) fn solve_dt(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // Lift non-Bool ITEs out of predicates/applications (#5082).
        let lifted: Vec<TermId> = self.ctx.terms.lift_arithmetic_ite_all(&self.ctx.assertions);
        self.ctx.assertions = lifted;

        // Acyclicity fast-path (#1776, #dt-sel-projection). The pure-DT DPLL(T)
        // loop reasons over the generated selector/tester axioms and does not feed
        // raw constructor equalities to the interactive DtSolver, so its occurs-
        // check (and the new downward selector-projection) never see them. Run the
        // dedicated occurs-check over the top-level equalities/testers here: it
        // builds a fresh DtSolver with the full constructor DAG + selector
        // signatures and only ever returns UNSAT for a genuine well-foundedness
        // cycle (e.g. `x = cons(cons(tl x))`). Sound: UNSAT-only, every edge is
        // implied by an asserted fact.
        let occurs_check_assertions = self.ctx.assertions.clone();
        if self.dt_occurs_check_unsat_from_equalities(&occurs_check_assertions, &[]) {
            self.last_unknown_reason = None;
            return Ok(SolveResult::unsat());
        }

        // Lazy, demand-driven case-splitting via iterative deepening (the DT
        // final-check / completeness backstop).
        //
        // The eager DT axiom pass (`dt_selector_axioms_to_depth`) unrolls recursive
        // selector structure only to a bounded depth. The warm-start depth settles
        // the common shallow cases in a single pipeline run. When that bounded unroll
        // returns Unknown, the obligation's (UN)SAT proof needs a constructor
        // case-split deeper than the current bound, so we re-solve at a strictly
        // larger depth — materializing the next frontier of `sel_i(...)` subterms and
        // their (C)/(D) axioms — until we get a definitive answer, the recursive
        // structure is fully unrolled (no deeper DT subterm appears, so a fixpoint is
        // reached and the answer is genuine), or the deepening ceiling is hit
        // (fail-closed Unknown).
        //
        // Soundness: each deepening round only ADDS datatype-theory tautologies
        // (exhaustiveness + selector/constructor axioms), which can only shrink the
        // model space — never create a false-UNSAT. A SAT or UNSAT verdict at any
        // depth is therefore trustworthy and returned immediately.
        // Termination: every real model has finitely many selector applications; the
        // term store growth between consecutive depths is monotone and detected, and
        // the ceiling bounds the genuinely-infinite recursive shapes.
        let mut depth = crate::executor::dt_axioms::DT_WARM_START_DEPTH;
        let ceiling = crate::executor::dt_axioms::DT_MAX_DEEPENING_DEPTH;
        let mut prev_term_len: Option<usize> = None;
        loop {
            if self.should_abort_theory_loop() {
                return Ok(SolveResult::Unknown);
            }
            let pre_axiom_term_len = self.ctx.terms.len();
            let result = self.solve_dt_at_depth(depth)?;

            // A definitive verdict is sound at every depth (deeper unrolls only add
            // entailed tautologies). Return it immediately.
            if !matches!(result, SolveResult::Unknown) {
                return Ok(result);
            }

            // Unknown: decide whether deepening can possibly help. If the eager pass
            // at this depth did not grow the term store relative to the previous
            // depth, the recursive structure is fully unrolled (acyclic / depth-
            // bounded) and a deeper unroll would add nothing — the Unknown is from
            // some other source and deepening is futile.
            let post_axiom_term_len = self.ctx.terms.len();
            let grew = post_axiom_term_len > pre_axiom_term_len;
            let advanced_vs_prev = prev_term_len.is_none_or(|p| post_axiom_term_len > p);
            prev_term_len = Some(post_axiom_term_len);

            if !grew || !advanced_vs_prev || depth >= ceiling {
                // Fail-closed: no deeper structure to expand, or budget exhausted.
                return Ok(SolveResult::Unknown);
            }
            depth = depth.saturating_add(1);
        }
    }

    /// Run one DT solve at a fixed eager-unroll `max_recursive_depth`.
    ///
    /// Extracted from `solve_dt` so the iterative-deepening final-check can
    /// re-solve at increasing depths. Generates the DT selector/tester/
    /// constructor axioms unrolled to `max_recursive_depth`, runs the DPLL(T)
    /// pipeline, then restores the assertion list. The added axioms are all
    /// datatype-theory tautologies, so the verdict is sound at every depth.
    fn solve_dt_at_depth(&mut self, max_recursive_depth: usize) -> Result<SolveResult> {
        // Register DT selector axioms as theory lemmas for proof tracking
        let base_assertions: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut extra_axioms =
            self.dt_selector_axioms_to_depth(&base_assertions, max_recursive_depth);
        // Value-equality congruence for bare datatype-valued `(= x y)` operands
        // where neither side is a constructor application
        // (#dt-value-eq-congruence; see solve_with_dt_axioms_at_depth). The
        // emitted EXACT datatype-equality biconditional is a datatype tautology,
        // so the pure-DT path benefits identically and cannot false-unsat.
        extra_axioms.extend(self.dt_datatype_value_equality_congruence_axioms(&base_assertions));

        // Guarded datatype-acyclicity clauses mined from disjunctive contexts
        // (#dt-acyclic-case-split). A structural cycle hidden inside a case
        // split — e.g. `(not (distinct (nd y x) lf x))` ⇒ surviving disjunct
        // `x = nd(y, x)` — is invisible to both the occurs-check fast path and
        // the SAT-core EUF (which treats constructors as plain UF), causing
        // false-SAT. Each clause `(not (= a b))` is a valid datatype-theory
        // consequence (an inductive value is never a proper subterm of itself),
        // so it only constrains the search and can never cause a false-UNSAT.
        let assertions_snapshot = self.ctx.assertions.clone();
        extra_axioms.extend(self.dt_guarded_acyclicity_disjuncts(&assertions_snapshot, &[]));
        // Guard-FORCING units from cycles hidden behind a single free guard and
        // selector-on-constructor layers (#dt-acyclic-guard-forcing). Each
        // emitted literal `g`/`(not g)` is entailed (the other polarity would
        // assert a well-foundedness cycle), so it only prunes the search and
        // cannot cause a false-UNSAT.
        extra_axioms.extend(self.dt_guarded_acyclicity_guard_units(&assertions_snapshot, &[]));
        if self.produce_proofs_enabled() {
            self.record_dt_axiom_theory_lemmas(&extra_axioms);
        }

        // Pre-collect datatype registration data to avoid borrowing self.ctx
        // inside the macro (which already holds a mutable borrow on self).
        let dt_info: Vec<(String, Vec<String>)> = self
            .ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_owned(), ctors.to_vec()))
            .collect();

        // Add selector axioms to self.ctx.assertions temporarily;
        // the incremental pipeline reads assertions from there.
        let base_assertions_exact = self.ctx.assertions.clone();
        // Record the appended axiom terms so the in-loop validation's
        // #dt-embedded-cycle compound guard exempts them (each is an entailed
        // datatype tautology; see `dt_solver_added_axiom_terms`).
        self.dt_solver_added_axiom_terms
            .extend(extra_axioms.iter().copied());
        self.ctx.assertions.extend(extra_axioms);

        let result = solve_incremental_theory_pipeline!(self,
            tag: "DT",
            create_theory: {
                let mut t = DtSolver::new(&self.ctx.terms);
                for (dt_name, constructors) in &dt_info {
                    t.register_datatype(dt_name, constructors);
                    // Register each constructor's selector signature so the DT
                    // solver's downward selector-projection and tester-edge
                    // occurs-check can derive `sel_i(t') = a_i` from constructor
                    // equalities (#dt-sel-projection). Without this the projection
                    // pass is a no-op and nested-constructor cycles like
                    // `x = cons(cons(tl x))` are missed (false-SAT).
                    for ctor_name in constructors {
                        if let Some(info) = self.ctx.constructor_selector_info(ctor_name) {
                            let sel_names: Vec<String> =
                                info.iter().map(|(n, _)| n.clone()).collect();
                            t.register_ctor_selectors(ctor_name, &sel_names);
                        }
                    }
                }
                t
            },
            extract_models: |theory| TheoryModels {
                // Export the final e-graph (classes, constructor/tester
                // commitments, disequalities) so print-time datatype value
                // resolution reads the REAL model instead of re-deriving
                // per-term values that fabricate defaults for constrained
                // selector chains (#mv-dt-single-source, M3/M4 F1).
                dt: Some(theory.export_model()),
                ..TheoryModels::default()
            },
            track_theory_stats: false,
            set_unknown_on_error: false
        );

        // Restore assertions to original length (remove temporary axioms).
        self.ctx.assertions = base_assertions_exact;
        self.dt_solver_added_axiom_terms.clear();
        result
    }

    /// Shared DT delegation: occurs-check, selector/acyclicity axioms, delegate, truncate.
    ///
    /// All `solve_dt_*` methods follow the same pattern (#3536):
    /// 1. DT occurs-check fast path → early UNSAT (#1776)
    /// 2. Generate DT selector axioms from base assertions
    /// 3. Optionally generate acyclicity depth axioms (#1764)
    /// 4. Temporarily extend assertions with DT axioms
    /// 5. Delegate to underlying theory solver
    /// 6. Truncate assertions to restore original state (#1770)
    fn solve_with_dt_axioms(
        &mut self,
        acyclicity_sort: Option<Sort>,
        solve_fn: fn(&mut Self) -> Result<SolveResult>,
    ) -> Result<SolveResult> {
        // SOUNDNESS: capture the datatype-carrying-array-equality signature NOW,
        // from the ORIGINAL assertions. The BV core below scalarizes/expands
        // stores (`select_store_expansion`), which erases both the array sort and
        // the `(= store store)` structure — so by the time a SAT verdict comes
        // back this signature is gone and cannot be re-detected. See the degrade
        // gate after the solve loop.
        let dt_carrying_array_eq = self.problem_has_datatype_carrying_array();

        // Store-value constructor-injectivity bridge coverage
        // (#dt-array-store-value-injectivity). When every datatype-carrying-array
        // hazard is modeled by `dt_store_value_injectivity_axioms`, a returned SAT
        // model already satisfies the emitted injectivity/disjointness
        // implications (they are part of the solved formula), so the fail-closed
        // degrade gate below — and the sibling gate in
        // `finalize_sat_model_validation` — can be soundly bypassed. Computed from
        // the ORIGINAL (pre-flatten) assertions; default false (degrade) for every
        // non-bypassed route. See `dt_array_injectivity_fully_modeled`.
        // OR-preserve: check-sat entry may already have enabled the bypass via
        // the route-independent observational-completeness argument.
        self.dt_array_injectivity_gate_bypass = self.dt_array_injectivity_gate_bypass
            || (dt_carrying_array_eq && self.dt_array_injectivity_fully_modeled());

        // Flatten top-level conjunctions so DT axiom scan sees individual
        // equalities, not (and ...) wrappers. Without this, the reachability
        // filter in dt_selector_axioms misses DT constructors inside
        // conjunctions, causing false-SAT on DT+BV formulas (#7016).
        let mut flatten = crate::preprocess::FlattenAnd::new();
        flatten.apply(&mut self.ctx.terms, &mut self.ctx.assertions);

        // Lift non-Bool ITEs out of predicates/applications (#5082), exactly as
        // `solve_dt` does. Without this the combined DT+BV/DT+Array routes leave
        // `(sel (ite g A B))` as an unconstrained UF for the eager bit-blast
        // core: the selector-axiom scan matches none of ctor-app / asserted
        // var-ctor equality / selector chain, the SAT core invents a spurious
        // model, the strict ite_uf_definition oracle rejects it, and the
        // deepening loop fixpoints to unknown-incomplete (observed on the ay-pb
        // eval_lit whole-fn VC). Lifting rewrites it to
        // `ite(g, (sel A), (sel B))`, which the DT axiom pass covers.
        //
        // BUT the lift also Shannon-expands an UNCONDITIONAL constructor
        // equality `(= x (C .. (ite g A B) ..))` into `(ite g (= x C_A) (= x
        // C_B))`, which `collect_unconditional_equalities` (no `Ite` arm)
        // misses — losing the acyclicity guard-forcing unit (fuzz881). Snapshot
        // the assertions PRE-lift so the acyclicity passes can additionally mine
        // them; every unit they derive is entailed by the original assertions
        // and lifting is semantics-preserving, so it stays sound post-lift.
        self.dt_pre_lift_assertions = self.ctx.assertions.clone();
        let lifted: Vec<TermId> = self.ctx.terms.lift_arithmetic_ite_all(&self.ctx.assertions);
        self.ctx.assertions = lifted;

        // Cross-vocabulary UF congruence over datatype selector-bridge equalities
        // (#dt-uf-bridge-congruence). verification-consumer's recursive-ADT catamorphism VCs
        // (`inc_some_list`/rusthorn, `binary_search_list`) read a field in TWO
        // vocabularies — the declared datatype selector `enum_payload_get_1_1(x)`
        // and a shadow UF selector `list_cons_1(x)` — linked by a guarded bridge
        // equality, then apply a recursive logic function (`logic_sum`) to BOTH.
        // The refutation needs the congruence `list_cons_1(x)=enum_payload_get_1_1(x)
        // ⟹ logic_sum(list_cons_1(x))=logic_sum(enum_payload_get_1_1(x))` to reach
        // the LIA side, but the combined UF+LIA loop can return a UF-containing
        // expression split (#7884) from a candidate assignment BEFORE EUF closes
        // that congruence in the bridge-true branch, degrading a provable UNSAT to
        // `unknown` (z3 refutes it in <1s; ay diverges through the DT deepening).
        // This pass emits the congruence STATICALLY as a base assertion so the
        // SAT/LIA layer has it from the start. It MUST run here (over the base,
        // pre-selector-axiom assertions) rather than per-depth: the DT selector
        // unroll and `solve_fn`'s preprocessing must see the congruence uniformly
        // with everything else, exactly like every other base fact. Sound: each
        // clause is the congruence tautology `(= a b) ⟹ (= f(a) f(b))`, valid in
        // every model, so it can only prune spurious models — never false-UNSAT.
        // Appending to the (already-lifted, non-restored) assertion window matches
        // this function's existing `self.ctx.assertions = lifted` discipline.
        let bridge_congruence_axioms = {
            let base: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
            self.dt_uf_bridge_congruence_axioms(&base)
        };
        self.ctx.assertions.extend(bridge_congruence_axioms);

        let occurs_check_assertions = self.ctx.assertions.clone();
        if self.dt_occurs_check_unsat_from_equalities(&occurs_check_assertions, &[]) {
            self.last_unknown_reason = None;
            return Ok(SolveResult::unsat());
        }

        // Lazy iterative-deepening DT final-check for the combined DT+X routes,
        // mirroring `solve_dt`. The eager unroll is a warm-start fast path; on
        // Unknown we re-solve at a strictly larger recursive depth (materializing
        // the next selector frontier + its entailed (C)/(D) axioms) until the
        // verdict is definitive, the structure is fully unrolled (term-store
        // fixpoint), or the deepening ceiling is hit (fail-closed Unknown). Each
        // round only adds datatype-theory tautologies, so a SAT/UNSAT verdict at
        // any depth is sound and returned immediately.
        let warm_start = crate::executor::dt_axioms::DT_WARM_START_DEPTH;
        // M5 demand lane — LAW #5 (DT resume-not-restart) + the DT co-budget half of
        // LAW #4/#7. When the lane is ARMED (a classified self-chaining/bridge-cycle
        // family is present), RESUME the DT deepening from the depth this solve
        // reached last demand round (never restarting the shallow depths), and BOUND
        // the deepening ceiling to the generation frontier `F` (`warm_start + F`) so
        // the DT selector unroll co-budgets with the same frontier that gates
        // E-matching — the second minter cannot outrun the first. When the lane is
        // NOT armed (no classified family, or the force-eager override), the gate
        // below reads `demand_active()==false` and both fall back to the stock
        // warm-start / 64 ceiling — byte-identical to the pre-flip eager path.
        let (mut depth, ceiling) = {
            let qm_demand = self.quantifier_manager.as_ref().map(|qm| {
                (
                    qm.demand_active(),
                    qm.demand_dt_resume_depth(),
                    qm.demand_frontier(),
                )
            });
            match qm_demand {
                Some((true, resume, frontier)) => {
                    let start = resume.max(warm_start);
                    let cbudget = warm_start.saturating_add(frontier as usize).max(start);
                    (start, cbudget)
                }
                _ => (
                    warm_start,
                    crate::executor::dt_axioms::DT_MAX_DEEPENING_DEPTH,
                ),
            }
        };
        // (B10: the INTERFACE-DIET M0(c) depth-pin diagnostic and its
        // AY_DT_EAGER_DEPTH_OVERRIDE env flag are deleted — the flood
        // attribution question it existed for is settled; unset was already
        // byte-identical control flow.)
        let mut prev_term_len: Option<usize> = None;
        // D0 model-e-graph recheck pass (#dt-model-recheck): constructed once
        // per solve so its clause dedup / fresh-EUF validation state persists
        // across recheck rounds (a re-emitted clause fails closed instead of
        // looping).
        let mut model_recheck_pass = ay_dt::DtEgraphPass::new();
        for (dt_name, ctors) in self.ctx.datatype_iter() {
            model_recheck_pass.register_datatype(dt_name, ctors);
        }
        let mut recheck_rounds = 0u32;
        // Whether any declared constructor carries a datatype-sorted field
        // (recursive / nested datatypes — the deep-case-split family). Guards
        // the refuted-witness deepening backstop below so flat/enum problems
        // (e.g. the heavy all-nullary Bouvier instances) never pay an extra
        // in-loop gate run.
        let deepen_on_refuted_witness = {
            let dt_names: HashSet<&str> = self.ctx.datatype_iter().map(|(n, _)| n).collect();
            self.ctx
                .datatype_iter()
                .flat_map(|(_, cs)| cs.iter())
                .filter_map(|c| self.ctx.constructor_selector_info(c))
                .flatten()
                .any(|(_, fsort)| match fsort {
                    Sort::Uninterpreted(n) => dt_names.contains(n.as_str()),
                    Sort::Datatype(dt) => dt_names.contains(dt.name.as_str()),
                    _ => false,
                })
        };
        loop {
            if self.should_abort_theory_loop() {
                return Ok(SolveResult::Unknown);
            }
            // LAW #5: persist the depth reached so the next demand round resumes
            // here. Guarded on the actual armed state (`demand_active`), so it is a
            // no-op when no classified family is present (byte-identical).
            if let Some(qm) = self.quantifier_manager.as_mut() {
                if qm.demand_active() {
                    qm.demand_set_dt_resume_depth(depth);
                }
            }
            let pre_axiom_term_len = self.ctx.terms.len();
            let result =
                self.solve_with_dt_axioms_at_depth(acyclicity_sort.clone(), solve_fn, depth);
            // M5 LAW #4 (DT-emitter charge-AND-tag): the selector emitter just minted
            // the depth-`depth` selector frontier (`sel_i(...)`, its (C)/(D) axioms)
            // as fresh terms — the campaign's SECOND minter. Tag those newly-minted
            // terms (TermId >= the pre-axiom watermark) with a generation so a
            // subsequent interleave E-matching round cannot re-enter the frontier
            // gate with a laundered gen-0 DT-minted term (closing the DT-side gen-0
            // laundering hole). Charged at `depth` (the DT unroll depth this frontier
            // sits at). Guarded on the actual armed state; `demand_tag_dt_minted`
            // also no-ops unless the lane is armed, so this is inert (byte-identical)
            // when no classified family is present.
            if self.demand_lane_armed() {
                let end = self.ctx.terms.len();
                let tag_gen = u32::try_from(depth).unwrap_or(u32::MAX).max(1);
                if let Some(qm) = self.quantifier_manager.as_mut() {
                    qm.demand_tag_dt_minted(pre_axiom_term_len, end, tag_gen);
                }
            }
            if ay_core::misc_cli_flags().phase_trace {
                eprintln!(
                    "c phase-trace dt-round-result depth={} result={:?} reason={:?}",
                    depth,
                    result.as_ref().map(|r| format!("{r:?}")),
                    self.last_unknown_reason
                );
            }

            // SOUNDNESS: the DT selector/injectivity axioms materialized above are
            // derived from syntactic terms. Constructor injectivity *through array
            // equality* (`store(a,i,Ctor x) = store(b,i,Ctor (x+1))`) is now
            // emitted by `dt_store_value_injectivity_axioms` for the store-pair
            // fragment, so those decidable instances reach a genuine UNSAT here.
            // For the residual (uncovered) datatype-carrying-array hazards the
            // array/BV core still carries no datatype theory, so a Sat can be a
            // FALSE SAT (the arrays must differ at index i, yet the bit-blasted
            // model satisfies the equality). `dt_array_injectivity_gate_bypass`
            // records whether the bridge PROVABLY modeled every hazard; when it
            // did not, DEFER to the INDEPENDENT, fail-closed ground-evaluation
            // gate before degrading — exactly as the sibling gate in
            // `finalize_sat_model_validation` (pipeline.rs) does. That gate
            // re-checks EVERY assertion against the emitted model with a
            // solver-independent evaluator, resolving each datatype-carrying array
            // through its asserted store-chain / definitional equality: it
            // DIRECTLY decides the constructor-injectivity-through-array-equality
            // hazard this gate guards (computing `(= (store a i (C x)) (store b i
            // (C (x+1))))` FALSE and REFUTING such a model), while CONFIRMING a
            // genuinely-SAT datatype-array model the syntactic footprint check
            // cannot certify. Only a full `ConfirmedSat` skips the degrade;
            // `ModelViolates` / `CannotConfirm` still degrade (fail-closed).
            // UNSAT and datatype-free results stay sound and are returned
            // unchanged. (#dt-array-store-value-injectivity, #dt-array-defer-to-independent-gate)
            if dt_carrying_array_eq
                && !self.dt_array_injectivity_gate_bypass
                && !self.last_model_validated
                && matches!(&result, Ok(SolveResult::Sat))
                && !matches!(
                    self.confirm_sat_with_independent_gate(),
                    ay_model_check::GateVerdict::ConfirmedSat
                )
            {
                self.last_degrade_was_datatype_array = true;
                if ay_core::misc_cli_flags().phase_trace {
                    eprintln!("c phase-trace dt-array-gate-demoted-sat depth={depth}");
                }
                self.last_unknown_reason = Some(crate::executor_types::UnknownReason::Incomplete);
                return Ok(SolveResult::Unknown);
            }

            // Post-`Sat` D0 model-e-graph recheck (#dt-model-recheck, stage-4
            // review F1): the BV routes have no combiner-hosted D0 pass and no
            // acyclicity depth axioms, so a decoded model whose TRUE datatype
            // equalities congruence-close into a constructor cycle/clash was
            // returned as Sat (min-pred + one BV declaration). A verified
            // conflict re-asserts its DT tautology clause and re-solves at the
            // same depth (never a false-UNSAT: the clause is theory-valid);
            // an unemittable conflict — or a recheck budget overrun — degrades
            // to a sound Unknown (fail-closed). See `dt_model_egraph_recheck`.
            // Run on `Sat` AND on `Unknown` rounds: the executor-side strict
            // in-loop validation (#dt-total-model, merged alongside this
            // pass) can demote the very wrong-SAT this recheck was built to
            // close (F1 min-pred: fabricated `succ^k(zero)` witness) to a
            // round-`Unknown` BEFORE the recheck sees a `Sat` — but the
            // decoded model (and its cycle-closing TRUE equalities) is still
            // present, and only the injected DT tautology clause can turn the
            // futile deepening into the genuine `unsat`. Conflict-only and
            // clause-validated, so running it on an Unknown round can never
            // manufacture a verdict — it either injects an entailed clause
            // and re-solves, or changes nothing.
            if matches!(&result, Ok(SolveResult::Sat) | Ok(SolveResult::Unknown)) {
                let round_was_sat = matches!(&result, Ok(SolveResult::Sat));
                match self.dt_model_egraph_recheck(&mut model_recheck_pass) {
                    DtModelRecheck::Clean => {}
                    DtModelRecheck::LemmasInjected => {
                        recheck_rounds += 1;
                        if recheck_rounds > DT_MODEL_RECHECK_MAX_ROUNDS {
                            self.last_unknown_reason =
                                Some(crate::executor_types::UnknownReason::Incomplete);
                            return Ok(SolveResult::Unknown);
                        }
                        if ay_core::misc_cli_flags().phase_trace {
                            eprintln!(
                                "c phase-trace dt-model-recheck-resolve \
                                 round={recheck_rounds} depth={depth}"
                            );
                        }
                        continue;
                    }
                    DtModelRecheck::Inconclusive => {
                        if round_was_sat {
                            if ay_core::misc_cli_flags().phase_trace {
                                eprintln!(
                                    "c phase-trace dt-model-recheck-inconclusive depth={depth}"
                                );
                            }
                            self.last_unknown_reason =
                                Some(crate::executor_types::UnknownReason::Incomplete);
                            return Ok(SolveResult::Unknown);
                        }
                        // An Unknown round stays Unknown; let the ordinary
                        // deepening logic below decide what happens next.
                    }
                }
            }

            // Refuted-witness deepening backstop (#dt-deepen-refuted-witness):
            // a round-accepted `Sat` whose model in-loop validation did NOT
            // confirm and the INDEPENDENT, fail-closed gate REFUTES
            // (`ModelViolates`) can never survive the emit funnel — the
            // #sat-chokepoint gate would fail-close it to a public Unknown.
            // On a recursive/nested-datatype problem such a witness is the
            // deep-case-split signature (the eager unroll is too shallow to
            // materialize any model the asserted disequalities permit, e.g.
            // `n` distinct from `succ^0..k(zero)` at unroll depth < k+1), and
            // deepening is exactly the remedy. Strictly fail-closed: only a
            // gate-REFUTED unvalidated Sat is demoted to this round's
            // Unknown, and the loop's exhaustion path returns Unknown — the
            // same public verdict the emit gate would have produced — while a
            // deeper round may recover a genuine, materializable Sat.
            let result = if deepen_on_refuted_witness
                && depth < ceiling
                && matches!(&result, Ok(SolveResult::Sat))
                && matches!(
                    self.confirm_sat_with_independent_gate(),
                    ay_model_check::GateVerdict::ModelViolates { .. }
                ) {
                if ay_core::misc_cli_flags().phase_trace {
                    eprintln!("c phase-trace dt-deepen-refuted-witness depth={depth}");
                }
                self.last_unknown_reason = Some(crate::executor_types::UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            } else {
                result
            };

            if !matches!(&result, Ok(SolveResult::Unknown)) {
                return result;
            }

            // Exact finite-array exhaustion is query-cumulative and
            // depth-invariant: later DT rounds cannot replenish the ledger, so
            // retrying would only rebuild the same relaxed obligation and risk
            // reviving artifacts already revoked by the SAT fail-close gate.
            if !self.finite_array_expansion.is_complete() {
                self.publish_unknown_from_origin(
                    crate::executor_types::UnknownOrigin::DeterministicResourceBudget,
                );
                return Ok(SolveResult::Unknown);
            }

            // Perf backstop (#dt-array-degrade-backstop): if this round's Unknown
            // came from the datatype-carrying-array degrade gate, deepening cannot
            // change it — both gate inputs are depth-invariant
            // (`problem_has_datatype_carrying_array` is monotone-true; the
            // injectivity-gate bypass is computed once from the original
            // assertions). Return the Unknown now instead of re-bit-blasting the
            // whole instance up to the deepening ceiling. Strictly degrade-only: a
            // definitive Sat/Unsat already returned above, so this touches no
            // Sat/Unsat verdict. With the observational-completeness bypass active
            // this flag is never set for an otherwise-Sat instance, so the genuine
            // Sat is still returned.
            if self.last_degrade_was_datatype_array {
                return result;
            }

            let post_axiom_term_len = self.ctx.terms.len();
            let grew = post_axiom_term_len > pre_axiom_term_len;
            let advanced_vs_prev = prev_term_len.is_none_or(|p| post_axiom_term_len > p);
            prev_term_len = Some(post_axiom_term_len);

            if !grew || !advanced_vs_prev || depth >= ceiling {
                return result;
            }
            if ay_core::misc_cli_flags().phase_trace {
                eprintln!(
                    "c phase-trace dt-deepening next_depth={}",
                    depth.saturating_add(1)
                );
            }
            depth = depth.saturating_add(1);
        }
    }

    /// Run one combined DT+X solve at a fixed eager-unroll `max_recursive_depth`.
    ///
    /// Extracted from `solve_with_dt_axioms` so the iterative-deepening
    /// final-check can re-solve at increasing depths. Behaviour at the
    /// warm-start depth is identical to the original single-pass solve,
    /// including the spurious-acyclicity-UNSAT post-hoc re-check.
    fn solve_with_dt_axioms_at_depth(
        &mut self,
        acyclicity_sort: Option<Sort>,
        solve_fn: fn(&mut Self) -> Result<SolveResult>,
        max_recursive_depth: usize,
    ) -> Result<SolveResult> {
        let base_assertions: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut extra_axioms =
            self.dt_selector_axioms_to_depth(&base_assertions, max_recursive_depth);
        // Field-level selector-congruence for datatype-valued array selects at
        // symbolic indices (the static DT axioms above do not cover these; see
        // dt_array_select_field_congruence_axioms). Sound: only entailed
        // instances of array∘selector congruence — cannot cause false-unsat.
        extra_axioms.extend(self.dt_array_select_field_congruence_axioms(&base_assertions));
        // SCALAR-PROJECTION select-congruence (#dt-array-select-scalar-projection):
        // route datatype-valued-select scalar-field projections through FRESH
        // scalar arrays so the eager array lane's own select-congruence connects a
        // DERIVED-equal index (the guarded field-congruence above cannot — its
        // EUF-routed datatype consequent leaves the guard disconnected). Sound:
        // fresh arrays constrained only by their definitional cell pins + array
        // congruence tautology. This is the z3-style lazy datatype-array reasoning
        // that lets datatype-array SELECT-congruence reach a genuine verdict.
        extra_axioms.extend(self.dt_array_select_scalar_projection_axioms(&base_assertions));
        // Field-level decomposition for select-vs-constructor equalities
        // (#dt-select-ctor-field-decomposition) — the seam the pass above and
        // the static selector pass both miss; sound (datatype tautologies).
        extra_axioms.extend(self.dt_array_select_ctor_field_axioms(&base_assertions));
        // Constructor injectivity/disjointness through array STORE-value equality
        // (#dt-array-store-value-injectivity). The static DT axioms above only
        // fire on syntactic constructor equalities; a datatype value stored into
        // an array and equated *through* an array equality
        // (`store(a,i,C x) = store(b,i,C (x+1))`) never surfaces its
        // value-injectivity to the array/BV or array/LIA participant, so the
        // combined route returns a spurious SAT (degraded, fail-closed, by the
        // datatype-carrying-array gate). This pass emits the missing entailment
        // as a valid Array+DT implication; sound (shrinks the model space only),
        // and it lets the decidable instances (`inj_dt_bv`, `inj_dt_int`) reach a
        // genuine UNSAT so the gate never has to fire. See the method docs.
        extra_axioms.extend(self.dt_store_value_injectivity_axioms(&base_assertions));
        // Read-over-equality congruence for datatype-ELEMENT array equalities
        // (#dt-array-eq-read-congruence). A `(= X Y)` over an `Array _ D` (D a
        // datatype) has NO cell-level bit-blast semantics, so injectivity is not
        // surfaced when the equality reaches the solver indirectly (e.g. X bound
        // to `(ite g (store a i (C v)) a)`) — a spurious SAT. Emitting
        // `(=> (= X Y) (= (select X i) (select Y i)))` at every observed index
        // lets the synthesized selects fold through ROW/select-over-ite to the
        // stored constructors. Sound: read-over-array-equality is valid in every
        // model (functional congruence), so it can only prune spurious models.
        extra_axioms.extend(self.dt_array_equality_read_congruence_axioms(&base_assertions));
        // Value-equality congruence for BARE datatype-valued operands `(= x y)`
        // where neither side is a constructor application
        // (#dt-value-eq-congruence). The static DT axioms only fire on
        // constructor-side equalities; a bare two-const datatype equality with
        // cross-theory (Array/BV) fields gets no congruence, so EUF can place
        // x,y in distinct classes even when the field theory forces every field
        // equal -> spurious model (degraded to incomplete by the validation
        // gate). Sound: the emitted EXACT datatype-equality biconditional is a
        // datatype tautology, so it can never cause a false-unsat.
        extra_axioms.extend(self.dt_datatype_value_equality_congruence_axioms(&base_assertions));

        // Guarded datatype-acyclicity clauses from disjunctive contexts
        // (#dt-acyclic-case-split); see `solve_dt` for the rationale. Sound for
        // combined DT+X paths too: a structural cycle is a datatype-only fact.
        let assertions_snapshot = self.ctx.assertions.clone();
        extra_axioms.extend(self.dt_guarded_acyclicity_disjuncts(&assertions_snapshot, &[]));
        // See `solve_dt`: guard-forcing units for single-guard hidden cycles.
        extra_axioms.extend(self.dt_guarded_acyclicity_guard_units(&assertions_snapshot, &[]));
        // Also mine the PRE-lift snapshot: the ite-lift (#5082) turns an
        // unconditional ctor equality into a guarded ITE that the miner's
        // unconditional-equality collector misses, dropping the entailed
        // cycle-breaking unit (fuzz881). Pre-lift-derived units are entailed by
        // the original assertions (lifting is semantics-preserving), so this is
        // sound and can only prune spurious models. Skip when empty / identical.
        if !self.dt_pre_lift_assertions.is_empty()
            && self.dt_pre_lift_assertions != assertions_snapshot
        {
            let pre_lift = self.dt_pre_lift_assertions.clone();
            extra_axioms.extend(self.dt_guarded_acyclicity_disjuncts(&pre_lift, &[]));
            extra_axioms.extend(self.dt_guarded_acyclicity_guard_units(&pre_lift, &[]));
        }

        if let Some(ref sort) = acyclicity_sort {
            extra_axioms.extend(self.dt_acyclicity_depth_axioms(sort.clone()));
        }

        if self.produce_proofs_enabled() {
            self.record_dt_axiom_theory_lemmas(&extra_axioms);
        }

        let base_assertions_exact = self.ctx.assertions.clone();
        // Record the appended axiom terms so the in-loop validation's
        // #dt-embedded-cycle compound guard exempts them (each is an entailed
        // datatype tautology; see `dt_solver_added_axiom_terms`).
        self.dt_solver_added_axiom_terms
            .extend(extra_axioms.iter().copied());
        self.ctx.assertions.extend(extra_axioms);
        let result = solve_fn(self);
        self.ctx.assertions = base_assertions_exact;
        self.dt_solver_added_axiom_terms.clear();

        // Post-hoc soundness re-check for spurious acyclicity UNSAT
        // (#dt-array-acyc wrong-unsat / FALSE THEOREM). The recursive selector
        // unfolding (axiom E in `dt_selector_axioms`) synthesizes constructor
        // terms — e.g. `(node0 (lft0 X) (rgt0 X))` — as conditional tautological
        // expansions of a selector chain. The acyclicity DEPTH axioms generated
        // over those ARTIFACTS, once EUF merges the unfolded equality and the
        // array layer (aliased arrays + nested store + a fresh
        // extensionality-skolem index) forces a structure on `X`, close a
        // SPURIOUS depth cycle and drive a false UNSAT that no model contradicts.
        // When the result is UNSAT and acyclicity was enabled, re-solve with the
        // depth axioms SCOPED to genuine pre-selector-axiom (asserted) structure.
        // If the scoped solve is not UNSAT, the unsat depended on the artifact
        // depth axioms and is untrustworthy → degrade to Unknown.
        //
        // Sound + non-regressing: the PRIMARY solve above is byte-for-byte
        // unchanged (so timing/path-dependent verdicts elsewhere are untouched),
        // and the re-check only ever downgrades UNSAT→Unknown. Genuine direct/
        // indirect cycles (`x = cons(a,y)`, `y = cons(b,x)`) keep their depth
        // axioms in the scoped re-solve (those constructor terms are asserted),
        // so their unsat survives and is preserved.
        if acyclicity_sort.is_some()
            && matches!(&result, Ok(r) if r.is_unsat())
            && self.dt_acyclicity_unsat_is_spurious(acyclicity_sort, solve_fn)
        {
            self.last_unknown_reason = Some(crate::executor_types::UnknownReason::Incomplete);
            return Ok(SolveResult::Unknown);
        }
        result
    }

    /// Re-solve with acyclicity depth axioms SCOPED to the pre-selector-axiom
    /// term store (genuine asserted constructor structure only) and report
    /// whether the result is NOT unsat — i.e. the original unsat depended on the
    /// recursive-selector-unfolding ARTIFACT depth axioms and is therefore a
    /// spurious FALSE THEOREM. See the caller for the soundness argument.
    fn dt_acyclicity_unsat_is_spurious(
        &mut self,
        acyclicity_sort: Option<Sort>,
        solve_fn: fn(&mut Self) -> Result<SolveResult>,
    ) -> bool {
        let Some(sort) = acyclicity_sort else {
            return false;
        };
        // Snapshot the term-store size BEFORE selector-axiom generation so the
        // scoped acyclicity scan excludes the synthetic artifacts (TermId >=
        // limit). The selector/acyclicity passes are re-run from the same
        // base_assertions; selector axioms are regenerated (idempotent on the
        // store) and acyclicity is restricted to the genuine asserted window.
        let acyclicity_scan_limit = self.ctx.terms.len();
        let base_assertions: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut extra_axioms = self.dt_selector_axioms(&base_assertions);
        extra_axioms.extend(self.dt_acyclicity_depth_axioms_up_to(sort, acyclicity_scan_limit));
        // Re-emit the store-value constructor-injectivity bridge in the scoped
        // re-solve too. These are genuine Array+DT entailments (NOT recursive-
        // selector-unfolding artifacts), so an UNSAT that legitimately depends on
        // them (e.g. `store(a,i,C x) = store(b,i,C (x+1))` ⇒ `x = x+1`) must
        // survive the scoping. Omitting them reproduces the pre-bridge false-SAT,
        // which would wrongly flag the genuine UNSAT as spurious and spin the
        // iterative-deepening loop to the ceiling (#dt-array-store-value-injectivity).
        extra_axioms.extend(self.dt_store_value_injectivity_axioms(&base_assertions));

        if self.produce_proofs_enabled() {
            self.record_dt_axiom_theory_lemmas(&extra_axioms);
        }

        let base_assertions_exact = self.ctx.assertions.clone();
        // Record the appended axiom terms so the in-loop validation's
        // #dt-embedded-cycle compound guard exempts them (each is an entailed
        // datatype tautology; see `dt_solver_added_axiom_terms`).
        self.dt_solver_added_axiom_terms
            .extend(extra_axioms.iter().copied());
        self.ctx.assertions.extend(extra_axioms);
        let scoped_result = solve_fn(self);
        self.ctx.assertions = base_assertions_exact;
        self.dt_solver_added_axiom_terms.clear();

        // Spurious iff the scoped (artifact-free) re-solve does NOT reproduce the
        // unsat. A genuine cycle stays unsat under scoping (asserted constructors
        // keep their depth axioms), so it is correctly NOT flagged as spurious.
        !matches!(&scoped_result, Ok(r) if r.is_unsat())
    }

    /// Post-`Sat` D0 clash/acyclicity recheck of the DECODED MODEL's e-graph
    /// (#dt-model-recheck, stage-4 review F1).
    ///
    /// The combined DT+BV routes (`solve_dt_ufbv`/`solve_dt_aufbv`) bit-blast:
    /// no `TheoryCombiner` hosts the D0 [`ay_dt::DtEgraphPass`], and the eager
    /// DT axioms carry no acyclicity depth axioms (there is no arithmetic sort
    /// to encode depth), so a SAT-core assignment whose TRUE datatype
    /// equalities congruence-close into a constructor cycle or clash was
    /// accepted as `Sat` (the `min-pred` shape plus one irrelevant BV
    /// declaration: WRONG-SAT).
    ///
    /// This recheck re-derives, on a FRESH EUF solver, the e-graph the model
    /// commits to — every datatype-sorted equality atom that is asserted as a
    /// top-level unit or TRUE in the SAT model — and runs the same conflict-only
    /// D0 pass over it:
    ///
    /// - `Ok`: the model is consistent with the D0 rules; `Sat` stands.
    /// - `Lemmas`: a verified conflict (validated by the pass's own independent
    ///   fresh-EUF re-derivation) is appended to the assertions as a datatype
    ///   tautology clause and the caller re-solves. The clause is true in every
    ///   model of the datatype theory, so it prunes only DT-inconsistent
    ///   assignments — it can never manufacture a false-UNSAT.
    /// - `Inconclusive`: fail-closed; the caller degrades to `Unknown`.
    ///
    /// Combiner-backed lanes (`solve_dt_ax`, the arith routes) run the in-loop
    /// D0 pass already; for them this recheck is defense-in-depth over an
    /// e-graph that arrives clean. Model-free `Sat` paths (assertions
    /// simplified away) have no solver-derived merges to check and pass
    /// trivially.
    fn dt_model_egraph_recheck(&mut self, pass: &mut ay_dt::DtEgraphPass) -> DtModelRecheck {
        if pass.is_inert() {
            return DtModelRecheck::Clean;
        }
        let Some(model) = self.last_model.as_ref() else {
            // No decoded model: nothing beyond the raw assertions was
            // committed (trivially-sat preprocessing path) — no derived
            // e-graph exists to violate the D0 rules.
            return DtModelRecheck::Clean;
        };

        // Datatype sort names (internal, possibly instance-mangled).
        let dt_names: HashSet<String> = self
            .ctx
            .datatype_iter()
            .map(|(name, _)| name.to_string())
            .collect();
        let is_dt_sort = |sort: &Sort| match sort {
            Sort::Datatype(dt) => dt_names.contains(&dt.name),
            Sort::Uninterpreted(name) => dt_names.contains(name),
            _ => false,
        };

        // The model's TRUE datatype equalities: asserted top-level units are
        // true in every accepted model; everything else reads the SAT
        // assignment (this is where the axiom-(C) instantiation equalities
        // `t = C(sel_1 t, ...)` the bit-blast core decided live). An atom the
        // SAT layer never saw is skipped — fewer merges can only MISS a
        // conflict (fail-open for that atom; the always-on gates remain the
        // backstop), never invent one.
        let asserted: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut true_eqs: Vec<TermId> = Vec::new();
        for raw in 0..self.ctx.terms.len() {
            let tid = TermId(raw as u32);
            let TermData::App(Symbol::Named(sym), args) = self.ctx.terms.get(tid) else {
                continue;
            };
            if sym.as_str() != "=" || args.len() != 2 || !is_dt_sort(self.ctx.terms.sort(args[0])) {
                continue;
            }
            let truth = if asserted.contains(&tid) {
                Some(true)
            } else {
                self.term_value(&model.sat_model, &model.term_to_var, tid)
            };
            if truth == Some(true) {
                true_eqs.push(tid);
            }
        }
        if true_eqs.is_empty() {
            return DtModelRecheck::Clean;
        }

        let outcome = {
            let mut euf = ay_euf::EufSolver::new(&self.ctx.terms);
            for &eq in &true_eqs {
                euf.assert_literal(eq, true);
            }
            // Positive equalities alone are always EUF-consistent; check()
            // just settles the congruence closure the pass reads.
            let _ = euf.check();
            pass.check(&self.ctx.terms, &mut euf)
        };
        match outcome {
            ay_dt::DtPassOutcome::Ok => DtModelRecheck::Clean,
            ay_dt::DtPassOutcome::Inconclusive => DtModelRecheck::Inconclusive,
            ay_dt::DtPassOutcome::Lemmas(lemmas) => {
                for lemma in lemmas {
                    let lits: Vec<TermId> = lemma
                        .clause
                        .iter()
                        .map(|l| {
                            if l.value {
                                l.term
                            } else {
                                self.ctx.terms.mk_not(l.term)
                            }
                        })
                        .collect();
                    let clause_term = if lits.len() == 1 {
                        lits[0]
                    } else {
                        self.ctx.terms.mk_or(lits)
                    };
                    self.ctx.assertions.push(clause_term);
                }
                DtModelRecheck::LemmasInjected
            }
        }
    }

    /// Solve combined DT + LIA (#1760). DT axioms + acyclicity(Int) → AUFLIA.
    pub(in crate::executor) fn solve_dt_auflia(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // L1a lazy-DT-AUFLIA on-demand route (combined-theory-engine campaign;
        // `AY_DT_LAZY_AUFLIA`, unset/`0` ⇒ byte-identical eager path below).
        // SHADOW-FIRST: the flag is OFF by default, so the eager authority is
        // untouched. When ON (measurement / the eager-shadow differential) the
        // lazy lane is attempted first; a DEFINITIVE verdict passes the same
        // always-on model gates as any other route and is returned, otherwise
        // the lane falls through with full state restoration to the eager
        // authority. See `try_solve_dt_auflia_lazy`.
        if std::env::var_os("AY_DT_LAZY_AUFLIA").is_some_and(|v| v != "0") {
            if let Some(result) =
                self.try_solve_dt_auflia_lazy_maybe_incremental(Self::solve_auf_lia)?
            {
                return Ok(result);
            }
        }
        self.solve_with_dt_axioms(Some(Sort::Int), Self::solve_auf_lia)
    }

    /// Revoke verdict/output artifacts produced by a discarded lazy-DT solve.
    ///
    /// This is deliberately narrower than `invalidate_last_check_result`:
    /// fallback is an internal retry of the SAME public query, so its immutable
    /// UNSAT epoch, Pareto frontier, and proof-source provenance must survive.
    /// Tracker-correlated provenance is either retained with the AUFLIA guard's
    /// terms or restored from the entry snapshot before a real term rollback.
    /// The SAT-reconstruction bundle (`last_clause_trace`, var/trail maps,
    /// negations, and clause annotations) is deliberately discarded: it is
    /// output from the failed SAT run, not `ProofTracker` provenance, and the
    /// eager fallback must rebuild the whole bundle from its own clause DB.
    fn revoke_dt_lazy_attempt_artifacts(&mut self) {
        self.last_result = None;
        self.last_model = None;
        self.last_sat_certificate = None;
        self.last_unsat_certificate = None;
        self.last_assumption_core = None;
        self.last_proof = None;
        self.clear_finite_enum_proof_state();
        self.last_lrat_certificate = None;
        self.last_proof_quality = None;
        self.last_unknown_reason = None;
        self.last_unknown_origin = None;
        self.last_clause_trace = None;
        self.last_checked_sat_refutation = None;
        self.last_var_to_term = None;
        self.last_trail_provenance = None;
        self.last_negations = None;
        self.last_clausification_proofs = None;
        self.last_original_clause_theory_proofs = None;
        self.proof_check_result = None;
        self.proof_check_ok = false;
        self.pending_sat_unknown_reason = None;
        self.last_model_validated = false;
        self.clear_quantified_sat_authority();
        self.last_validation_stats = None;
        self.model_validation_delegated_assertions.clear();
        self.dt_solver_added_axiom_terms.clear();
        self.last_soft_cost = None;
        self.last_soft_cost_optimal = true;
        self.last_soft_violations = None;
        self.finite_objective_values.clear();
        self.unbounded_objectives.clear();
        self.infinitesimal_objectives.clear();
        self.unavailable_objectives.clear();
        self.objective_certificates.clear();
    }

    /// Drop indexes whose entries are derived from the current TermStore.
    ///
    /// A lazy-DT fallback shrinks the store, so preserving any suffix-derived
    /// entry would let a subsequently recycled numeric `TermId` inherit facts
    /// about the discarded term. Snapshot-keyed model indexes are cleared as
    /// well: rebuilding them is cheap compared with making their shrink
    /// detection part of this rollback's soundness argument.
    fn clear_dt_lazy_rebuildable_term_indexes(&mut self) {
        self.reset_array_congruence_caches();
        *self.select_by_array_index.borrow_mut() = (0, Default::default());
        *self.array_def_index.borrow_mut() = None;
        *self.required_terms_index.borrow_mut() = None;
        ay_euf::clear_bool_arg_repair_candidates();
    }

    /// Lazy DT + LIA lane (campaign L1a): solve the DT+LIA(+Array) residual
    /// with the eager depth-3 selector/array axiom flood REPLACED by a SPARSE
    /// on-demand DT axiom set materialized at only the occurrence-driven
    /// UNION-relevant datatype terms (`ay_dt::occurrence_relevant_dt_terms`).
    ///
    /// M0a proved (on the rusthorn List-sum VC gl.smt2) that stripping ay's
    /// 4213 eager axioms and injecting z3's ~28 on-demand DT axioms at 7 ground
    /// terms flips a 206K-decision wedge into a correct UNSAT at 24.6–40K
    /// decisions, because the sparse axioms are present at CLAUSIFICATION and
    /// let the preprocessor collapse the 2018-clause base to ~250 — the eager
    /// per-depth axioms are bolted on AFTER the base is fixed and never feed
    /// that simplification. This lane reconstructs that effect: the sparse
    /// axioms are asserted UPFRONT (not fixpoint-emitted), which is why they
    /// feed base simplification. M0b proved the occurrence-driven UNION
    /// criterion discovers those terms in one round.
    ///
    /// Soundness frame (identical to `try_solve_dt_lazy`):
    /// - the depth-1 syntactic axiom slice STAYS as the floor
    ///   (`AY_DT_LAZY_AUFLIA_DEPTH`, default 1); the sparse relevance axioms are
    ///   ADDITIVE above it, never a wholesale drop of the eager grounding;
    /// - the UF-bridge congruence stays EAGER (dn110 / `inc_some_list` UNSAT);
    /// - every emitted clause is a datatype tautology (exhaustiveness /
    ///   exclusivity / reconstruction), so it can only prune spurious models;
    /// - a lane `Sat` the independent fail-closed gate ground-REFUTES is demoted
    ///   to a lane miss (the relevance-miss backstop) → eager fallback;
    /// - the incremental gate is CLAMPED (non-incremental scope only);
    /// - on any Unknown the entry assertions are restored; the term/proof
    ///   ledgers are restored together unless the measured AUFLIA proof-step
    ///   guard retains both, in which case no recycled ID can dangle.
    ///
    /// Returns `Ok(Some(_))` only for a definitive Sat/Unsat.
    ///
    /// `solve_fn` is the inner combiner the residual is routed through —
    /// `solve_auf_lia` (array-enabled) or `solve_uf_lia` (array-free) — chosen
    /// by the caller to match the eager authority it shadows.
    fn try_solve_dt_auflia_lazy(
        &mut self,
        solve_fn: fn(&mut Self) -> Result<SolveResult>,
    ) -> Result<Option<SolveResult>> {
        // Incremental gate (#dt-lazy-incremental-gate): the lane's term-store
        // rollback contract is unenforceable under a persistent incremental
        // session (recycled TermIds alias stale encodings → wrong-UNSAT). Skip.
        if self.incremental_mode
            || self.incr_theory_state.as_ref().is_some_and(|s| {
                s.scope_depth > 0
                    || s.pending_push > 0
                    || !s.encoded_assertions.is_empty()
                    || !s.pre_push_assertions.is_empty()
                    || s.persistent_sat.is_some()
                    || s.lia_persistent_sat.is_some()
            })
        {
            return Ok(None);
        }
        if !self.dt_lazy_lemma_cache_isolation_available() {
            return Ok(None);
        }
        // Eligibility: at least one RECURSIVE datatype (a constructor with a
        // datatype-sorted field). Pure enum/nullary content is handled by the
        // finite-domain lane; this route targets the recursive DT+LIA family.
        if !self.dt_auflia_lazy_eligible() {
            return Ok(None);
        }
        // The exact rollback snapshot below roughly doubles the TermStore
        // footprint. Decline this OPTIONAL lane before cloning when less than
        // that headroom remains; the eager authority below is unchanged.
        if !self.dt_auflia_snapshot_preflight() {
            return Ok(None);
        }
        let Ok(entry_proof_checkpoint) = self.bounded_proof_rollback_checkpoint() else {
            // Optional lane: preserve the eager authority when the cumulative
            // proof-snapshot allocation envelope has been exhausted.
            return Ok(None);
        };

        // Entry snapshots (mirror `try_solve_dt_lazy` isolation).
        let entry_assertions = self.ctx.assertions.clone();
        let entry_pre_lift = std::mem::take(&mut self.dt_pre_lift_assertions);
        let entry_terms_len = self.ctx.terms.len();
        // A failed detour may replace `ctx.terms`, changing rollback identity;
        // this opt-in lane therefore pays for an exact store snapshot.
        let entry_terms = self.ctx.terms.clone();
        let entry_proof_steps = self.proof_tracker.num_steps();
        let entry_lazy_proof_state = lazy_proof_state::DtLazyProofState::capture(self);
        let entry_attempt_state = DtLazyAttemptState::capture(self);
        let entry_lia_probe_state = ay_lia::save_probe_state();
        // A fallback can occur only once: both call sites immediately return.
        // Keep this closure `FnOnce` so restoring the entry store MOVES the
        // snapshot instead of briefly holding a third full TermStore clone.
        let rollback_on_fallback = move |this: &mut Self| {
            // These move assignments make fallback one affine transaction:
            // every call site consumes the same exact entry assertion window
            // and pre-lift state together with the owned term universe below.
            this.ctx.assertions = entry_assertions;
            this.dt_pre_lift_assertions = entry_pre_lift;
            // Only user-requested proof output prevents term rollback. The
            // tracker is enabled for every public decision and is not by
            // itself evidence that speculative terms must survive.
            let proof_guard_blocks_term_rollback =
                this.is_producing_proofs() && this.proof_tracker.num_steps() != entry_proof_steps;

            // The inner attempt is not a public query result. Revoke its
            // output artifacts and typed quantified-SAT authority without
            // destroying the enclosing query's UNSAT/Pareto authority.
            this.revoke_dt_lazy_attempt_artifacts();
            this.clear_dt_theory_model();
            this.dt_egraph_assignment.replace(None);
            let entry_array_ext_witness_cache = entry_attempt_state.restore(this);
            ay_lia::restore_probe_state(entry_lia_probe_state);
            crate::executor::model::eval_memo_clear();

            // Keep the measured AUFLIA proof-production guard: its fallback
            // retains the speculative proof ledger, correlated provenance,
            // and matching terms. Only user-visible result artifacts above are
            // revoked on this path.
            if proof_guard_blocks_term_rollback {
                this.proof_tracker
                    .restore_checkpoint_metadata(entry_proof_checkpoint);
                this.clear_dt_lazy_rebuildable_term_indexes();
                return;
            }

            entry_lazy_proof_state.restore(this);
            // ProofIds and TermIds are parallel positional ledgers. Discard all
            // proof-side references before TermStore can recycle its IDs.
            // The witness cache is proof/term provenance too: restore it only
            // when the corresponding speculative terms are actually removed.
            // On the proof guard path above, retaining it keeps generated
            // extensionality clauses reconstructible against the retained
            // tracker ledger.
            this.clear_dt_lazy_rebuildable_term_indexes();
            if !this.proof_tracker.rollback_to(entry_proof_checkpoint) {
                // A nested `take_proof`/reset moved the entry ledger away. A
                // watermark cannot rebuild that prefix, so retain terms rather
                // than risk dangling TermIds in the moved proof.
                return;
            }
            this.array_ext_witness_cache = entry_array_ext_witness_cache;
            restore_dt_auflia_entry_terms(&mut this.ctx.terms, entry_terms);
            this.clear_dt_lazy_rebuildable_term_indexes();
            if ay_core::misc_cli_flags().phase_trace {
                eprintln!("c phase-trace dt-auflia-lazy-rollback to={entry_terms_len}");
            }
        };

        // Preamble parity with the eager route (flatten AND wrappers; lift
        // non-Bool ITEs), snapshotting pre-lift assertions for guarded
        // acyclicity. Both rewrites are semantics-preserving and shared with
        // the eager fallback.
        let mut flatten = crate::preprocess::FlattenAnd::new();
        flatten.apply(&mut self.ctx.terms, &mut self.ctx.assertions);
        self.dt_pre_lift_assertions = self.ctx.assertions.clone();
        let lifted: Vec<TermId> = self.ctx.terms.lift_arithmetic_ite_all(&self.ctx.assertions);
        self.ctx.assertions = lifted;

        let occurs_check_assertions = self.ctx.assertions.clone();
        if self.dt_occurs_check_unsat_from_equalities(&occurs_check_assertions, &[]) {
            self.last_unknown_reason = None;
            return Ok(Some(SolveResult::unsat()));
        }

        // Depth-1 syntactic axiom slice (the load-bearing floor) + guarded
        // acyclicity mining, exactly as `try_solve_dt_lazy`.
        // B10: depth pinned at 1 (the AY_DT_LAZY_AUFLIA_DEPTH override
        // nothing set is retired).
        let depth: usize = 1;
        let base_assertions: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut extra_axioms = self.dt_selector_axioms_to_depth(&base_assertions, depth);
        let assertions_snapshot = self.ctx.assertions.clone();
        extra_axioms.extend(self.dt_guarded_acyclicity_disjuncts(&assertions_snapshot, &[]));
        extra_axioms.extend(self.dt_guarded_acyclicity_guard_units(&assertions_snapshot, &[]));
        if !self.dt_pre_lift_assertions.is_empty()
            && self.dt_pre_lift_assertions != assertions_snapshot
        {
            let pre_lift = self.dt_pre_lift_assertions.clone();
            extra_axioms.extend(self.dt_guarded_acyclicity_disjuncts(&pre_lift, &[]));
            extra_axioms.extend(self.dt_guarded_acyclicity_guard_units(&pre_lift, &[]));
        }
        // UF-bridge congruence stays EAGER (soundness pin: dn110 /
        // dt_uf_bridge_congruence / inc_some_list UNSAT preserved).
        extra_axioms.extend(self.dt_uf_bridge_congruence_axioms(&base_assertions));
        // The SPARSE on-demand relevance axioms (the L1a payload).
        let sparse = self.dt_auflia_lazy_relevant_axioms();
        let sparse_count = sparse.len();
        extra_axioms.extend(sparse);

        let base_assertions_exact = self.ctx.assertions.clone();
        let base_len = base_assertions_exact.len();
        self.ctx.assertions.extend(extra_axioms);

        if ay_core::misc_cli_flags().phase_trace {
            eprintln!(
                "c phase-trace dt-auflia-lazy-axioms base={base_len} sparse_relevance={sparse_count} depth_floor={depth} total_asserts={}",
                self.ctx.assertions.len()
            );
        }

        // Time split: the lazy attempt gets HALF the remaining budget so a lane
        // miss can at worst halve — never consume — the eager lane's time.
        let saved_deadline = self.solve_deadline.get();
        if let Some(deadline) = saved_deadline {
            let now = ay_core::time::Instant::now();
            if deadline <= now {
                rollback_on_fallback(self);
                return Ok(None);
            }
            self.solve_deadline.set(Some(now + (deadline - now) / 2));
        }
        // L2 eager-arm routing (`AY_DT_LAZY_AUFLIA_EAGER`, default off ⇒ this
        // whole block is inert and the lane is byte-identical to L1a): the
        // sparse on-demand DT axioms above make the residual EAGER-tractable, so
        // route the inner UF+LIA combiner solve through the eager split arm and
        // skip the UFLIA hybrid's non-converging lazy DETOUR (the measured 96s+
        // wall — see `dt_lazy_auflia_eager_arm`). Scoped strictly to this inner
        // solve: set immediately before, reset immediately after (there is no
        // early return between the two — `solve_fn` returns a captured Result).
        // If the eager arm returns Unknown the lane falls through to the eager
        // DT-axioms authority exactly as it does today, so nothing is lost.
        let eager_arm = std::env::var_os("AY_DT_LAZY_AUFLIA_EAGER").is_some_and(|v| v != "0");
        let saved_eager_arm = self.dt_lazy_auflia_eager_arm;
        if eager_arm {
            self.dt_lazy_auflia_eager_arm = true;
        }
        let result = solve_fn(self);
        self.dt_lazy_auflia_eager_arm = saved_eager_arm;
        self.solve_deadline.set(saved_deadline);
        self.ctx.assertions = base_assertions_exact;

        if ay_core::misc_cli_flags().phase_trace {
            eprintln!(
                "c phase-trace dt-auflia-lazy-lane result={:?} reason={:?}",
                result.as_ref().map(|r| format!("{r:?}")),
                self.last_unknown_reason
            );
        }
        // Relevance-miss backstop (#dt-lazy-refuted-fallback): a lane `Sat`
        // whose witness the independent fail-closed gate ground-refutes is
        // treated as a lane MISS (a missed relevance term left a class
        // under-constrained) → eager fallback, never a public wrong-SAT.
        let result = match result {
            Ok(SolveResult::Sat)
                if matches!(
                    self.confirm_sat_with_independent_gate(),
                    ay_model_check::GateVerdict::ModelViolates { .. }
                ) =>
            {
                if ay_core::misc_cli_flags().phase_trace {
                    eprintln!("c phase-trace dt-auflia-lazy-refuted-fallback");
                }
                self.last_model_validated = false;
                Ok(SolveResult::Unknown)
            }
            Ok(SolveResult::Sat) if self.dt_lazy_sat_would_print_partial() => {
                if ay_core::misc_cli_flags().phase_trace {
                    eprintln!("c phase-trace dt-auflia-lazy-partial-fallback");
                }
                self.last_model_validated = false;
                Ok(SolveResult::Unknown)
            }
            other => other,
        };
        match result {
            Ok(SolveResult::Unknown) => {
                rollback_on_fallback(self);
                Ok(None)
            }
            Err(error) => {
                // An internal solver error publishes no verdict, but callers
                // may keep and reuse the Executor. Preserve the same affine
                // isolation contract as an ordinary lane miss before
                // propagating the error.
                rollback_on_fallback(self);
                Err(error)
            }
            Ok(result) => Ok(Some(result)),
        }
    }

    /// Entry to the lazy DT+LIA lane with the incremental case clamped.
    ///
    /// Persistent solver maps make speculative TermStore recycling unsafe, and
    /// mandatory internal proof tracking means disabling user-facing proof
    /// output does not remove the proof's `TermId` dependencies. Incremental
    /// sessions therefore stay on the eager authority until this optimization
    /// can export a self-contained authored-scope proof without shrinking the
    /// term store.
    pub(in crate::executor) fn try_solve_dt_auflia_lazy_maybe_incremental(
        &mut self,
        solve_fn: fn(&mut Self) -> Result<SolveResult>,
    ) -> Result<Option<SolveResult>> {
        // Detect a live incremental session — the EXACT condition the in-lane
        // gate (`#dt-lazy-incremental-gate`) tests.
        let incremental = self.incremental_mode
            || self.incr_theory_state.as_ref().is_some_and(|s| {
                s.scope_depth > 0
                    || s.pending_push > 0
                    || !s.encoded_assertions.is_empty()
                    || !s.pre_push_assertions.is_empty()
                    || s.persistent_sat.is_some()
                    || s.lia_persistent_sat.is_some()
            });
        if !incremental {
            // Non-incremental: the original single-shot lane, unchanged path.
            return self.try_solve_dt_auflia_lazy(solve_fn);
        }
        // Fail closed: internal proof tracking is mandatory even when
        // user-facing proof output is disabled. The former optional oracle
        // rolled its TermStore back after accepting an inner UNSAT, leaving the
        // strict authored-scope proof with recycled TermIds. Suspending the
        // persistent SAT state does not solve that proof-translation problem.
        // Keep this incremental optimization clamped until it can return a
        // self-contained authored-scope proof without shrinking its term store.
        Ok(None)
    }

    /// Eligibility for the lazy DT+LIA lane: at least one declared datatype has
    /// a constructor with a datatype-sorted field (a genuinely recursive /
    /// nested datatype — the family the sparse reconstruction axioms address).
    fn dt_auflia_lazy_eligible(&self) -> bool {
        let dt_names: HashSet<&str> = self.ctx.datatype_iter().map(|(n, _)| n).collect();
        if dt_names.is_empty() {
            return false;
        }
        self.ctx
            .datatype_iter()
            .flat_map(|(_, cs)| cs.iter())
            .filter_map(|c| self.ctx.constructor_selector_info(c))
            .flatten()
            .any(|(_, fsort)| match fsort {
                Sort::Uninterpreted(n) => dt_names.contains(n.as_str()),
                Sort::Datatype(dt) => dt_names.contains(dt.name.as_str()),
                _ => false,
            })
    }

    /// Whether an exact AUFLIA rollback snapshot fits the active memory
    /// envelope.
    ///
    /// This is predictive rather than reactive: this lane clones the term
    /// store plus disjoint rollback ledgers. Require best-effort room for
    /// another observed process footprint as well as the TermStore's
    /// capacity-aware per-engine clone bound. Returning `false` only skips an
    /// optional speculative lane and leaves the eager solver authoritative.
    fn dt_auflia_snapshot_preflight(&self) -> bool {
        if self.external_stop_reason().is_some()
            || ay_core::TermStore::global_memory_exceeded()
            || !self.bulk_state_clone_fits_memory()
        {
            return false;
        }
        let clone_limit = ay_core::TermStore::per_engine_budget() / 2;
        self.ctx
            .terms
            .diagnostic_clone_memory_bytes(clone_limit)
            .is_some()
    }

    /// Materialize the SPARSE on-demand DT axioms at the occurrence-driven
    /// UNION-relevant datatype terms (campaign L1a; the z3-validated 4-shape
    /// family per relevant term). Returns the asserted axiom TermIds.
    ///
    /// For each relevant, NON-constructor, ground datatype term `t`:
    /// - exhaustiveness `(or (is-C1 t) ... (is-Ck t))` (k ≥ 2),
    /// - pairwise exclusivity `(or (not (is-Ci t)) (not (is-Cj t)))`,
    /// - per-constructor reconstruction
    ///   `(=> (is-C t) (= t (C (sel0 t) ... (seln t))))` (nullary: `(= t C)`).
    ///
    /// The term set is chosen by [`ay_dt::occurrence_relevant_dt_terms`] (the
    /// UNION criterion), NOT the eager depth-3 closure — O(tens) not O(1000s).
    fn dt_auflia_lazy_relevant_axioms(&mut self) -> Vec<TermId> {
        // --- Gather datatype metadata into owned form (before mutably
        //     borrowing the term store for construction). ---
        let dt_sort_names: HashSet<String> = self
            .ctx
            .datatype_iter()
            .map(|(n, _)| n.to_string())
            .collect();
        // (dt name, [(ctor name, [(selector name, field sort)])])
        let dt_meta: Vec<(String, Vec<(String, Vec<(String, Sort)>)>)> = self
            .ctx
            .datatype_iter()
            .map(|(n, ctors)| (n.to_string(), ctors.to_vec()))
            .collect::<Vec<_>>()
            .into_iter()
            .map(|(dt, ctors)| {
                let ctor_meta: Vec<(String, Vec<(String, Sort)>)> = ctors
                    .into_iter()
                    .map(|c| {
                        let sels = self
                            .ctx
                            .constructor_selector_info(&c)
                            .map(<[(String, Sort)]>::to_vec)
                            .unwrap_or_default();
                        (c, sels)
                    })
                    .collect();
                (dt, ctor_meta)
            })
            .collect();
        let ctor_names: HashSet<String> = dt_meta
            .iter()
            .flat_map(|(_, cs)| cs.iter().map(|(c, _)| c.clone()))
            .collect();
        let mut tester_names: HashSet<String> = HashSet::default();
        let mut selector_names: HashSet<String> = HashSet::default();
        for (_, ctors) in &dt_meta {
            for (c, sels) in ctors {
                tester_names.insert(format!("is-{c}"));
                for (s, _) in sels {
                    selector_names.insert(s.clone());
                }
            }
        }

        let relevant = ay_dt::occurrence_relevant_dt_terms(
            &self.ctx.terms,
            &self.ctx.assertions,
            &dt_sort_names,
            &tester_names,
            &selector_names,
        );

        let base: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut seen: HashSet<TermId> = HashSet::default();
        let mut axioms: Vec<TermId> = Vec::new();
        for t in relevant {
            // Skip constructor applications/constants (committed values — their
            // reconstruction is vacuous and exhaustiveness/exclusivity trivial).
            let is_ctor_term = match self.ctx.terms.get(t) {
                TermData::App(Symbol::Named(name), _) | TermData::Var(name, _) => {
                    ctor_names.contains(name)
                }
                _ => false,
            };
            if is_ctor_term {
                continue;
            }
            let t_sort = self.ctx.terms.sort(t).clone();
            let dt_name = match &t_sort {
                Sort::Uninterpreted(n) if dt_sort_names.contains(n) => n.clone(),
                Sort::Datatype(dt) if dt_sort_names.contains(&dt.name) => dt.name.clone(),
                _ => continue,
            };
            let Some((_, ctors)) = dt_meta.iter().find(|(n, _)| *n == dt_name) else {
                continue;
            };
            if ctors.is_empty() {
                continue;
            }
            // Tester applications for every constructor of t's sort.
            let testers: Vec<TermId> = ctors
                .iter()
                .map(|(c, _)| {
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(format!("is-{c}")), [t], Sort::Bool)
                })
                .collect();
            // Exhaustiveness + pairwise exclusivity (multi-constructor only).
            if testers.len() >= 2 {
                let exhaust = self.ctx.terms.mk_or(testers.clone());
                if !base.contains(&exhaust) && seen.insert(exhaust) {
                    axioms.push(exhaust);
                }
                for i in 0..testers.len() {
                    for j in (i + 1)..testers.len() {
                        let ni = self.ctx.terms.mk_not(testers[i]);
                        let nj = self.ctx.terms.mk_not(testers[j]);
                        let excl = self.ctx.terms.mk_or(vec![ni, nj]);
                        if !base.contains(&excl) && seen.insert(excl) {
                            axioms.push(excl);
                        }
                    }
                }
            }
            // Per-constructor reconstruction.
            for (ci, (c, sels)) in ctors.iter().enumerate() {
                let ctor_term = if sels.is_empty() {
                    self.ctx.terms.mk_var(c.clone(), t_sort.clone())
                } else {
                    let sel_apps: Vec<TermId> = sels
                        .iter()
                        .map(|(sname, fsort)| {
                            self.ctx
                                .terms
                                .mk_app(Symbol::named(sname), [t], fsort.clone())
                        })
                        .collect();
                    self.ctx
                        .terms
                        .mk_app(Symbol::named(c), sel_apps, t_sort.clone())
                };
                let eq = self.ctx.terms.mk_eq(t, ctor_term);
                let recon = self.ctx.terms.mk_implies(testers[ci], eq);
                if !base.contains(&recon) && seen.insert(recon) {
                    axioms.push(recon);
                }
            }
        }
        axioms
    }

    /// Solve combined DT + LIA when the problem is ARRAY-FREE (#chc25-dt-uflia):
    /// route the post-axiom residual through the UF+LIA combiner rather than the
    /// array-enabled `solve_auf_lia`. Enum/list/nat datatypes emit no array axioms,
    /// and `solve_with_dt_axioms` adds the SAME DT axioms either way, so this is a
    /// pure routing choice — but the array-enabled Nelson-Oppen combiner fails to
    /// share EUF-derived congruence equalities into the arithmetic theory for these
    /// (empirically: the tip-adt-lia catamorphism obligations over enum/list stall
    /// to Unknown at 20s through `solve_auf_lia` yet discharge fast through
    /// `solve_uf_lia`). Mirrors the existing `LogicCategory::Auflia` fast path
    /// (check_sat.rs) which already picks `solve_uf_lia` when array-free. Sound:
    /// `solve_uf_lia` is a sound (and, for this pattern, complete) decision
    /// procedure; a wrong routing can only degrade to Unknown, never a wrong verdict.
    pub(in crate::executor) fn solve_dt_uf_lia(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // L1a lazy-DT-AUFLIA on-demand route (array-free sibling; the actual
        // route the rusthorn List-sum VC gl.smt2 takes — it is array-free so
        // the DtAuflia dispatch tries `solve_dt_uf_lia` first). Flag OFF ⇒
        // byte-identical. See `solve_dt_auflia` / `try_solve_dt_auflia_lazy`.
        if std::env::var_os("AY_DT_LAZY_AUFLIA").is_some_and(|v| v != "0") {
            if let Some(result) =
                self.try_solve_dt_auflia_lazy_maybe_incremental(Self::solve_uf_lia)?
            {
                return Ok(result);
            }
        }
        self.solve_with_dt_axioms(Some(Sort::Int), Self::solve_uf_lia)
    }

    /// Solve combined DT + Seq + LIA by adding datatype axioms, then using the
    /// mixed Seq/AUFLIA route so live sequence terms are not discarded.
    pub(in crate::executor) fn solve_dt_seq_auflia(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        self.solve_with_dt_axioms(Some(Sort::Int), Self::solve_seq_auflia)
    }

    /// Solve combined DT + LRA (#1760). DT axioms + acyclicity(Real) → AUFLRA.
    pub(in crate::executor) fn solve_dt_auflra(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        self.solve_with_dt_axioms(Some(Sort::Real), Self::solve_auf_lra)
    }

    /// Solve combined DT + LIRA (#5402). DT axioms + acyclicity(Int) → AUFLIRA.
    pub(in crate::executor) fn solve_dt_auflira(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        self.solve_with_dt_axioms(Some(Sort::Int), Self::solve_auflira)
    }

    /// Solve combined DT + BV (#1766). DT axioms only (no acyclicity) → UFBV.
    pub(in crate::executor) fn solve_dt_ufbv(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        self.solve_with_dt_axioms(None, Self::solve_ufbv)
    }

    /// Solve combined DT + Arrays + BV (#1766). DT axioms only → AUFBV.
    pub(in crate::executor) fn solve_dt_aufbv(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        self.solve_with_dt_axioms(None, Self::solve_aufbv)
    }

    /// Solve combined DT + Arrays (#1766). DT axioms only → Array+EUF.
    pub(in crate::executor) fn solve_dt_ax(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // Enum finite-domain SAT lane (#enum-sat-lane): pure all-nullary-enum
        // (dis)equality problems (e.g. the Bouvier vlsat3 coloring family)
        // compile exactly to one-hot CNF and are decided by the SAT core in
        // seconds where the lazy combined lane needs millions of theory
        // callbacks. Strictly gated: any construct outside the fragment — and
        // any SAT model the always-on gates reject — falls through here.
        if let Some(result) = self.try_solve_enum_finite_domain()? {
            return Ok(result);
        }
        // Lazy DT lane (DESIGN_lazy_dt.md stages D1+D2, routing per R1):
        // pure DT(+UF) content skips the eager selector-depth unroll and
        // runs the raw Boolean skeleton with the in-loop D0/D1/D2 passes.
        // Definitive verdicts return here; Unknown (including the lane's
        // half-budget deadline) falls through to the eager lane unchanged.
        if let Some(result) = self.try_solve_dt_lazy()? {
            return Ok(result);
        }
        self.solve_with_dt_axioms(None, Self::solve_array_euf)
    }

    /// Lazy DT lane (stages D1+D2): solve pure-DT(+UF) content WITHOUT the
    /// eager selector-depth unroll.
    ///
    /// The eager DtAx encoding pre-instantiates selector/tester/
    /// exhaustiveness axiom families to iterative depth and hands a huge
    /// clause set to CDCL — on deep BMC instances (blocksworld) 99.9% of
    /// wall time is SAT-core grind over that encoding. This lane instead
    /// runs the ORIGINAL Boolean skeleton through the array_euf combiner
    /// pipeline, where datatype semantics live in the in-loop passes:
    ///
    /// - D0 (clash / ground structural disequality / cycle) fires verified
    ///   conflict tautologies at BCP quiescence and at the fixpoint;
    /// - D1 (tester evaluation, tester transfer, selector projection) fires
    ///   merge-driven propagation clauses — projection needs the equality
    ///   atom `(= sel(t) u_i)` to EXIST, so this method pre-materializes the
    ///   (selector-application × same-constructor-argument) atom pairs the
    ///   rules can ever propagate (bounded; see below);
    /// - D2 (splitting on demand) emits domain-closure clauses for enum
    ///   split bases at the fixpoint (completeness for finite sorts).
    ///
    /// Fail-closed frame: sat only through the always-on model gates; unsat
    /// only conflict-derived; `Unknown` — including budget/eligibility skips
    /// and the lane's half-remaining-time deadline (design R1: at worst a
    /// time split) — falls back to the eager lane with NO verdict influence.
    /// Kill switch: `AY_DT_LAZY=0`.
    ///
    /// ## The depth-1 syntactic axiom slice is load-bearing
    ///
    /// The lane asserts `dt_selector_axioms_to_depth(_, 1)` — the SYNTACTIC
    /// slice of the proven eager axiom families (selector evaluation,
    /// tester evaluation/exclusion/exhaustiveness, instantiate, injectivity
    /// on terms that appear in the formula) WITHOUT the iterative deepening
    /// that unrolls them to depth 64. The in-loop passes only cover DERIVED
    /// facts (post-merge), and the always-on model gates were measured to
    /// MISS a selector-semantics violation on an axiom-free candidate
    /// (`(= (rest ground-tower) other-ground-tower)` confirmed sat by the
    /// gates when nothing pinned `rest`): without this slice the lane
    /// produced a wrong SAT in testing. Depth override for A/B measurement:
    /// `AY_DT_LAZY_DEPTH` (default 1).
    ///
    /// Returns `Ok(Some(_))` only for a definitive Sat/Unsat.
    fn try_solve_dt_lazy(&mut self) -> Result<Option<SolveResult>> {
        if std::env::var_os("AY_DT_LAZY").is_some_and(|v| v == "0") {
            return Ok(None);
        }
        // INCREMENTAL GATE (#dt-lazy-incremental-gate — wrong-UNSAT fix):
        // the lane's fallback isolation (#dt-lazy-isolation) rolls the term
        // store back, and `TermStore::rollback_to`'s contract requires that
        // NO rolled-back TermId survive anywhere. Under an incremental
        // session that contract is unenforceable: the persistent
        // `IncrementalTheoryState` (encoded_assertions, tseitin term_to_var,
        // assertion_activation_scope, theory_atoms, scratch_var_to_term,
        // recorded theory lemmas) outlives the lane across check-sats, and —
        // because the inner solve routes to the PERSISTENT pipeline
        // (`solve_array_euf_incremental`) when incremental — even within one
        // query. After a rollback, later terms recycle the freed TermIds and
        // the stale persistent encodings alias them to unrelated SAT
        // literals: false conflicts, observed as a WRONG UNSAT on a
        // push/pop-wrapped satisfiable QF_DT query. The base line answered
        // sound-unknown on this route (the lane post-dates it), so skipping
        // the lane here loses nothing that ever worked. Covers explicit
        // push (`incremental_mode` set on Push and by
        // `note_api_assertion_mutation`) AND any session whose persistent
        // theory state already carries content.
        if self.incremental_mode
            || self.incr_theory_state.as_ref().is_some_and(|s| {
                s.scope_depth > 0
                    || s.pending_push > 0
                    || !s.encoded_assertions.is_empty()
                    || !s.pre_push_assertions.is_empty()
                    || s.persistent_sat.is_some()
                    || s.lia_persistent_sat.is_some()
            })
        {
            return Ok(None);
        }
        if !self.dt_lazy_lemma_cache_isolation_available() {
            return Ok(None);
        }
        if !self.dt_lazy_content_eligible() {
            return Ok(None);
        }
        // Apply predictive backpressure before cloning the rollback ledgers.
        // This optional lane leaves the eager authority unchanged on decline.
        if !self.bulk_state_clone_fits_memory() {
            return Ok(None);
        }
        let Ok(entry_proof_checkpoint) = self.bounded_proof_rollback_checkpoint() else {
            // Optional lane: fall through before mutating assertion/term state.
            return Ok(None);
        };

        // On FALLBACK restore assertions so the eager lane mines the ORIGINAL
        // shapes; its pre-lift snapshot must not see an already-lifted list or
        // the fuzz881 acyclicity units are lost. Unasserted appended terms are
        // harmless to every lane.
        let entry_assertions = self.ctx.assertions.clone();
        let entry_pre_lift = std::mem::take(&mut self.dt_pre_lift_assertions);
        // Entry TERM-STORE snapshot (#dt-lazy-isolation, mv-rerun-20260718
        // Barrett regression, merge 547590f8): every term this attempt
        // creates — the flatten/lift rewrites, the depth-1 axiom slice's
        // synthesized constructor/selector unfoldings, `dt_lazy_prepare`'s
        // projection / domain-closure atoms, and the inner solve's scratch
        // terms — is rolled back on FALLBACK, so the eager lane runs over
        // the exact store it would have seen had this lane never existed.
        // Without the rollback, main's store-scanning selector-axiom miner
        // and the combiner's D1 pass axiomatize/propagate over the leftover
        // unasserted scaffolding, flooding the eager SAT skeleton with
        // don't-care tester/selector atoms whose noisy assignments break
        // total-datatype-model construction and the single-source e-graph
        // assignment — the fail-closed z3-audit validation then degrades
        // genuinely-Sat eager models to unknown (166 Barrett QF_DT sats).
        // Sound: rollback happens only after every entry snapshot is
        // restored and the lane's model/caches (including a stale e-graph
        // export and the attempt's recorded variable substitutions) are
        // dropped, so no TermId above the watermark survives anywhere.
        //
        // PROOF-PRODUCTION INTERACTION (read this before touching): proof
        // steps and their assumption/lemma/name maps contain TermIds minted by
        // the attempt. The paired proof-tracker checkpoint is rolled back
        // BEFORE the TermStore checkpoint, removing the entire dependent
        // ledger (including speculative nested scopes). This keeps fallback
        // isolation active in both proof and non-proof modes without dangling
        // IDs or preserving failed-lane scaffolding.
        let entry_terms_len = self.ctx.terms.len();
        let entry_terms_checkpoint = self.ctx.terms.rollback_checkpoint();
        let entry_lazy_proof_state = lazy_proof_state::DtLazyProofState::capture(self);
        let entry_attempt_state = DtLazyAttemptState::capture(self);
        let entry_lia_probe_state = ay_lia::save_probe_state();
        // Every fallback callsite returns immediately. Make the transaction
        // affine so all entry snapshots are moved back rather than cloned
        // after the inner solve may have grown the corresponding structures.
        let rollback_on_fallback = move |this: &mut Self| {
            // #dt-lazy-isolation, repaired 2026-08-07.
            //
            // This guard used to skip the rollback whenever proof steps existed,
            // and its own comment recorded the precondition that made that safe:
            // "the SMT-COMP configuration (--z3-mode) never enables proofs and
            // always takes the rollback". 66538b006 made proof tracking
            // unconditional and silently voided it — the rollback stopped firing,
            // the failed lazy attempt's scaffold survived, and the pre-fix unknown
            // returned. Measured cost: 99 answers on MV QF_Datatypes, with SQ and
            // MV QF_Datatypes lost outright.
            //
            // The old guard existed because rolling terms back under recorded
            // proof steps dangles them. The proof-ledger checkpoint below now
            // removes those steps and every correlated ProofId map first, so
            // this lane can always restore its TermStore isolation contract.
            //
            // Note this is the try_solve_dt_lazy lane ONLY. The sibling
            // try_solve_dt_auflia_lazy guard above must stay — enabling it
            // regresses FP/BV/NRA (measured: 14 FP failures).
            // Revoke only the discarded attempt's result artifacts. The active
            // public UNSAT epoch and Pareto state belong to the enclosing query.
            this.ctx.assertions = entry_assertions;
            this.dt_pre_lift_assertions = entry_pre_lift;
            this.revoke_dt_lazy_attempt_artifacts();
            this.clear_dt_theory_model();
            this.dt_egraph_assignment.replace(None);
            let entry_array_ext_witness_cache = entry_attempt_state.restore(this);
            ay_lia::restore_probe_state(entry_lia_probe_state);
            crate::executor::model::eval_memo_clear();
            entry_lazy_proof_state.restore(this);
            this.clear_dt_lazy_rebuildable_term_indexes();
            if !this.proof_tracker.rollback_to(entry_proof_checkpoint) {
                // The checkpoint's prefix was moved out by a nested proof
                // reset/take. Keep the speculative terms so no escaped proof
                // can dangle; eager fallback remains sound, just less isolated.
                return;
            }
            this.array_ext_witness_cache = entry_array_ext_witness_cache;
            this.ctx.terms.rollback_to(entry_terms_checkpoint);
            this.clear_dt_lazy_rebuildable_term_indexes();
            if ay_core::misc_cli_flags().phase_trace {
                eprintln!("c phase-trace dt-lazy-rollback to={entry_terms_len}");
            }
        };

        // Preamble parity with `solve_with_dt_axioms` on the pieces the
        // depth-1 axiom scan depends on: flatten AND wrappers so asserted
        // equalities are visible (#7016) and lift non-Bool ITEs (#5082),
        // snapshotting the pre-lift assertions for the guarded-acyclicity
        // miners (fuzz881). Both rewrites are semantics-preserving and shared
        // with the eager fallback.
        let mut flatten = crate::preprocess::FlattenAnd::new();
        flatten.apply(&mut self.ctx.terms, &mut self.ctx.assertions);
        self.dt_pre_lift_assertions = self.ctx.assertions.clone();
        let lifted: Vec<TermId> = self.ctx.terms.lift_arithmetic_ite_all(&self.ctx.assertions);
        self.ctx.assertions = lifted;

        let occurs_check_assertions = self.ctx.assertions.clone();
        if self.dt_occurs_check_unsat_from_equalities(&occurs_check_assertions, &[]) {
            self.last_unknown_reason = None;
            return Ok(Some(SolveResult::unsat()));
        }

        // Depth-1 syntactic axiom slice + guarded acyclicity mining (both
        // entailed datatype tautology families; see method docs).
        // B10: depth pinned at 1 (the AY_DT_LAZY_DEPTH override nothing set
        // is retired).
        let depth: usize = 1;
        let base_assertions: HashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let mut extra_axioms = self.dt_selector_axioms_to_depth(&base_assertions, depth);
        let assertions_snapshot = self.ctx.assertions.clone();
        extra_axioms.extend(self.dt_guarded_acyclicity_disjuncts(&assertions_snapshot, &[]));
        extra_axioms.extend(self.dt_guarded_acyclicity_guard_units(&assertions_snapshot, &[]));
        if !self.dt_pre_lift_assertions.is_empty()
            && self.dt_pre_lift_assertions != assertions_snapshot
        {
            let pre_lift = self.dt_pre_lift_assertions.clone();
            extra_axioms.extend(self.dt_guarded_acyclicity_disjuncts(&pre_lift, &[]));
            extra_axioms.extend(self.dt_guarded_acyclicity_guard_units(&pre_lift, &[]));
        }
        let base_assertions_exact = self.ctx.assertions.clone();
        self.ctx.assertions.extend(extra_axioms);

        // Materialize the lane's atom families AFTER axiom generation so the
        // projection pairing also covers axiom-synthesized selector/ctor
        // terms.
        let Some((dt_registry, bases)) = self.dt_lazy_prepare() else {
            rollback_on_fallback(self);
            return Ok(None);
        };

        // R1 time split: the lazy attempt gets HALF the remaining budget so
        // a lane miss can at worst halve — never consume — the eager lane's
        // time. No wall deadline (library/CLI use without timeout): the lane
        // runs to verdict; the kill switch remains available.
        let saved_deadline = self.solve_deadline.get();
        if let Some(deadline) = saved_deadline {
            let now = ay_core::time::Instant::now();
            if deadline <= now {
                rollback_on_fallback(self);
                return Ok(None);
            }
            self.solve_deadline.set(Some(now + (deadline - now) / 2));
        }
        self.dt_lazy_splits = Some((dt_registry, bases));
        let result = self.solve_array_euf();
        self.dt_lazy_splits = None;
        self.solve_deadline.set(saved_deadline);
        self.ctx.assertions = base_assertions_exact;

        if ay_core::misc_cli_flags().phase_trace {
            eprintln!(
                "c phase-trace dt-lazy-lane result={:?} reason={:?}",
                result.as_ref().map(|r| format!("{r:?}")),
                self.last_unknown_reason
            );
        }
        // Refuted-witness fallback (#dt-lazy-refuted-fallback): a lane `Sat`
        // whose stored witness the INDEPENDENT, fail-closed gate ground-
        // REFUTES (`ModelViolates`) can never survive the emit funnel — the
        // #sat-chokepoint would fail-close it to a public Unknown anyway
        // (observed on the lazy lane's free-slack collisions: in-loop
        // validation passes on the model's own evaluator, the gate then
        // refutes an asserted distinctness). Treat it as a lane MISS instead:
        // full entry restore + store rollback, and the eager lane — which
        // solves these instances outright — gets its clean shot. Strictly
        // sound: only a gate-refuted Sat is demoted (the same evidence class
        // the deepening loop's #dt-deepen-refuted-witness backstop acts on),
        // and the public verdict can only improve (Unknown -> the eager
        // lane's gate-confirmed answer).
        let result = match result {
            Ok(SolveResult::Sat)
                if matches!(
                    self.confirm_sat_with_independent_gate(),
                    ay_model_check::GateVerdict::ModelViolates { .. }
                ) =>
            {
                if ay_core::misc_cli_flags().phase_trace {
                    eprintln!("c phase-trace dt-lazy-refuted-fallback");
                }
                self.last_model_validated = false;
                Ok(SolveResult::Unknown)
            }
            // Partial-emission fallback (#dt-lazy-partial-fallback): the lane's
            // model would print WITHOUT a definition for a user-declared
            // datatype constant (its class was poisoned by the single-source
            // assignment's failed self-check — the printer's fail-closed
            // omission, stage-4 review F2). A partial model scores zero to a
            // model validator, while the eager lane typically produces a
            // complete gate-confirmed witness for the same instance — a lane
            // miss is strictly better. Only the completeness CHECK is new;
            // the values themselves are untouched.
            Ok(SolveResult::Sat) if self.dt_lazy_sat_would_print_partial() => {
                if ay_core::misc_cli_flags().phase_trace {
                    eprintln!("c phase-trace dt-lazy-partial-fallback");
                }
                self.last_model_validated = false;
                Ok(SolveResult::Unknown)
            }
            other => other,
        };
        match result {
            Ok(SolveResult::Unknown) => {
                // Fallback: hand the eager lane the ORIGINAL assertion shapes
                // AND the original term store (see entry snapshots above,
                // #dt-lazy-isolation).
                rollback_on_fallback(self);
                Ok(None)
            }
            other => other.map(Some),
        }
    }

    /// Whether the lazy lane's stored `Sat` model would print WITHOUT a
    /// definition for some user-declared datatype-sorted constant — i.e. the
    /// single-source assignment has no value for its class AND the class is
    /// poisoned, which is exactly the printer's fail-closed omission
    /// condition (output.rs, stage-4 review F2). Used to demote such a lane
    /// `Sat` to a lane miss (#dt-lazy-partial-fallback).
    fn dt_lazy_sat_would_print_partial(&self) -> bool {
        let Some(model) = self.last_model.as_ref() else {
            return false;
        };
        for (name, info) in self.ctx.symbol_iter() {
            if !info.arg_sorts.is_empty()
                || self.is_exact_dt_internal_symbol(self.ctx.symbol_identity_name(name, info))
            {
                continue;
            }
            let Some(term_id) = info.term else {
                continue;
            };
            if self.datatype_sort_name(&info.sort).is_none() {
                continue;
            }
            if self.dt_egraph_value(model, term_id).is_none()
                && self.dt_egraph_class_poisoned(model, term_id)
            {
                return true;
            }
        }
        false
    }

    /// Lazy-lane content gate: every term sort must be Bool, an
    /// uninterpreted sort, or a datatype sort, and at least one datatype
    /// must be declared. Arithmetic/BV/array/string/float/seq content keeps
    /// the eager lane (design R1/R6: the eager bridge axiom families encode
    /// cross-theory entailments the lazy passes do not cover).
    fn dt_lazy_content_eligible(&self) -> bool {
        if self.ctx.datatype_iter().next().is_none() {
            return false;
        }
        for raw in 0..self.ctx.terms.len() {
            let tid = TermId(raw as u32);
            match self.ctx.terms.sort(tid) {
                Sort::Bool | Sort::Uninterpreted(_) | Sort::Datatype(_) => {}
                _ => return false,
            }
            // Quantified content never takes this lane (QF routing should
            // exclude it already; defensive).
            if matches!(
                self.ctx.terms.get(tid),
                TermData::Forall(..) | TermData::Exists(..)
            ) {
                return false;
            }
        }
        true
    }

    /// Materialize the lazy lane's atom families and split registry.
    ///
    /// Creates (as terms; nothing is asserted):
    /// - projection equality atoms `(= sel_i^C(t) u_i)` for every syntactic
    ///   selector application and every same-constructor application
    ///   argument of matching sort — the atoms D1's selector-projection rule
    ///   propagates over (it never creates terms itself);
    /// - domain-closure atom families `(= t Cj)` for every term of an
    ///   all-nullary (enum) datatype sort — the D2 split bases.
    ///
    /// Returns `None` (lane skipped, eager fallback) when the atom budget
    /// would be exceeded; the store then carries only already-created atoms,
    /// which are unasserted and harmless to every other lane.
    #[allow(clippy::type_complexity)]
    fn dt_lazy_prepare(
        &mut self,
    ) -> Option<(Vec<(String, Vec<String>, bool)>, Vec<(TermId, Vec<TermId>)>)> {
        /// Hard cap on materialized atoms (projection + domain closure).
        const DT_LAZY_MAX_ATOMS: usize = 150_000;

        // --- Registry ------------------------------------------------------
        let dt_registry: Vec<(String, Vec<String>, bool)> = self
            .ctx
            .datatype_iter()
            .map(|(name, ctors)| {
                let all_nullary = ctors.iter().all(|c| {
                    self.ctx
                        .constructor_selectors(c)
                        .is_none_or(|sels| sels.is_empty())
                });
                (name.to_owned(), ctors.to_vec(), all_nullary)
            })
            .collect();
        let enum_dts: HashSet<String> = dt_registry
            .iter()
            .filter(|(_, _, all_nullary)| *all_nullary)
            .map(|(name, _, _)| name.clone())
            .collect();
        let dt_names: HashSet<String> = dt_registry
            .iter()
            .map(|(name, _, _)| name.clone())
            .collect();
        // Selector name -> (constructor name, argument position).
        let mut sel_defs: std::collections::HashMap<String, (String, usize)> =
            std::collections::HashMap::new();
        for (_, ctors, _) in &dt_registry {
            for ctor in ctors {
                if let Some(sels) = self.ctx.constructor_selectors(ctor) {
                    for (pos, sel) in sels.iter().enumerate() {
                        sel_defs
                            .entry(sel.clone())
                            .or_insert_with(|| (ctor.clone(), pos));
                    }
                }
            }
        }

        let dt_sort_name = |sort: &Sort| -> Option<String> {
            match sort {
                Sort::Uninterpreted(n) => Some(n.clone()),
                Sort::Datatype(dt) => Some(dt.name.clone()),
                _ => None,
            }
        };

        // --- Scan (immutable) ----------------------------------------------
        // Selector applications: (sel_app, ctor name, arg position).
        let mut sel_apps: Vec<(TermId, String, usize)> = Vec::new();
        // Constructor applications by constructor name: (app, args).
        let mut ctor_apps: std::collections::HashMap<String, Vec<(TermId, Vec<TermId>)>> =
            std::collections::HashMap::new();
        // Enum split-base candidates: (term, enum dt name).
        let mut enum_bases: Vec<(TermId, String)> = Vec::new();
        // Enum constructor constants: (dt name, ctor name) -> (term, sort).
        let mut enum_consts: std::collections::HashMap<(String, String), TermId> =
            std::collections::HashMap::new();
        // One observed sort per enum dt (to build missing constants).
        let mut enum_sorts: std::collections::HashMap<String, Sort> =
            std::collections::HashMap::new();

        let term_len = self.ctx.terms.len();
        for raw in 0..term_len {
            let tid = TermId(raw as u32);
            let sort = self.ctx.terms.sort(tid);
            let tid_dt = dt_sort_name(sort).filter(|n| dt_names.contains(n.as_str()));
            let mut is_ctor_term = false;
            match self.ctx.terms.get(tid) {
                TermData::App(Symbol::Named(name), args) => {
                    if self.ctx.is_constructor(name).is_some() {
                        is_ctor_term = true;
                        ctor_apps
                            .entry(name.clone())
                            .or_default()
                            .push((tid, args.clone()));
                    } else if args.len() == 1 {
                        if let Some((ctor, pos)) = sel_defs.get(name.as_str()) {
                            sel_apps.push((tid, ctor.clone(), *pos));
                        }
                    }
                }
                TermData::Var(name, _) => {
                    if let Some((dt, ctor)) = self.ctx.is_constructor(name) {
                        is_ctor_term = true;
                        if let Some(n) = &tid_dt {
                            enum_consts.insert((n.clone(), ctor), tid);
                        } else {
                            enum_consts.insert((dt, ctor), tid);
                        }
                    }
                }
                _ => {}
            }
            if let Some(n) = tid_dt {
                if enum_dts.contains(n.as_str()) {
                    enum_sorts.entry(n.clone()).or_insert_with(|| sort.clone());
                    if !is_ctor_term {
                        enum_bases.push((tid, n));
                    }
                }
            }
        }

        // --- Budget (computed before any creation) --------------------------
        let ctors_of = |dt: &str| -> usize {
            dt_registry
                .iter()
                .find(|(name, _, _)| name == dt)
                .map_or(0, |(_, ctors, _)| ctors.len())
        };
        let projection_atoms: usize = sel_apps
            .iter()
            .map(|(_, ctor, _)| ctor_apps.get(ctor).map_or(0, Vec::len))
            .sum();
        let closure_atoms: usize = enum_bases.iter().map(|(_, dt)| ctors_of(dt)).sum();
        if projection_atoms + closure_atoms > DT_LAZY_MAX_ATOMS {
            if ay_core::misc_cli_flags().phase_trace {
                eprintln!(
                    "c phase-trace dt-lazy-skip projection_atoms={projection_atoms} closure_atoms={closure_atoms}"
                );
            }
            return None;
        }

        // --- Materialize projection atoms -----------------------------------
        for (sel_app, ctor, pos) in &sel_apps {
            let Some(apps) = ctor_apps.get(ctor) else {
                continue;
            };
            let sel_sort = self.ctx.terms.sort(*sel_app).clone();
            for (_, args) in apps {
                let Some(&field) = args.get(*pos) else {
                    continue;
                };
                if field == *sel_app || self.ctx.terms.sort(field) != &sel_sort {
                    continue;
                }
                let _ = self.ctx.terms.mk_eq(*sel_app, field);
            }
        }

        // --- Materialize split bases -----------------------------------------
        let mut bases: Vec<(TermId, Vec<TermId>)> = Vec::new();
        for (t, dt) in &enum_bases {
            let Some(sort) = enum_sorts.get(dt) else {
                continue;
            };
            let ctors: Vec<String> = dt_registry
                .iter()
                .find(|(name, _, _)| name == dt)
                .map(|(_, ctors, _)| ctors.clone())
                .unwrap_or_default();
            if ctors.is_empty() {
                continue;
            }
            let mut atoms: Vec<TermId> = Vec::with_capacity(ctors.len());
            for ctor in &ctors {
                let const_tid = *enum_consts
                    .entry((dt.clone(), ctor.clone()))
                    .or_insert_with(|| self.ctx.terms.mk_var(ctor.clone(), sort.clone()));
                atoms.push(self.ctx.terms.mk_eq(*t, const_tid));
            }
            bases.push((*t, atoms));
        }

        if ay_core::misc_cli_flags().phase_trace {
            eprintln!(
                "c phase-trace dt-lazy-prepare sel_apps={} projection_atoms={} bases={} closure_atoms={}",
                sel_apps.len(),
                projection_atoms,
                bases.len(),
                closure_atoms,
            );
        }
        Some((dt_registry, bases))
    }
}

#[cfg(test)]
mod rollback_artifact_tests {
    use ay_core::Proof;

    use super::*;
    use crate::executor::optimization::ParetoState;

    #[test]
    fn lazy_lane_cache_gate_excludes_persistence_and_existing_entries() {
        let mut executor = Executor::new();
        assert!(executor.dt_lazy_lemma_cache_isolation_available());

        executor.lemma_persistence = true;
        assert!(!executor.dt_lazy_lemma_cache_isolation_available());
        executor.lemma_persistence = false;

        let lemma = ay_core::TheoryLemma::new(vec![TheoryLit::new(TermId(5), true)]);
        assert!(executor.lemma_cache.record_lemma(lemma, 0));
        assert!(!executor.dt_lazy_lemma_cache_isolation_available());
    }

    #[test]
    fn auflia_fallback_moves_the_exact_entry_term_store() {
        let mut executor = Executor::new();
        let entry_terms = executor.ctx.terms.clone();
        let entry_len = entry_terms.len();
        let entry_stamp = entry_terms.snapshot_stamp();
        let entry_checkpoint = entry_terms.rollback_checkpoint();

        let scratch = executor
            .ctx
            .terms
            .mk_var("__test_dt_auflia_speculative", Sort::Int);
        assert!(scratch.index() >= entry_len);

        restore_dt_auflia_entry_terms(&mut executor.ctx.terms, entry_terms);

        assert_eq!(executor.ctx.terms.len(), entry_len);
        assert_eq!(executor.ctx.terms.snapshot_stamp(), entry_stamp);
        // The opaque checkpoint is bound to the saved store's physical
        // identity. This succeeds only because fallback moved that exact store;
        // a clone at restore time would panic as a foreign universe.
        executor.ctx.terms.rollback_to(entry_checkpoint);
    }

    #[test]
    fn discarded_lazy_attempt_preserves_enclosing_query_authority() {
        let mut executor = Executor::new();
        executor.begin_unsat_query_epoch(&[]);
        executor.pareto_state = Some(ParetoState::default());
        executor.last_assumptions = Some(vec![TermId(7)]);
        executor.last_core_term_to_name = Some(Default::default());
        executor.last_result = Some(SolveResult::Sat);
        executor.last_proof = Some(Proof::new());
        executor.last_model_validated = true;
        executor.dt_cert_grant_active = true;
        executor.finite_table_cert_grant_active = true;
        executor.const_interp_cert_grant_active = true;
        executor.bv_quantifier_full_domain_proof = true;

        executor.revoke_dt_lazy_attempt_artifacts();

        assert!(executor.active_unsat_query_requires_strict_proof());
        assert!(executor.pareto_state.is_some());
        assert_eq!(executor.last_assumptions, Some(vec![TermId(7)]));
        assert!(executor.last_core_term_to_name.is_some());
        assert!(executor.last_result.is_none());
        assert!(executor.last_proof.is_none());
        assert!(!executor.last_model_validated);
        assert!(!executor.dt_cert_grant_active);
        assert!(!executor.finite_table_cert_grant_active);
        assert!(!executor.const_interp_cert_grant_active);
        assert!(!executor.bv_quantifier_full_domain_proof);
    }

    #[test]
    fn discarded_lazy_attempt_clears_every_rebuildable_term_index() {
        let mut executor = Executor::new();
        let term = executor.ctx.terms.true_term();
        executor
            .cached_store_eqs
            .push((term, term, term, term, term));
        executor.store_eq_scan_hwm = 17;
        executor
            .cached_select_indices_by_array
            .insert(term, vec![term]);
        executor.select_index_scan_hwm = 19;
        {
            let mut index = executor.select_by_array_index.borrow_mut();
            index.0 = 23;
            index.1.insert(term, vec![term]);
        }
        let mut required = HashSet::default();
        required.insert(term);
        *executor.required_terms_index.borrow_mut() =
            Some((vec![term], Some(vec![term]), required));

        executor.clear_dt_lazy_rebuildable_term_indexes();

        assert!(executor.cached_store_eqs.is_empty());
        assert_eq!(executor.store_eq_scan_hwm, 0);
        assert!(executor.cached_select_indices_by_array.is_empty());
        assert_eq!(executor.select_index_scan_hwm, 0);
        let select_index = executor.select_by_array_index.borrow();
        assert_eq!(select_index.0, 0);
        assert!(select_index.1.is_empty());
        assert!(executor.array_def_index.borrow().is_none());
        assert!(executor.required_terms_index.borrow().is_none());
    }

    #[test]
    fn discarded_lazy_attempt_restores_validation_and_retry_state() {
        let mut executor = Executor::new();
        executor
            .recorded_var_substitutions
            .insert(TermId(1), TermId(2));
        executor
            .array_default_epsilon_by_sort
            .insert(Sort::Int, TermId(3));
        executor
            .array_default_diag_by_sort
            .insert(Sort::Bool, "entry-diag".to_string());
        executor.qfax_refinement_clause = Some(vec![(TermId(7), true)]);
        executor.last_rejected_array_assertion = Some(TermId(8));
        executor.cegar_pending_lemma = Some(TermId(9));
        executor.qfax_retry_done = true;
        executor.uflia_congruence_retry_done = true;
        executor.uflia_model_repair_done = true;
        executor.sat_validated_by_mod_div_or_branch = true;
        executor.defer_model_validation = true;
        executor.skip_model_eval = true;
        executor.read_pin_repair_done = true;
        executor.dt_array_injectivity_gate_bypass = true;
        executor.original_problem_had_quantifiers = true;
        executor.in_nested_array_residue_probe = true;
        executor.residue_probe_failures = 7;
        executor.mod_div_or_branch_rescue_depth = 2;
        executor.last_degrade_was_datatype_array = true;
        executor.nested_array_row_reduction_unsat = true;
        executor.uflia_congruence_lane = true;
        executor.uflia_congruence_gate_rejected = true;
        let entry = DtLazyAttemptState::capture(&executor);

        executor.recorded_var_substitutions.clear();
        executor.array_default_epsilon_by_sort.clear();
        executor.array_default_diag_by_sort.clear();
        executor.qfax_refinement_clause = None;
        executor.last_rejected_array_assertion = None;
        executor.cegar_pending_lemma = None;
        executor.qfax_retry_done = false;
        executor.uflia_congruence_retry_done = false;
        executor.uflia_model_repair_done = false;
        executor.sat_validated_by_mod_div_or_branch = false;
        executor.defer_model_validation = false;
        executor.skip_model_eval = false;
        executor.read_pin_repair_done = false;
        executor.dt_array_injectivity_gate_bypass = false;
        executor.original_problem_had_quantifiers = false;
        executor.in_nested_array_residue_probe = false;
        executor.residue_probe_failures = 0;
        executor.mod_div_or_branch_rescue_depth = 0;
        executor.last_degrade_was_datatype_array = false;
        executor.nested_array_row_reduction_unsat = false;
        executor.uflia_congruence_lane = false;
        executor.uflia_congruence_gate_rejected = false;

        let _entry_witness_cache = entry.restore(&mut executor);

        assert_eq!(
            executor.recorded_var_substitutions.get(&TermId(1)),
            Some(&TermId(2))
        );
        assert_eq!(
            executor.array_default_epsilon_by_sort.get(&Sort::Int),
            Some(&TermId(3))
        );
        assert_eq!(
            executor
                .array_default_diag_by_sort
                .get(&Sort::Bool)
                .map(String::as_str),
            Some("entry-diag")
        );
        assert_eq!(
            executor.qfax_refinement_clause,
            Some(vec![(TermId(7), true)])
        );
        assert_eq!(executor.last_rejected_array_assertion, Some(TermId(8)));
        assert_eq!(executor.cegar_pending_lemma, Some(TermId(9)));
        assert!(executor.qfax_retry_done);
        assert!(executor.uflia_congruence_retry_done);
        assert!(executor.uflia_model_repair_done);
        assert!(executor.sat_validated_by_mod_div_or_branch);
        assert!(executor.defer_model_validation);
        assert!(executor.skip_model_eval);
        assert!(executor.read_pin_repair_done);
        assert!(executor.dt_array_injectivity_gate_bypass);
        assert!(executor.original_problem_had_quantifiers);
        assert!(executor.in_nested_array_residue_probe);
        assert_eq!(executor.residue_probe_failures, 7);
        assert_eq!(executor.mod_div_or_branch_rescue_depth, 2);
        assert!(executor.last_degrade_was_datatype_array);
        assert!(executor.nested_array_row_reduction_unsat);
        assert!(executor.uflia_congruence_lane);
        assert!(executor.uflia_congruence_gate_rejected);
    }

    #[test]
    fn discarded_lazy_attempt_restores_witness_cache_in_second_phase() {
        let mut executor = Executor::new();
        let array_sort = Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Int)));
        let entry_lhs = executor
            .ctx
            .terms
            .mk_var("__test_dt_lazy_entry_lhs", array_sort.clone());
        let entry_rhs = executor
            .ctx
            .terms
            .mk_var("__test_dt_lazy_entry_rhs", array_sort.clone());
        let entry_witness = crate::executor::theories::array_extensionality_witness(
            &mut executor.ctx.terms,
            &mut executor.array_ext_witness_cache,
            entry_lhs,
            entry_rhs,
        )
        .expect("entry array pair should mint a witness");
        let entry = DtLazyAttemptState::capture(&executor);

        let speculative_lhs = executor
            .ctx
            .terms
            .mk_var("__test_dt_lazy_speculative_lhs", array_sort.clone());
        let speculative_rhs = executor
            .ctx
            .terms
            .mk_var("__test_dt_lazy_speculative_rhs", array_sort);
        let speculative_witness = crate::executor::theories::array_extensionality_witness(
            &mut executor.ctx.terms,
            &mut executor.array_ext_witness_cache,
            speculative_lhs,
            speculative_rhs,
        )
        .expect("speculative array pair should mint a witness");

        let entry_witness_cache = entry.restore(&mut executor);
        assert_eq!(
            executor.array_ext_witness_cache.pair_witness(
                &executor.ctx.terms,
                speculative_lhs,
                speculative_rhs,
            ),
            Some(speculative_witness),
            "ordinary attempt-state restore must leave proof-coupled cache entries in place"
        );

        executor.array_ext_witness_cache = entry_witness_cache;
        assert_eq!(
            executor.array_ext_witness_cache.pair_witness(
                &executor.ctx.terms,
                entry_lhs,
                entry_rhs,
            ),
            Some(entry_witness)
        );
        assert_eq!(
            executor.array_ext_witness_cache.pair_witness(
                &executor.ctx.terms,
                speculative_lhs,
                speculative_rhs,
            ),
            None,
            "second-phase restore must discard speculative witness provenance"
        );
    }

    #[test]
    fn incremental_lazy_auflia_oracle_is_clamped_with_mandatory_proofs() {
        fn must_not_run(_: &mut Executor) -> Result<SolveResult> {
            panic!("clamped incremental lane called its speculative solver")
        }

        let mut executor = Executor::new();
        executor.incremental_mode = true;
        executor.proof_tracker.enable();

        let result = executor
            .try_solve_dt_auflia_lazy_maybe_incremental(must_not_run)
            .expect("clamped lane cannot fail");

        assert!(result.is_none());
    }
}

#[cfg(test)]
mod dt_axiom_attribution_tests {
    use ay_core::ProofStep;
    use ay_frontend::parse;

    use super::*;

    /// C1.iv/C5 retag pass: `record_dt_axiom_theory_lemmas` must tag exactly
    /// the shapes the ay-proof validators accept (selector projection ->
    /// `DatatypeSelectorProject`, constructor coverage ->
    /// `DatatypeExhaustive`, guarded reconstruction ->
    /// `DatatypeConstructorReconstruct`, tester evaluation ->
    /// `DatatypeTesterEval`) and keep every declined shape `Generic` —
    /// classifier equals validator, decline-only.
    #[test]
    fn dt_axiom_recording_tags_validator_accepted_families_only() {
        let mut exec = Executor::new();
        let commands = parse(
            r#"
            (set-logic QF_DT)
            (declare-datatype Pair ((mk (first Int) (second Int)) (unit)))
            (declare-const p Pair)
            "#,
        )
        .expect("datatype declarations parse");
        exec.execute_all(&commands).expect("declarations execute");
        exec.proof_tracker.enable();

        let p = exec.ctx.terms.lookup("p").expect("p is declared");
        let pair_sort = exec.ctx.terms.sort(p).clone();
        let one = exec.ctx.terms.mk_int(1.into());
        let two = exec.ctx.terms.mk_int(2.into());
        let mk_pair = exec
            .ctx
            .terms
            .mk_app(Symbol::named("mk"), vec![one, two], pair_sort.clone());

        // Family (A): `(= (first (mk 1 2)) 1)` -> DatatypeSelectorProject.
        let first_app = exec
            .ctx
            .terms
            .mk_app(Symbol::named("first"), vec![mk_pair], Sort::Int);
        let selector_axiom = exec.ctx.terms.mk_eq(first_app, one);

        // Family (B) positive: `(is-mk (mk 1 2))` (the emitted `= .. true`
        // folds to this at mk_eq) -> DatatypeTesterEval.
        let tester_pos = exec
            .ctx
            .terms
            .mk_app(Symbol::named("is-mk"), vec![mk_pair], Sort::Bool);

        // Family (B) negative: `(not (is-unit (mk 1 2)))` -> DatatypeTesterEval.
        let tester_unit =
            exec.ctx
                .terms
                .mk_app(Symbol::named("is-unit"), vec![mk_pair], Sort::Bool);
        let tester_neg = exec.ctx.terms.mk_not(tester_unit);

        // Family (D): constructor coverage over one scrutinee — since C5 this
        // carries its own DatatypeExhaustive kind (probed before the tester
        // lane, whose general exhaustiveness branch also accepts it; the move
        // is between two strict-checkable kinds).
        let is_mk_p = exec
            .ctx
            .terms
            .mk_app(Symbol::named("is-mk"), vec![p], Sort::Bool);
        let is_unit_p = exec
            .ctx
            .terms
            .mk_app(Symbol::named("is-unit"), vec![p], Sort::Bool);
        let exhaustive = exec.ctx.terms.mk_or(vec![is_mk_p, is_unit_p]);

        // Family (C): the guarded reconstructions the eager pass emits via
        // `mk_implies` -> DatatypeConstructorReconstruct (C5). Non-nullary
        // `mk` rebuilds from its full selector chain; registry-nullary `unit`
        // rebuilds as the bare constant (`mk_var`, exactly as the emitter
        // interns it).
        let first_p = exec
            .ctx
            .terms
            .mk_app(Symbol::named("first"), vec![p], Sort::Int);
        let second_p = exec
            .ctx
            .terms
            .mk_app(Symbol::named("second"), vec![p], Sort::Int);
        let rebuilt_p = exec.ctx.terms.mk_app(
            Symbol::named("mk"),
            vec![first_p, second_p],
            pair_sort.clone(),
        );
        let p_eq_rebuilt = exec.ctx.terms.mk_eq(p, rebuilt_p);
        let reconstruct_mk = exec.ctx.terms.mk_implies(is_mk_p, p_eq_rebuilt);
        let unit_const = exec.ctx.terms.mk_var("unit".to_string(), pair_sort);
        let p_eq_unit = exec.ctx.terms.mk_eq(p, unit_const);
        let reconstruct_unit = exec.ctx.terms.mk_implies(is_unit_p, p_eq_unit);

        // No validator accepts this (acyclicity-disjunct/bridge residue
        // stand-in): `(not (= p (mk 1 2)))` must stay Generic.
        let p_eq_ctor = exec.ctx.terms.mk_eq(p, mk_pair);
        let generic_residue = exec.ctx.terms.mk_not(p_eq_ctor);

        let axioms = [
            selector_axiom,
            tester_pos,
            tester_neg,
            exhaustive,
            reconstruct_mk,
            reconstruct_unit,
            generic_residue,
        ];
        exec.record_dt_axiom_theory_lemmas(&axioms);
        let proof = exec.proof_tracker.take_proof();

        let expected = [
            (selector_axiom, TheoryLemmaKind::DatatypeSelectorProject),
            (tester_pos, TheoryLemmaKind::DatatypeTesterEval),
            (tester_neg, TheoryLemmaKind::DatatypeTesterEval),
            (exhaustive, TheoryLemmaKind::DatatypeExhaustive),
            (
                reconstruct_mk,
                TheoryLemmaKind::DatatypeConstructorReconstruct,
            ),
            (
                reconstruct_unit,
                TheoryLemmaKind::DatatypeConstructorReconstruct,
            ),
            (generic_residue, TheoryLemmaKind::Generic),
        ];
        assert_eq!(proof.steps.len(), expected.len());
        for (step, (axiom, expected_kind)) in proof.steps.iter().zip(expected) {
            match step {
                ProofStep::TheoryLemma { kind, clause, .. } => {
                    assert_eq!(clause, &vec![axiom]);
                    assert_eq!(*kind, expected_kind, "wrong kind for clause {clause:?}");
                }
                other => panic!("expected theory lemma, got {other:?}"),
            }
        }

        // Classifier == validator: every typed step must re-validate against
        // the SAME registries the mint-time strict check receives.
        let decls = exec.datatype_decls_for_strict_proof();
        let selectors = exec.ctor_selector_decls_for_strict_proof();
        assert!(ay_proof::recognize_datatype_selector_project(
            &exec.ctx.terms,
            &[selector_axiom],
            &selectors,
        ));
        for tester in [tester_pos, tester_neg] {
            assert!(ay_proof::recognize_datatype_tester_eval_with_selectors(
                &exec.ctx.terms,
                &[tester],
                &decls,
                &selectors,
            ));
        }
        assert!(ay_proof::recognize_datatype_exhaustive(
            &exec.ctx.terms,
            &[exhaustive],
            &decls,
        ));
        for reconstruction in [reconstruct_mk, reconstruct_unit] {
            assert!(ay_proof::recognize_datatype_constructor_reconstruct(
                &exec.ctx.terms,
                &[reconstruction],
                &decls,
                &selectors,
            ));
        }
    }

    /// Fail-closed regression: DT axiom families without an enabled promotion
    /// lane must remain explicit `Generic` trust, including value-equality
    /// congruence and mined structural disequalities.
    #[test]
    fn dt_axiom_recording_keeps_unpromoted_families_generic() {
        let mut exec = Executor::new();
        let commands = parse(
            r#"
            (set-logic QF_DT)
            (declare-datatype List ((nil) (cons (hd Int) (tl List))))
            (declare-const x List)
            (declare-const y List)
            (declare-const g Bool)
            "#,
        )
        .expect("datatype declarations parse");
        exec.execute_all(&commands).expect("declarations execute");
        exec.proof_tracker.enable();

        let x = exec.ctx.terms.lookup("x").expect("x is declared");
        let y = exec.ctx.terms.lookup("y").expect("y is declared");
        let g = exec.ctx.terms.lookup("g").expect("g is declared");
        let list_sort = exec.ctx.terms.sort(x).clone();
        let one = exec.ctx.terms.mk_int(1.into());

        // Value-eq congruence biconditional, built exactly as
        // `emit_dt_value_eq_congruence` interns it for the two-constructor
        // List: tester agreement per constructor + guarded field congruence
        // per cons field.
        let is_nil_x = exec
            .ctx
            .terms
            .mk_app(Symbol::named("is-nil"), vec![x], Sort::Bool);
        let is_nil_y = exec
            .ctx
            .terms
            .mk_app(Symbol::named("is-nil"), vec![y], Sort::Bool);
        let is_cons_x = exec
            .ctx
            .terms
            .mk_app(Symbol::named("is-cons"), vec![x], Sort::Bool);
        let is_cons_y = exec
            .ctx
            .terms
            .mk_app(Symbol::named("is-cons"), vec![y], Sort::Bool);
        let t_nil = exec.ctx.terms.mk_eq(is_nil_x, is_nil_y);
        let t_cons = exec.ctx.terms.mk_eq(is_cons_x, is_cons_y);
        let hd_x = exec
            .ctx
            .terms
            .mk_app(Symbol::named("hd"), vec![x], Sort::Int);
        let hd_y = exec
            .ctx
            .terms
            .mk_app(Symbol::named("hd"), vec![y], Sort::Int);
        let tl_x = exec
            .ctx
            .terms
            .mk_app(Symbol::named("tl"), vec![x], list_sort.clone());
        let tl_y = exec
            .ctx
            .terms
            .mk_app(Symbol::named("tl"), vec![y], list_sort.clone());
        let eq_hd = exec.ctx.terms.mk_eq(hd_x, hd_y);
        let eq_tl = exec.ctx.terms.mk_eq(tl_x, tl_y);
        let g_hd = exec.ctx.terms.mk_implies(is_cons_x, eq_hd);
        let g_tl = exec.ctx.terms.mk_implies(is_cons_x, eq_tl);
        let rhs = exec.ctx.terms.mk_and(vec![t_nil, t_cons, g_hd, g_tl]);
        let eq_xy = exec.ctx.terms.mk_eq(x, y);
        let value_eq_bic = exec.ctx.terms.mk_eq(eq_xy, rhs);

        // Mined direct-cycle unit `(not (= x (cons 1 x)))`.
        let cons_x = exec
            .ctx
            .terms
            .mk_app(Symbol::named("cons"), vec![one, x], list_sort.clone());
        let eq_cycle = exec.ctx.terms.mk_eq(x, cons_x);
        let acyclic_unit = exec.ctx.terms.mk_not(eq_cycle);

        // Mined same-constructor unit whose tails are refuted by
        // well-foundedness: `(not (= (cons 1 x) (cons 1 (cons 1 x))))`.
        let outer = exec
            .ctx
            .terms
            .mk_app(Symbol::named("cons"), vec![one, cons_x], list_sort);
        let eq_inj = exec.ctx.terms.mk_eq(cons_x, outer);
        let injective_unit = exec.ctx.terms.mk_not(eq_inj);

        // Other unsupported residues: a forced guard-unit literal and an
        // (F1)-style BARE field equality (modus ponens against an asserted
        // constructor equality — not a standalone theorem).
        let guard_unit = exec.ctx.terms.mk_not(g);
        let bare_field_eq = exec.ctx.terms.mk_eq(hd_x, one);

        let axioms = [
            value_eq_bic,
            acyclic_unit,
            injective_unit,
            guard_unit,
            bare_field_eq,
        ];
        exec.record_dt_axiom_theory_lemmas(&axioms);
        let proof = exec.proof_tracker.take_proof();

        assert_eq!(proof.steps.len(), axioms.len());
        for (step, axiom) in proof.steps.iter().zip(axioms) {
            match step {
                ProofStep::TheoryLemma { kind, clause, .. } => {
                    assert_eq!(clause, &vec![axiom]);
                    assert_eq!(
                        *kind,
                        TheoryLemmaKind::Generic,
                        "unsupported DT axiom must remain fail-closed: {clause:?}"
                    );
                }
                other => panic!("expected theory lemma, got {other:?}"),
            }
        }
    }
}
