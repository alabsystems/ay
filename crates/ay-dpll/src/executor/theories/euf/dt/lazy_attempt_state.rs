// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by executor::theories::euf::dt to preserve item paths.

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
