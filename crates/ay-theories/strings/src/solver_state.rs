// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver construction, state transfer, model extraction, and internal equality handling.

use super::*;

impl<'a> StringSolver<'a> {
    /// Create a new string solver with a reference to the term store.
    pub fn new(terms: &'a TermStore) -> Self {
        Self {
            terms,
            state: SolverState::new(),
            base: BaseSolver::new(),
            core: CoreSolver::new(),
            regexp: RegExpSolver::new(),
            infer: InferenceManager::new(),
            skolems: SkolemCache::new(),
            pre_registered_empty: None,
            cycle_conflict_trustworthy: false,
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
        }
    }

    /// Pre-register the empty string term so endpoint-empty inferences work
    /// even when the formula doesn't contain an explicit `""` literal.
    pub fn set_empty_string_id(&mut self, id: TermId) {
        self.pre_registered_empty = Some(id);
        self.state.set_empty_string_id(self.terms, id);
    }

    /// Mark a term as having been reduced via DPLL-level reduction lemmas.
    /// The core solver will skip these terms in `check_extf_reductions`.
    pub fn mark_reduced(&mut self, term: TermId) {
        self.core.mark_reduced(term);
    }

    /// Extract warm state for cross-iteration preservation (#3762).
    ///
    /// Captures statistics and reduced-term markers that should persist
    /// across CEGAR iterations. Call this before dropping the solver
    /// (e.g., before `DpllT::into_sat_state()`), then call
    /// `import_warm_state()` on the replacement solver.
    pub fn take_warm_state(&self) -> StringSolverWarmState {
        StringSolverWarmState {
            check_count: self.check_count,
            conflict_count: self.conflict_count,
            propagation_count: self.propagation_count,
            reduced_terms: self.core.reduced_term_ids(),
        }
    }

    /// Import warm state from a previous CEGAR iteration (#3762).
    ///
    /// Restores statistics and reduced-term markers that were extracted
    /// via `take_warm_state()`. This avoids losing cumulative statistics
    /// and re-registering reduced terms externally.
    pub fn import_warm_state(&mut self, state: &StringSolverWarmState) {
        self.check_count = state.check_count;
        self.conflict_count = state.conflict_count;
        self.propagation_count = state.propagation_count;
        for &tid in &state.reduced_terms {
            self.core.mark_reduced(tid);
        }
    }

    /// Extract a concrete model for string variables.
    ///
    /// Only variables in EQCs with known constants are assigned. Variables in
    /// non-constant EQCs remain unassigned and are handled conservatively by
    /// the caller.
    /// Whether the last conflict from `check()` came from ground evaluation
    /// (constant conflicts, extf predicate/reduction checks) rather than
    /// NF-dependent reasoning. Ground conflicts are always trustworthy;
    /// NF-dependent conflicts may be spurious due to incomplete normal form
    /// computation (#6275).
    ///
    /// Only meaningful after `check()` returned `TheoryResult::Unsat`.
    pub fn is_ground_conflict(&self) -> bool {
        self.infer.is_ground_conflict()
    }

    /// Whether the conflict follows from cycle detection (I_CYCLE) inferences.
    /// Cycle-derived equalities (e.g., x = str.++(y,x) → y = "") are sound,
    /// so subsequent NF-based conflicts are trustworthy (#3875).
    ///
    /// Only meaningful after `check()` returned `TheoryResult::Unsat`.
    pub fn is_cycle_based_conflict(&self) -> bool {
        self.cycle_conflict_trustworthy
    }

    /// Extract a string model mapping variables to their resolved constant values.
    pub fn extract_model(&self) -> StringModel {
        let mut values = HashMap::default();
        for rep in self.state.eqc_representatives() {
            let Some(constant) = self.state.get_constant(&rep) else {
                continue;
            };
            let Some(members) = self.state.eqc_members(rep) else {
                continue;
            };
            for &member in members {
                if *self.terms.sort(member) == Sort::String
                    && matches!(self.terms.get(member), ay_core::term::TermData::Var(_, _))
                {
                    values.insert(member, constant.to_string());
                }
            }
        }
        StringModel { values }
    }

    /// When N-O propagates an integer equality where one side is `str.len(x)`
    /// and the other resolves to 0, infer `x = ""` by merging x with the empty
    /// string. This bridges the gap between LIA-derived length facts and
    /// string-level emptiness — the SAT-level bridge axiom
    /// `[NOT(str.len(x)=0), x=""]` cannot fire in the CEGAR architecture
    /// because the LIA-derived equality is not propagated as a SAT literal.
    pub(super) fn infer_empty_from_zero_length(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        reason: &[TheoryLit],
    ) {
        // Identify which side is str.len(var) and which is the integer constant.
        let (len_term, const_term) = match (
            self.state.get_str_len_arg(self.terms, lhs),
            self.state.get_str_len_arg(self.terms, rhs),
        ) {
            (Some(_), None) => (lhs, rhs),
            (None, Some(_)) => (rhs, lhs),
            _ => return,
        };

        // Check if const_term resolves to 0.
        let is_zero = self
            .state
            .resolve_int_constant(self.terms, const_term)
            .is_some_and(|n| n == 0);
        if !is_zero {
            return;
        }

        // Get the string variable from str.len(var).
        let Some(str_var) = self.state.get_str_len_arg(self.terms, len_term) else {
            return;
        };

        // Use the cached empty string (registered during CEGAR init).
        let Some(empty) = self.state.empty_string_id() else {
            return;
        };

        // Ensure str_var is registered (it might not be if only seen inside str.len).
        self.state.register_term(self.terms, str_var);

        if self.state.find(str_var) != self.state.find(empty) {
            let _ = self.state.merge_with_explanation(str_var, empty, reason);
        }
    }

    /// Drain internal equalities from the inference engine and merge them
    /// into the local EQC state.
    ///
    /// Equalities with non-empty explanations are merged normally. Equalities
    /// with empty explanations are converted to SAT-level `EqualitySplit`
    /// lemmas instead of being silently dropped (#4025). This prevents
    /// premature fix-point convergence: the DPLL solver decides the equality
    /// with a proper reason chain, providing the explanation provenance that
    /// the proof forest was missing.
    pub(super) fn merge_internal_equalities(&mut self) -> MergeResult {
        let mut merged_any = false;
        let mut deferred_splits = Vec::new();
        let internal_equalities = self.infer.drain_internal_equalities();
        for eq in internal_equalities {
            self.state.register_term(self.terms, eq.lhs);
            self.state.register_term(self.terms, eq.rhs);

            if self.state.find(eq.lhs) != self.state.find(eq.rhs) {
                // Soundness guard (#4057): reject internal equalities
                // with empty explanations. A merge with an empty explanation
                // creates a proof-forest edge with no reasons, causing all
                // downstream explain() calls through that edge to return
                // incomplete results.
                //
                // Instead of silently dropping (#4025), convert to a
                // SAT-level EqualitySplit so the DPLL solver decides the
                // equality. If DPLL assigns true, the equality comes back
                // via assert_literal with a proper SAT-level reason. If
                // false, the disequality is decided. Either way, the
                // fix-point loop no longer converges prematurely.
                if eq.explanation.is_empty() {
                    deferred_splits.push(StringLemma {
                        kind: StringLemmaKind::EqualitySplit,
                        x: eq.lhs,
                        y: eq.rhs,
                        char_offset: 0,
                        start_offset: 0,
                        reason: vec![],
                    });
                    continue;
                }
                let _ = self
                    .state
                    .merge_with_explanation(eq.lhs, eq.rhs, &eq.explanation);
                merged_any = true;
            }
        }
        MergeResult {
            merged_any,
            deferred_splits,
        }
    }
}
