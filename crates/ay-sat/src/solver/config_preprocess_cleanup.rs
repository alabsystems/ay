// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum PreprocessOutcome {
    Complete,
    Unsat,
    Stopped(SatUnknownReason),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum PreprocessStageControl {
    Continue,
    ReturnFalse,
    Unsat,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct PreprocessCleanupOutcome {
    pub(super) control: PreprocessStageControl,
    pub(super) invalidated_watches: bool,
}

impl PreprocessCleanupOutcome {
    const fn continue_with(invalidated_watches: bool) -> Self {
        Self {
            control: PreprocessStageControl::Continue,
            invalidated_watches,
        }
    }

    const fn return_false() -> Self {
        Self {
            control: PreprocessStageControl::ReturnFalse,
            invalidated_watches: false,
        }
    }

    const fn unsat(invalidated_watches: bool) -> Self {
        Self {
            control: PreprocessStageControl::Unsat,
            invalidated_watches,
        }
    }
}

impl Solver {
    pub(super) fn run_preprocess_cleanup_stage<F>(
        &mut self,
        preprocessing_quick_mode: bool,
        skip_expensive_preprocessing_passes: bool,
        skip_dense_formula: bool,
        should_stop: &F,
    ) -> PreprocessCleanupOutcome
    where
        F: Fn() -> bool + ?Sized,
    {
        let mut invalidated_watches = false;

        // 5. Conditioning (GBCE): globally blocked clause elimination.
        //    CaDiCaL runs conditioning only in full preprocessing rounds
        //    (internal.cpp:695-739), not in the quick path. Deferred from
        //    preprocessing quick mode.
        if self.preprocessing_should_stop(should_stop) {
            return PreprocessCleanupOutcome::return_false();
        }
        if self.inproc_ctrl.condition.enabled
            && !preprocessing_quick_mode
            && !skip_expensive_preprocessing_passes
        {
            // Conditioning deferred on large formulas -- fires in first
            // inprocessing round at ~2K conflicts (#8084).
            self.set_diagnostic_pass(DiagnosticPass::Condition);
            self.condition();
            self.clear_diagnostic_pass();
            if self.has_empty_clause {
                return PreprocessCleanupOutcome::unsat(invalidated_watches);
            }
        }

        // 6. Subsumption + strengthening.
        //    CaDiCaL runs subsumption only within full BVE rounds
        //    (elim.cpp:1043), not in the quick preprocessing path.
        //    Deferred from preprocessing quick mode.
        //    Bug fix: previously only subsumed clauses were deleted but
        //    strengthening results (literal removal) were silently discarded.
        if self.preprocessing_should_stop(should_stop) {
            return PreprocessCleanupOutcome::return_false();
        }
        if self.inproc_ctrl.subsume.enabled
            && !preprocessing_quick_mode
            && !skip_expensive_preprocessing_passes
        {
            // Post-loop subsumption + strengthening deferred on large
            // formulas -- fires in first inprocessing round (#8084).
            self.set_diagnostic_pass(DiagnosticPass::Subsume);
            self.inproc.subsumer.ensure_num_vars(self.num_vars);
            self.inproc.subsumer.rebuild(&self.arena);
            // CaDiCaL subsume.cpp:349-362: during preprocessing,
            // propagations.search=0 so budget = max(subsumemineff=0,
            // 2*active()). Match this effort limit for large formulas.
            let active_vars = (self.num_vars - self.count_fixed_vars()) as u64;
            self.inproc.subsumer.set_check_limit(2 * active_vars);
            let num_clauses = self.arena.num_clauses();
            let result = self.inproc.subsumer.run_subsumption(
                &mut self.arena,
                &self.cold.freeze_counts,
                0,
                num_clauses,
            );

            // Apply strengthening (self-subsumption) BEFORE forward
            // subsumption deletions. LRAT correctness requires that
            // subsumer clause IDs are still alive when used as resolution
            // hints. If forward subsumption deletes a clause that is also
            // a subsumer for strengthening, the batched LRAT deletion is
            // flushed before the strengthening add step, causing "ERROR:
            // using DELETED hint clause" (#4398).
            self.ensure_reason_clause_marks_current();
            for (clause_idx, new_lits, subsumer_idx) in &result.strengthened {
                let subsumer_hints = if self.cold.lrat_enabled {
                    vec![self.clause_id(ClauseRef(*subsumer_idx as u32))]
                } else {
                    Vec::new()
                };
                self.replace_clause_with_explicit_lrat_hints(
                    *clause_idx,
                    new_lits,
                    &subsumer_hints,
                );
            }
            // Strengthening modifies clause literals in-place, invalidating
            // watch pointers that reference the old literal positions.
            if !result.strengthened.is_empty() {
                invalidated_watches = true;
            }

            // Delete forward-subsumed clauses AFTER strengthening.
            // NOTE: learned clauses DO exist during the preprocess loop
            // (BVE/vivify/probe phases run before this stage and can learn
            // clauses), so this must use the full guarded applier shared
            // with the inprocessing subsume pass: promote a learned
            // subsumer of an irredundant clause to irredundant first
            // (otherwise BVE can later delete the learned survivor with no
            // resolvent and no reconstruction witness, silently losing the
            // constraint), skip deletions whose subsumer died earlier in
            // the batch (#6913), and notify BVE occ/dirty maintenance.
            // ReasonPolicy::Skip (inside the applier) protects reason
            // clauses created by level-0 unit propagation in earlier
            // preprocessing passes.
            for &(clause_idx, subsumer_idx) in &result.subsumed {
                self.apply_forward_subsumption_deletion(clause_idx, subsumer_idx);
            }
            self.clear_diagnostic_pass();

            // Propagate any units discovered by strengthening.
            if self.propagate_check_unsat() {
                return PreprocessCleanupOutcome::unsat(invalidated_watches);
            }
        }

        // 7. Component analysis (#8168): detect formula decomposition after
        //    BVE + subsumption. Measurement-only pass: logs component
        //    structure and updates stats. Sub-solver invocation is deferred
        //    pending measurement data showing sufficient decomposable instances.
        //    Skip on large dense formulas: analyze_components allocates
        //    Vec<Vec<Literal>> for all clauses, which is O(total_lits) memory
        //    and time. On shuffling-2 (4.7M clauses), this alone costs ~100ms.
        if self.preprocessing_should_stop(should_stop) {
            return PreprocessCleanupOutcome::return_false();
        }
        if !skip_dense_formula && self.inproc_ctrl.decompose.enabled {
            self.analyze_components();
        }

        PreprocessCleanupOutcome::continue_with(invalidated_watches)
    }
}
