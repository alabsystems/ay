// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared theory-dispatch helpers for `DpllT` solve paths.

use ay_core::{TheoryResult, TheorySolver};
use ay_sat::{Literal, SatResult, Variable};

use crate::{DpllT, FinalCheckResult, SolveStepResult, TheoryCheck, TheoryDispatch};

impl<T: TheorySolver> DpllT<'_, T> {
    pub(crate) fn check_metrics(check: &TheoryCheck) -> (usize, usize) {
        match check {
            TheoryCheck::Propagated(count) => (*count, 0),
            TheoryCheck::Conflict(clause) => (0, clause.len()),
            _ => (0, 0),
        }
    }

    pub(crate) fn dispatch_label(
        dispatch: &TheoryDispatch,
    ) -> (&'static str, Option<&'static str>) {
        match dispatch {
            TheoryDispatch::Accept => ("accept", Some("DeclareSat")),
            TheoryDispatch::Unknown => ("unknown", Some("DeclareUnknown")),
            TheoryDispatch::NeedSplit(_) => ("need_split", Some("NeedSplit")),
            TheoryDispatch::NeedDisequalitySplit(_) => {
                ("need_disequality_split", Some("NeedDisequalitySplit"))
            }
            TheoryDispatch::NeedExpressionSplit(_) => {
                ("need_expression_split", Some("NeedExpressionSplit"))
            }
            TheoryDispatch::NeedStringLemma(_) => ("need_string_lemma", Some("NeedStringLemma")),
            TheoryDispatch::NeedLemmas(_) => ("need_lemmas", Some("NeedLemmas")),
            TheoryDispatch::NeedModelEquality(_) => {
                ("need_model_equality", Some("NeedModelEquality"))
            }
            TheoryDispatch::NeedModelEqualities(_) => {
                ("need_model_equalities", Some("NeedModelEqualities"))
            }
            TheoryDispatch::Continue => ("continue", Some("RoundContinue")),
        }
    }

    /// Dispatch a theory check result, handling conflict clauses and propagation.
    ///
    /// When `forward_splits` is true (step mode), split requests are returned to
    /// the caller. When false (loop mode), they are mapped to `Unknown` since
    /// the basic solve loop cannot handle splits.
    pub(crate) fn dispatch_theory_check(
        &mut self,
        check: TheoryCheck,
        forward_splits: bool,
    ) -> TheoryDispatch {
        match check {
            TheoryCheck::Sat => {
                if self.debug_dpll {
                    safe_eprintln!("[DPLL] Theory check: Sat - accepting model");
                }
                TheoryDispatch::Accept
            }
            TheoryCheck::Unknown => TheoryDispatch::Unknown,
            TheoryCheck::NeedSplit(s) if forward_splits => {
                self.emit_theory_split_event("need_split", self.timings.round_trips);
                TheoryDispatch::NeedSplit(s)
            }
            TheoryCheck::NeedDisequalitySplit(s) if forward_splits => {
                self.emit_theory_split_event("need_disequality_split", self.timings.round_trips);
                TheoryDispatch::NeedDisequalitySplit(s)
            }
            TheoryCheck::NeedExpressionSplit(s) if forward_splits => {
                self.emit_theory_split_event("need_expression_split", self.timings.round_trips);
                TheoryDispatch::NeedExpressionSplit(s)
            }
            TheoryCheck::NeedStringLemma(l) if forward_splits => {
                self.emit_theory_split_event("need_string_lemma", self.timings.round_trips);
                TheoryDispatch::NeedStringLemma(l)
            }
            TheoryCheck::NeedLemmas(lemmas) if forward_splits => {
                self.emit_theory_split_event("need_lemmas", self.timings.round_trips);
                TheoryDispatch::NeedLemmas(lemmas)
            }
            TheoryCheck::NeedLemmas(lemmas) => {
                if self.debug_dpll {
                    safe_eprintln!(
                        "[DPLL] Applying {} theory lemma clause(s) in-place",
                        lemmas.len()
                    );
                }
                for lemma in &lemmas {
                    self.apply_theory_lemma(&lemma.clause);
                }
                TheoryDispatch::Continue
            }
            TheoryCheck::NeedModelEquality(e) if forward_splits => {
                self.emit_theory_split_event("need_model_equality", self.timings.round_trips);
                TheoryDispatch::NeedModelEquality(e)
            }
            TheoryCheck::NeedModelEqualities(es) if forward_splits => {
                self.emit_theory_split_event("need_model_equalities", self.timings.round_trips);
                TheoryDispatch::NeedModelEqualities(es)
            }
            TheoryCheck::NeedSplit(_)
            | TheoryCheck::NeedDisequalitySplit(_)
            | TheoryCheck::NeedExpressionSplit(_)
            | TheoryCheck::NeedStringLemma(_)
            | TheoryCheck::NeedModelEquality(_)
            | TheoryCheck::NeedModelEqualities(_) => {
                self.emit_theory_split_event("deferred_split", self.timings.round_trips);
                TheoryDispatch::Unknown
            }
            TheoryCheck::Conflict(c) if c.is_empty() => TheoryDispatch::Unknown,
            TheoryCheck::Conflict(c) => {
                if self.debug_dpll {
                    safe_eprintln!(
                        "[DPLL] Adding theory conflict clause with {} literals",
                        c.len()
                    );
                }
                // #8421: Bump VSIDS activity for variables in theory conflict
                // clauses so the SAT solver prioritizes contentious theory atoms.
                for lit in &c {
                    self.sat.bump_variable_activity(lit.variable());
                }
                self.sat.add_clause(c);
                self.theory_conflict_count += 1;
                TheoryDispatch::Continue
            }
            TheoryCheck::Propagated(count) => {
                if self.debug_dpll {
                    safe_eprintln!("[DPLL] Theory propagated {} clause(s), re-solving", count);
                }
                self.theory_propagation_count += count as u64;
                TheoryDispatch::Continue
            }
        }
    }

    /// Run the full Nelson-Oppen fixpoint check if the theory requires it.
    ///
    /// `check_during_propagate()` is a lightweight per-theory check that does NOT
    /// run the N-O fixpoint loop. For combined theories (EUF+LIA, EUF+LRA, etc.),
    /// cross-theory equalities discovered by congruence closure must be forwarded
    /// to arithmetic before we can accept a SAT model. (#6825)
    pub(crate) fn run_final_check_if_needed(&mut self) -> FinalCheckResult {
        if !self.theory.needs_final_check_after_sat() {
            return FinalCheckResult::Accept;
        }
        let final_result = self.theory.check();
        match final_result {
            TheoryResult::Sat => FinalCheckResult::Accept,
            TheoryResult::Unsat(conflict_terms) => {
                // #8424: EUF chain minimization at the theory level.
                let mut conflict_terms = conflict_terms;
                if let Some(terms) = self.terms {
                    let euf_removed =
                        crate::theory_inference::minimize_euf_conflict(&mut conflict_terms, terms);
                    self.theory_minimize_lits_removed += euf_removed as u64;
                }
                let mut clause: Vec<Literal> = conflict_terms
                    .iter()
                    .map(|t| self.term_to_literal_or_register(t.term, !t.value))
                    .collect();
                if clause.is_empty() {
                    return FinalCheckResult::Unknown;
                }
                // #8424: Pre-minimize conflict clause with level-0 removal.
                let removed =
                    crate::theory_inference::minimize_conflict_with_levels(&mut clause, |var| {
                        self.sat.var_level(var)
                    });
                self.theory_minimize_lits_removed += removed as u64;
                // #8421: Bump VSIDS activity for variables in final-check conflict.
                for lit in &clause {
                    self.sat.bump_variable_activity(lit.variable());
                }
                if clause.is_empty() {
                    return FinalCheckResult::Unknown;
                }
                self.sat.add_clause(clause);
                FinalCheckResult::Conflict
            }
            TheoryResult::UnsatWithFarkas(conflict) => {
                let mut clause: Vec<Literal> = conflict
                    .literals
                    .iter()
                    .map(|t| self.term_to_literal_or_register(t.term, !t.value))
                    .collect();
                if clause.is_empty() {
                    return FinalCheckResult::Unknown;
                }
                // #8424: Pre-minimize Farkas conflict clause, then level-0 removal.
                let mut removed = if let Some(ref farkas) = conflict.farkas {
                    let mut coeffs = farkas.coefficients.clone();
                    crate::theory_inference::minimize_farkas_conflict(&mut clause, &mut coeffs)
                } else {
                    0
                };
                // Level-0 removal applies to both Farkas and non-Farkas paths.
                removed +=
                    crate::theory_inference::minimize_conflict_with_levels(&mut clause, |var| {
                        self.sat.var_level(var)
                    });
                self.theory_minimize_lits_removed += removed as u64;
                // #8421: Bump VSIDS activity for variables in Farkas final-check conflict.
                for lit in &clause {
                    self.sat.bump_variable_activity(lit.variable());
                }
                if clause.is_empty() {
                    return FinalCheckResult::Unknown;
                }
                self.sat.add_clause(clause);
                FinalCheckResult::Conflict
            }
            _ => FinalCheckResult::Unknown,
        }
    }

    /// Convert a `TheoryResult` split variant to a `SolveStepResult`.
    pub(crate) fn theory_result_to_step(result: TheoryResult) -> SolveStepResult {
        match result {
            TheoryResult::NeedSplit(s) => SolveStepResult::NeedSplit(s),
            TheoryResult::NeedDisequalitySplit(s) => SolveStepResult::NeedDisequalitySplit(s),
            TheoryResult::NeedExpressionSplit(s) => SolveStepResult::NeedExpressionSplit(s),
            TheoryResult::NeedExpressionSplits(splits) => {
                let Some(split) = splits.into_iter().next() else {
                    return SolveStepResult::Done(SatResult::Unknown);
                };
                SolveStepResult::NeedExpressionSplit(split)
            }
            TheoryResult::NeedStringLemma(l) => SolveStepResult::NeedStringLemma(l),
            TheoryResult::NeedLemmas(lemmas) => SolveStepResult::NeedLemmas(lemmas),
            TheoryResult::NeedModelEquality(e) => SolveStepResult::NeedModelEquality(e),
            TheoryResult::NeedModelEqualities(es) => SolveStepResult::NeedModelEqualities(es),
            TheoryResult::Sat
            | TheoryResult::Unknown
            | TheoryResult::Unsat(_)
            | TheoryResult::UnsatWithFarkas(_) => SolveStepResult::Done(SatResult::Unknown),
            other => {
                unreachable!("unhandled TheoryResult variant in theory_result_to_step(): {other:?}")
            }
        }
    }

    /// Pre-apply theory phase hints to the SAT solver's saved phases (#6296).
    ///
    /// For SAT solve paths that don't support Extension callbacks (assumption
    /// loop, `solve_loop`), we set the initial phase for theory atoms so
    /// `pick_phase` uses theory-guided polarity on the first decision.
    pub(crate) fn apply_theory_phase_hints(&mut self) {
        for &atom in &self.theory_atoms {
            if let Some(phase) = self.theory.suggest_phase(atom) {
                if let Some(&sat_var_idx) = self.term_to_var.get(&atom) {
                    self.sat.set_var_phase(Variable::new(sat_var_idx), phase);
                }
            }
        }
    }
}
