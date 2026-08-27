// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT scope alignment and assignment ingestion.
//!
//! ITE-inactive atoms are deferred, but Boolean ITE conditions are forwarded
//! so arithmetic theories can resolve the selected branch. The JIT and scalar
//! lanes preserve the same assertion/defer/skip ordering.

use ay_core::{TermId, TheorySolver};
use ay_sat::{Literal, Variable};

use super::*;
use crate::extension::types::format_term_recursive;

enum AssertionLane {
    Jit(u32),
    Scalar(Variable),
}

impl<T: TheorySolver> TheoryExtension<'_, T> {
    pub(super) fn align_theory_scope(&mut self, round: &mut PropagationRound<'_>) {
        while self.theory_level < round.sat_level {
            self.level_trail_positions.push(self.last_trail_pos);
            self.theory.push();
            self.theory_level += 1;
            round.pushed_scope = true;
            if let Some(diag) = self.diagnostic_trace {
                diag.emit_push(self.theory_level);
            }
            if self.debug {
                safe_eprintln!("[EAGER] Push to theory level {}", self.theory_level);
            }
        }
    }

    pub(super) fn feed_new_assignments(&mut self, round: &mut PropagationRound<'_>) {
        let new_assignments = round.trail.get(self.last_trail_pos..).unwrap_or_default();
        #[cfg(feature = "jit")]
        let asserted = if self.jit_dispatch_table.is_some() {
            self.feed_jit_assignments(new_assignments, round)
        } else {
            self.feed_scalar_assignments(new_assignments, round)
        };
        #[cfg(not(feature = "jit"))]
        let asserted = self.feed_scalar_assignments(new_assignments, round);
        round.asserted_atoms = asserted;
        self.last_trail_pos = round.trail.len();
    }

    #[cfg(feature = "jit")]
    fn feed_jit_assignments(
        &mut self,
        assignments: &[Literal],
        round: &PropagationRound<'_>,
    ) -> usize {
        let Some(dispatch) = self.jit_dispatch_table.as_ref() else {
            return 0;
        };
        let mut asserted = 0;
        for &literal in assignments {
            let variable = literal.variable();
            let var_id = variable.id();
            let value = literal.is_positive();
            let result = dispatch.dispatch_assignment(
                var_id,
                value,
                &|condition| round.ctx.value(Variable::new(condition)),
                round.sat_level,
            );
            self.eager_stats.jit_dispatch_atoms += 1;
            match result {
                ay_jit::TheoryDispatchResult::Assert { term_id, value } => {
                    let term = TermId(term_id);
                    self.trace_assertion(
                        term,
                        value,
                        round.sat_level,
                        6,
                        AssertionLane::Jit(var_id),
                    );
                    self.theory.assert_literal(term, value);
                    asserted += 1;
                }
                ay_jit::TheoryDispatchResult::DeferIte { term_id, value } => {
                    let level = round.ctx.var_level(variable).unwrap_or(round.sat_level);
                    self.ite_deferred_atoms
                        .push((TermId(term_id), value, level, false));
                    self.eager_stats.ite_relevancy_skips += 1;
                }
                ay_jit::TheoryDispatchResult::Skip => {
                    if let Some(term) = self.ite_condition_term(var_id) {
                        self.theory.assert_literal(term, value);
                        asserted += 1;
                    }
                }
            }
        }
        asserted
    }

    fn feed_scalar_assignments(
        &mut self,
        assignments: &[Literal],
        round: &PropagationRound<'_>,
    ) -> usize {
        assignments
            .iter()
            .map(|&literal| self.feed_scalar_assignment(literal, round))
            .sum()
    }

    fn feed_scalar_assignment(&mut self, literal: Literal, round: &PropagationRound<'_>) -> usize {
        let variable = literal.variable();
        if !self.is_theory_atom(variable) {
            let Some(term) = self.ite_condition_term(variable.id()) else {
                return 0;
            };
            self.theory.assert_literal(term, literal.is_positive());
            return 1;
        }
        let Some(&term) = self.var_to_term.get(&variable.id()) else {
            return 0;
        };
        let value = literal.is_positive();
        if self.ite_atom_is_inactive(variable, round) {
            let level = round.ctx.var_level(variable).unwrap_or(round.sat_level);
            self.ite_deferred_atoms.push((term, value, level, false));
            self.eager_stats.ite_relevancy_skips += 1;
            return 0;
        }
        self.trace_assertion(
            term,
            value,
            round.sat_level,
            500,
            AssertionLane::Scalar(variable),
        );
        self.theory.assert_literal(term, value);
        1
    }

    fn ite_atom_is_inactive(&self, variable: Variable, round: &PropagationRound<'_>) -> bool {
        if crate::theory_debug_flags::no_ite_deferral() {
            return false;
        }
        let index = variable.id() as usize;
        let word = index / 64;
        let guarded = word < self.ite_guarded_bitset.len()
            && (self.ite_guarded_bitset[word] >> (index % 64)) & 1 != 0;
        if !guarded {
            return false;
        }
        let (condition, then_branch) = self.ite_branch_guards[index];
        round
            .ctx
            .value(Variable::new(condition))
            .is_some_and(|value| value != then_branch)
    }

    fn ite_condition_term(&self, var_id: u32) -> Option<TermId> {
        let index = var_id as usize;
        let word = index / 64;
        let is_condition = word < self.ite_condition_bitset.len()
            && (self.ite_condition_bitset[word] >> (index % 64)) & 1 != 0;
        is_condition.then(|| {
            self.var_to_term
                .get(&var_id)
                .or_else(|| self.ite_condition_var_to_term.get(&var_id))
                .copied()
        })?
    }

    fn trace_assertion(
        &self,
        term: TermId,
        value: bool,
        sat_level: u32,
        depth: u32,
        lane: AssertionLane,
    ) {
        if self.debug {
            match lane {
                AssertionLane::Jit(var_id) => safe_eprintln!(
                    "[EAGER] Asserting term {:?} = {} (var {}) at level {} [jit]",
                    term,
                    value,
                    var_id,
                    sat_level,
                ),
                AssertionLane::Scalar(variable) => safe_eprintln!(
                    "[EAGER] Asserting term {:?} = {} (var {:?}) at level {}",
                    term,
                    value,
                    variable,
                    sat_level,
                ),
            }
        }
        if sat_level == 0 && tracing::enabled!(tracing::Level::DEBUG) {
            if let Some(terms) = self.terms {
                let term_str = format_term_recursive(terms, term, depth);
                tracing::debug!(
                    term = ?term,
                    value,
                    term_str = %term_str,
                    "  asserting theory atom at level 0"
                );
            }
        }
    }
}
