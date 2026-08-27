// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Producer-side context records for exact datatype proof reconstruction.

use std::collections::BTreeSet;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{TermId, TheoryLit, TheorySolver};
use ay_sat::{Literal, SolverContext};

use super::TheoryExtension;
use crate::executor::{DtContextConflictRecord, DtContextConflictSink};

const MAX_CONTEXT_CONFLICT_LITERALS: usize = 64;
const MAX_REASON_EXPANSIONS: usize = 4096;
const MAX_CONTEXT_PREMISES: usize = 16;
const REASON_FLATTEN_BUDGET: usize = 64;

struct ContextConflictPartition {
    premises: Vec<TermId>,
    surviving: Vec<TermId>,
    pending: Vec<Literal>,
}

impl<'a, T: TheorySolver> TheoryExtension<'a, T> {
    /// Wire the Executor-owned context-derivation record sink into this eager
    /// extension. `None` remains the record-free default.
    pub(crate) fn with_context_records(mut self, records: &'a mut DtContextConflictSink) -> Self {
        self.context_records = Some(records);
        self
    }
}

impl<T: TheorySolver> TheoryExtension<'_, T> {
    /// Preserve the premises that level-0 conflict minimization strips.
    pub(super) fn record_context_conflict_premises(
        &mut self,
        conflict_terms: &[TheoryLit],
        ctx: &dyn SolverContext,
    ) {
        if self.context_records.is_none()
            || conflict_terms.is_empty()
            || conflict_terms.len() > MAX_CONTEXT_CONFLICT_LITERALS
        {
            return;
        }
        let Some(proof) = self.proof.as_ref() else {
            return;
        };
        let negations = proof.negations;
        let Some(partition) = self.partition_context_conflict(conflict_terms, ctx, negations)
        else {
            return;
        };
        let expansions = self.expand_level_zero_reasons(partition.pending, ctx, negations);
        let Some(records) = self.context_records.as_deref_mut() else {
            return;
        };
        records.record(partition.surviving, partition.premises);
        for expansion in expansions {
            records.record(expansion.clause, expansion.premises);
        }
    }

    fn partition_context_conflict(
        &self,
        conflict_terms: &[TheoryLit],
        ctx: &dyn SolverContext,
        negations: &HashMap<TermId, TermId>,
    ) -> Option<ContextConflictPartition> {
        let mut premises = Vec::new();
        let mut surviving = Vec::new();
        let mut pending = Vec::new();
        for conflict_lit in conflict_terms {
            let literal = self.term_to_literal(conflict_lit.term, !conflict_lit.value)?;
            let &negation = negations.get(&conflict_lit.term)?;
            let (fact, blocking) = if conflict_lit.value {
                (conflict_lit.term, negation)
            } else {
                (negation, conflict_lit.term)
            };
            if ctx.var_level(literal.variable()) == Some(0) {
                premises.push(fact);
                if let Some(true_literal) =
                    self.term_to_literal(conflict_lit.term, conflict_lit.value)
                {
                    pending.push(true_literal);
                }
            } else {
                surviving.push(blocking);
            }
        }
        (!premises.is_empty() && !surviving.is_empty()).then_some(ContextConflictPartition {
            premises,
            surviving,
            pending,
        })
    }

    fn expand_level_zero_reasons(
        &self,
        mut pending: Vec<Literal>,
        ctx: &dyn SolverContext,
        negations: &HashMap<TermId, TermId>,
    ) -> Vec<DtContextConflictRecord> {
        let mut expansions = Vec::new();
        let mut visited = BTreeSet::new();
        // Seed the walk with the WHOLE level-0 trail prefix, not only
        // the conflict's own premises: rewrite-time hints cite facts
        // (e.g. the taken move's enum equality) that no conflict chain
        // happens to traverse, and those discharge only if the level-0
        // implication graph gave them records too. Bounded by the
        // visited cap exactly like the conflict-seeded walk.
        for &trail_literal in ctx.trail() {
            if ctx.var_level(trail_literal.variable()) == Some(0) {
                pending.push(trail_literal);
            } else {
                break;
            }
        }
        while let Some(true_literal) = pending.pop() {
            if visited.len() >= MAX_REASON_EXPANSIONS
                || !visited.insert(true_literal.variable().index() as u32)
            {
                continue;
            }
            let Some(initial_side) = ctx.var_reason_side(true_literal.variable()) else {
                continue;
            };
            let Some(fact) = self.fact_term_for_literal(true_literal, negations) else {
                continue;
            };
            let Some((side_facts, atom_sides)) =
                self.flatten_reason_side(initial_side, ctx, negations)
            else {
                continue;
            };
            pending.extend(atom_sides.into_iter().map(Literal::negated));
            expansions.push(DtContextConflictRecord {
                clause: vec![fact],
                premises: side_facts,
            });
        }
        expansions
    }

    fn flatten_reason_side(
        &self,
        mut side_work: Vec<Literal>,
        ctx: &dyn SolverContext,
        negations: &HashMap<TermId, TermId>,
    ) -> Option<(Vec<TermId>, Vec<Literal>)> {
        if side_work.is_empty() {
            return None;
        }
        let mut side_facts = Vec::new();
        let mut atom_sides = Vec::new();
        let mut seen_side = BTreeSet::new();
        let mut budget = REASON_FLATTEN_BUDGET;
        while let Some(side_literal) = side_work.pop() {
            budget = budget.checked_sub(1)?;
            let side_key = (side_literal.variable().index() as u64) * 2
                + u64::from(side_literal.is_positive());
            if !seen_side.insert(side_key) {
                continue;
            }
            if let Some(side_fact) = self.fact_term_for_literal(side_literal.negated(), negations) {
                if !side_facts.contains(&side_fact) {
                    side_facts.push(side_fact);
                    atom_sides.push(side_literal);
                }
                continue;
            }
            let aux_true = side_literal.negated();
            if ctx.var_level(aux_true.variable()) != Some(0) {
                return None;
            }
            side_work.extend(ctx.var_reason_side(aux_true.variable())?);
        }
        (!side_facts.is_empty()).then_some((side_facts, atom_sides))
    }

    fn fact_term_for_literal(
        &self,
        literal: Literal,
        negations: &HashMap<TermId, TermId>,
    ) -> Option<TermId> {
        let atom = *self.var_to_term.get(&(literal.variable().index() as u32))?;
        literal
            .is_positive()
            .then_some(atom)
            .or_else(|| negations.get(&atom).copied())
    }

    pub(super) fn minimize_context_conflict(
        &mut self,
        conflict_terms: &[TheoryLit],
        clause: &mut Vec<Literal>,
        ctx: &dyn SolverContext,
    ) {
        self.record_context_conflict_premises(conflict_terms, ctx);
        let removed = crate::theory_inference::minimize_conflict_with_levels(clause, |var| {
            ctx.var_level(var)
        });
        self.eager_stats.theory_minimize_lits_removed += removed as u64;
    }

    /// Record a lazy level-0 propagation without changing its SAT reason path.
    pub(super) fn record_lazy_context_propagation(
        &mut self,
        ctx: &dyn SolverContext,
        literal: &TheoryLit,
        reason_data: u64,
    ) {
        if ctx.decision_level() != 0 || self.context_records_full() {
            return;
        }
        if let Some(reason) = self.theory.explain_propagation(literal.term, reason_data) {
            self.record_context_propagation(literal, &reason);
        }
    }

    fn context_records_full(&self) -> bool {
        self.context_records
            .as_deref()
            .is_none_or(DtContextConflictSink::is_full)
    }

    /// Record `fact ← reason facts` for certification-time premise chains.
    pub(super) fn record_context_propagation(&mut self, literal: &TheoryLit, reason: &[TheoryLit]) {
        if reason.is_empty()
            || reason.len() > MAX_CONTEXT_PREMISES
            || self.context_records.is_none()
        {
            return;
        }
        let Some(proof) = self.proof.as_ref() else {
            return;
        };
        let negations = proof.negations;
        let fact_of = |lit: &TheoryLit| {
            lit.value
                .then_some(lit.term)
                .or_else(|| negations.get(&lit.term).copied())
        };
        let Some(fact) = fact_of(literal) else {
            return;
        };
        let mut premises = Vec::with_capacity(reason.len());
        for reason_lit in reason {
            let Some(premise) = fact_of(reason_lit) else {
                return;
            };
            if premise != fact && !premises.contains(&premise) {
                premises.push(premise);
            }
        }
        if premises.is_empty() {
            return;
        }
        if let Some(records) = self.context_records.as_deref_mut() {
            records.record(vec![fact], premises);
        }
    }
}
