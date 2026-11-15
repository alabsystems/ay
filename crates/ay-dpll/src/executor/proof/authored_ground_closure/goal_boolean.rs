// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked Boolean congruence and nested-disjunction coverage goals.
//! These only propose ordinary Alethe derivations from earlier closure edges.

use super::emit::ClosureEmitter;
use super::facts::FactBase;
use super::goal::MAX_GOAL_DEPTH;
use super::*;

pub(super) struct Coverage {
    guard: TermId,
    member: TermId,
    path: Vec<(TermId, TermId)>,
}

impl Executor {
    pub(super) fn ground_boolean_fact_source_parts(
        &self,
        closure: &GroundClosure,
        facts: &FactBase,
        term: TermId,
    ) -> Option<usize> {
        if self.ctx.terms.sort(term) != &Sort::Bool {
            return None;
        }
        facts.facts().iter().position(|fact| {
            self.ctx.terms.sort(fact.literal) == &Sort::Bool
                && closure.same_class(term, fact.literal)
        })
    }

    /// Only `(or (not guard) union)` with a nested `or` member already proved
    /// equal to `guard`. There is no model guess, Boolean normalization or SAT
    /// assumption here. Exhaustion declines the entire goal search.
    pub(super) fn ground_boolean_coverage_parts(
        &self,
        closure: &GroundClosure,
        term: TermId,
        work: &mut usize,
    ) -> Option<Option<Coverage>> {
        let TermData::App(Symbol::Named(head), args) = self.ctx.terms.get(term) else {
            return Some(None);
        };
        if head != "or" || args.len() != 2 || self.ctx.terms.sort(term) != &Sort::Bool {
            return Some(None);
        }
        let TermData::Not(guard) = self.ctx.terms.get(args[0]) else {
            return Some(None);
        };
        if self.ctx.terms.sort(*guard) != &Sort::Bool || self.ctx.terms.sort(args[1]) != &Sort::Bool
        {
            return Some(None);
        }
        let mut pending = vec![(args[1], Vec::new())];
        while let Some((member, path)) = pending.pop() {
            *work = work.checked_sub(1)?;
            if path.len() > MAX_GOAL_DEPTH {
                return None;
            }
            if member != args[0] && closure.same_class(member, *guard) {
                return Some(Some(Coverage {
                    guard: *guard,
                    member,
                    path,
                }));
            }
            if let TermData::App(Symbol::Named(head), children) = self.ctx.terms.get(member) {
                if head == "or"
                    && children
                        .iter()
                        .all(|&child| self.ctx.terms.sort(child) == &Sort::Bool)
                {
                    for &child in children.iter().rev() {
                        let mut next = path.clone();
                        next.push((member, child));
                        pending.push((child, next));
                    }
                }
            }
        }
        Some(None)
    }

    pub(super) fn emit_ground_boolean_fact(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        term: TermId,
        source: usize,
    ) -> Option<DerivedUnit> {
        let fact = self.emit_ground_fact(emitter, source)?;
        let limit = emitter.closure.edges().len();
        let equality = self.emit_closure_path_unit(emitter, fact.literal, term, limit)?;
        let negative_eq = self.ctx.terms.mk_not_raw(equality.literal);
        let negative_fact = self.ctx.terms.mk_not_raw(fact.literal);
        let clause = vec![negative_eq, negative_fact, term];
        let introduced = emitter.proof.add_rule_step(
            AletheRule::EquivPos2,
            clause.clone(),
            Vec::new(),
            Vec::new(),
        );
        let step =
            self.resolve_closure_units(emitter, introduced, clause, &[equality, fact], &[term])?;
        Some(DerivedUnit {
            step,
            literal: term,
        })
    }

    pub(super) fn emit_ground_boolean_coverage(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        term: TermId,
        coverage: Coverage,
    ) -> Option<DerivedUnit> {
        let limit = emitter.closure.edges().len();
        let equality =
            self.emit_closure_path_unit(emitter, coverage.guard, coverage.member, limit)?;
        let negative_eq = self.ctx.terms.mk_not_raw(equality.literal);
        let negative_guard = self.ctx.terms.mk_not_raw(coverage.guard);
        let clause = vec![negative_eq, negative_guard, coverage.member];
        let introduced = emitter.proof.add_rule_step(
            AletheRule::EquivPos2,
            clause.clone(),
            Vec::new(),
            Vec::new(),
        );
        let mut step = self.resolve_closure_units(
            emitter,
            introduced,
            clause,
            &[equality],
            &[negative_guard, coverage.member],
        )?;
        let mut union = coverage.member;
        for (parent, child) in coverage.path.into_iter().rev() {
            emitter.within_budget()?;
            if child != union {
                return None;
            }
            let negative_child = self.ctx.terms.mk_not_raw(child);
            let projection = emitter.proof.add_rule_step(
                AletheRule::OrNeg,
                vec![parent, negative_child],
                Vec::new(),
                Vec::new(),
            );
            step =
                emitter
                    .proof
                    .add_resolution(vec![negative_guard, parent], child, step, projection);
            union = parent;
        }
        let step = self.emit_coverage_or_unit(emitter, step, &[negative_guard, union], term)?;
        Some(DerivedUnit {
            step,
            literal: term,
        })
    }

    /// The same `or_neg`/resolution introduction used by consequence replay.
    /// Its two input literals must be exactly the authored goal's arguments.
    pub(super) fn emit_coverage_or_unit(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        mut step: ProofId,
        literals: &[TermId],
        goal: TermId,
    ) -> Option<ProofId> {
        let TermData::App(Symbol::Named(head), args) = self.ctx.terms.get(goal) else {
            return None;
        };
        if head != "or"
            || args.as_slice() != literals
            || literals.len() != 2
            || literals[0] == literals[1]
        {
            return None;
        }
        let mut remaining = literals.to_vec();
        for &literal in literals {
            emitter.within_budget()?;
            let complement = facts::complement(&mut self.ctx.terms, literal);
            let projection = emitter.proof.add_rule_step(
                AletheRule::OrNeg,
                vec![goal, complement],
                Vec::new(),
                Vec::new(),
            );
            let mut next: Vec<_> = remaining
                .iter()
                .copied()
                .filter(|&item| item != literal)
                .collect();
            if !next.contains(&goal) {
                next.push(goal);
            }
            step = emitter
                .proof
                .add_resolution(next.clone(), literal, step, projection);
            remaining = next;
        }
        (remaining == vec![goal]).then_some(step)
    }
}
