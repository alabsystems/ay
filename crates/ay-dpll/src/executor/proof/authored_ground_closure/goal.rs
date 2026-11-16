// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Negated composite goals: an authored `(not X)` whose `X` the closure
//! proves.
//!
//! A translation-validation query states its claim once, negated, as the
//! last conjunct of one nested root:
//!
//! ```text
//! (assert (and (= p0 e_rdi) .. (not (= true (and (= s30 m42) (= s33 m43) ..)))))
//! ```
//!
//! Every equality under the negation is a consequence of the hypotheses by
//! congruence, but no single literal fact negates any of them, so neither the
//! complementary-fact nor the disequality conflict fires. This module
//! recognizes these bounded composite shapes under the negation, recursively:
//!
//! * a conjunction `(and c1 .. cn)`, proved by `and_neg` once every `ci` is;
//! * a disjunction with a proved child, using `or_neg` and resolution;
//! * an equality with the Boolean constant `true`, `(= true Y)` or
//!   `(= Y true)`, proved by `equiv_neg1` against the `true` axiom once `Y`
//!   is;
//!
//! with leaves that are facts already held, Boolean facts connected through
//! justified congruence, nested-disjunction coverage of an equal guard, or
//! equalities between non-Boolean terms the closure has merged. Boolean
//! coverage uses ordinary `equiv_pos2`, `or_neg` and resolution steps.
//! Every step it emits has a strict validator that re-derives the clause
//! (`validate_and_neg`, `validate_equiv_neg1`, the `true` axiom, resolution),
//! and the candidate is still committed only through the lane's strict gate.

use super::emit::ClosureEmitter;
use super::facts::{FactBase, GroundSearch};
use super::*;

/// Nodes one `holds` query, and the matching emission, may visit.
pub(super) const MAX_GOAL_WORK: usize = 4_096;
/// Nesting depth of one goal formula (the recursion is structural).
pub(super) const MAX_GOAL_DEPTH: usize = 256;

/// Conditional range proposals run only after ordinary closure reasoning.
#[derive(Clone, Copy)]
pub(super) enum GoalPhase {
    Saturating,
    Final,
}

impl Executor {
    /// The body `Y` of `(= true Y)` or `(= Y true)`, when `Y` is Boolean and
    /// not itself the constant.
    pub(super) fn true_equality_body(&self, term: TermId) -> Option<TermId> {
        let (lhs, rhs) = decode_eq_local(&self.ctx.terms, term)?;
        let truth = self.ctx.terms.true_term();
        let body = match (lhs == truth, rhs == truth) {
            (true, false) => rhs,
            (false, true) => lhs,
            _ => return None,
        };
        (*self.ctx.terms.sort(body) == Sort::Bool).then_some(body)
    }

    /// Whether `term` is a composite goal this module proves: a conjunction,
    /// disjunction or equality with `true`. A plain equality ordinarily uses literal-fact propagation; the final
    /// bounded-prefix check also recognizes an already-proved non-Boolean equality.
    fn is_composite_goal(&self, term: TermId) -> bool {
        matches!(self.ctx.terms.get(term), TermData::App(symbol, args)
            if matches!(symbol.name(), "and" | "or") && !args.is_empty())
            || self.true_equality_body(term).is_some()
    }

    /// The leaves of every negated fact: register both sides of each
    /// non-Boolean leaf equality, under a composite goal or negated directly
    /// (`(not (= s0 ((_ extract 31 0) m3)))` as a nested conjunct), so the
    /// closure can merge them and the fact base can refute the fact. A
    /// root-level disequality is registered by `seed_ground_closure`; a
    /// conjunct's never was, so its sides were invisible to the closure.
    /// `None` once the node bound is exceeded.
    pub(super) fn seed_ground_goal_terms(&mut self, search: &mut GroundSearch) -> Option<()> {
        let mut pending: Vec<(TermId, usize)> = Vec::new();
        for fact in search.facts.facts() {
            if let TermData::Not(inner) = self.ctx.terms.get(fact.literal) {
                if self.is_composite_goal(*inner)
                    || decode_eq_local(&self.ctx.terms, *inner).is_some()
                {
                    pending.push((*inner, 0));
                }
            }
        }
        let mut work = MAX_GOAL_WORK;
        let mut sides = Vec::new();
        while let Some((term, depth)) = pending.pop() {
            work = work.checked_sub(1)?;
            if depth > MAX_GOAL_DEPTH {
                return None;
            }
            if let Some(body) = self.true_equality_body(term) {
                pending.push((body, depth + 1));
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(symbol, args) if matches!(symbol.name(), "and" | "or") => {
                    pending.extend(args.iter().map(|&arg| (arg, depth + 1)));
                }
                _ => {
                    if let Some((lhs, rhs)) = decode_eq_local(&self.ctx.terms, term) {
                        if *self.ctx.terms.sort(lhs) != Sort::Bool {
                            sides.extend([lhs, rhs]);
                        }
                    }
                }
            }
        }
        for side in sides {
            self.register_ground_subterms(&mut search.closure, side)?;
        }
        Some(())
    }

    /// The first negated goal fact whose body the closure already proves.
    /// A plain non-Boolean equality uses the same earlier-edge explanation
    /// as a composite equality leaf. This also works at the existing final
    /// prefix check when work refusal precedes literal-fact propagation.
    pub(super) fn negated_goal_conflict(
        &self,
        search: &GroundSearch,
        phase: GoalPhase,
    ) -> Option<ClosureConflict> {
        for (index, fact) in search.facts.facts().iter().enumerate() {
            let TermData::Not(inner) = self.ctx.terms.get(fact.literal) else {
                continue;
            };
            let plain_equality = matches!(phase, GoalPhase::Final)
                && decode_eq_local(&self.ctx.terms, *inner).is_some_and(|(lhs, rhs)| {
                    *self.ctx.terms.sort(lhs) != Sort::Bool
                        && self.ctx.terms.sort(lhs) == self.ctx.terms.sort(rhs)
                });
            if !self.is_composite_goal(*inner) && !plain_equality {
                continue;
            }
            let mut work = MAX_GOAL_WORK;
            if self.ground_goal_holds(search, *inner, 0, &mut work, phase) == Some(true) {
                return Some(ClosureConflict::NegatedGoal { negative: index });
            }
        }
        None
    }

    /// Whether `term` holds: a fact, a conjunction of holding terms, an
    /// equality with `true` whose body holds, a justified Boolean fact or
    /// coverage implication, or a non-Boolean equality whose sides share a class. `None` once the work or depth bound is exceeded.
    fn ground_goal_holds(
        &self,
        search: &GroundSearch,
        term: TermId,
        depth: usize,
        work: &mut usize,
        phase: GoalPhase,
    ) -> Option<bool> {
        self.ground_goal_holds_parts(&search.closure, &search.facts, term, depth, work, phase)
    }

    fn ground_goal_holds_parts(
        &self,
        closure: &GroundClosure,
        facts: &FactBase,
        term: TermId,
        depth: usize,
        work: &mut usize,
        phase: GoalPhase,
    ) -> Option<bool> {
        *work = work.checked_sub(1)?;
        if depth > MAX_GOAL_DEPTH {
            return None;
        }
        if facts.fact_for(term).is_some() {
            return Some(true);
        }
        if self
            .ground_boolean_fact_source_parts(closure, facts, term)
            .is_some()
            || self
                .ground_boolean_coverage_parts(closure, term, work)?
                .is_some()
        {
            return Some(true);
        }

        if let Some(body) = self.true_equality_body(term) {
            return self.ground_goal_holds_parts(closure, facts, body, depth + 1, work, phase);
        }
        if let TermData::App(symbol, args) = self.ctx.terms.get(term) {
            if symbol.name() == "and" {
                for &arg in args {
                    if !self.ground_goal_holds_parts(closure, facts, arg, depth + 1, work, phase)? {
                        return Some(false);
                    }
                }
                return Some(!args.is_empty());
            }
            if symbol.name() == "or" {
                if self
                    .proved_goal_disjunct_for_phase(closure, facts, term, depth, work, phase)?
                    .is_some()
                {
                    return Some(true);
                }
                return Some(match phase {
                    GoalPhase::Saturating => false,
                    GoalPhase::Final => self.ground_read_range_plan(closure, term, work)?.is_some(),
                });
            }
        }
        let Some((lhs, rhs)) = decode_eq_local(&self.ctx.terms, term) else {
            return Some(false);
        };
        let sort = self.ctx.terms.sort(lhs);
        Some(
            *sort != Sort::Bool && sort == self.ctx.terms.sort(rhs) && closure.same_class(lhs, rhs),
        )
    }

    fn proved_goal_disjunct(
        &self,
        closure: &GroundClosure,
        facts: &FactBase,
        term: TermId,
        depth: usize,
        work: &mut usize,
    ) -> Option<Option<TermId>> {
        self.proved_goal_disjunct_for_phase(
            closure,
            facts,
            term,
            depth,
            work,
            GoalPhase::Saturating,
        )
    }

    /// Search only for an already justified member. There is no case split or
    /// interpretation of an unknown disjunct. Every argument slot/type probe
    /// and recursive candidate shares this goal's existing work allowance.
    fn proved_goal_disjunct_for_phase(
        &self,
        closure: &GroundClosure,
        facts: &FactBase,
        term: TermId,
        depth: usize,
        work: &mut usize,
        phase: GoalPhase,
    ) -> Option<Option<TermId>> {
        self.ctx.terms.entry_stamp(term)?;
        if depth > MAX_GOAL_DEPTH {
            return None;
        }
        let TermData::App(Symbol::Named(head), args) = self.ctx.terms.get(term) else {
            return None;
        };
        if head != "or" || self.ctx.terms.sort(term) != &Sort::Bool || args.is_empty() {
            return None;
        }
        *work = work.checked_sub(args.len())?;
        if args.iter().any(|&arg| {
            self.ctx.terms.entry_stamp(arg).is_none() || self.ctx.terms.sort(arg) != &Sort::Bool
        }) {
            return None;
        }
        for &arg in args {
            if self.ground_goal_holds_parts(closure, facts, arg, depth + 1, work, phase)? {
                return Some(Some(arg));
            }
        }
        Some(None)
    }

    /// The unit `(cl term)` for a term [`Self::ground_goal_holds`] accepted,
    /// explained from every edge recorded so far.
    pub(super) fn emit_ground_goal(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        term: TermId,
        depth: usize,
    ) -> Option<DerivedUnit> {
        emitter.within_budget()?;
        if depth > MAX_GOAL_DEPTH {
            return None;
        }
        if let Some(fact) = emitter.facts.fact_for(term) {
            return self.emit_ground_fact(emitter, fact);
        }
        if let Some(source) =
            self.ground_boolean_fact_source_parts(emitter.closure, emitter.facts, term)
        {
            return self.emit_ground_boolean_fact(emitter, term, source);
        }
        if let Some(coverage) = self.ground_boolean_coverage_parts(
            emitter.closure,
            term,
            &mut emitter.disjunction_work,
        )? {
            return self.emit_ground_boolean_coverage(emitter, term, coverage);
        }

        if let Some(body) = self.true_equality_body(term) {
            return self.emit_true_equality(emitter, term, body, depth);
        }
        if let TermData::App(symbol, args) = self.ctx.terms.get(term) {
            if symbol.name() == "and" {
                let args = args.clone();
                return self.emit_goal_conjunction(emitter, term, &args, depth);
            }
            if symbol.name() == "or" {
                if let Some(unit) = self.emit_goal_disjunction(emitter, term, depth)? {
                    return Some(unit);
                }
                if let Some(plan) = self.ground_read_range_plan(
                    emitter.closure,
                    term,
                    &mut emitter.disjunction_work,
                )? {
                    return self.emit_ground_read_range(emitter, plan);
                }
                return None;
            }
        }
        let (lhs, rhs) = decode_eq_local(&self.ctx.terms, term)?;
        if *self.ctx.terms.sort(lhs) == Sort::Bool {
            return None;
        }
        let limit = emitter.closure.edges().len();
        let unit = self.emit_closure_path_unit(emitter, lhs, rhs, limit)?;
        (unit.literal == term).then_some(unit)
    }

    /// An already proved child entails its disjunction by `or_neg` and
    /// resolution. The child is derived from existing facts/closure paths;
    /// neither the guard nor the result is added as an assumption.
    fn emit_goal_disjunction(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        disjunction: TermId,
        depth: usize,
    ) -> Option<Option<DerivedUnit>> {
        // Prefer ordinary proofs across every child, including nested Ors,
        // before considering a conditional range proof. Both passes spend
        // the same remaining candidate allowance; refusal never restarts it.
        for phase in [GoalPhase::Saturating, GoalPhase::Final] {
            let member = match phase {
                GoalPhase::Saturating => self.proved_goal_disjunct(
                    emitter.closure,
                    emitter.facts,
                    disjunction,
                    depth,
                    &mut emitter.disjunction_work,
                )?,
                GoalPhase::Final => self.proved_goal_disjunct_for_phase(
                    emitter.closure,
                    emitter.facts,
                    disjunction,
                    depth,
                    &mut emitter.disjunction_work,
                    phase,
                )?,
            };
            let Some(child) = member else {
                continue;
            };
            let unit = self.emit_ground_goal(emitter, child, depth + 1)?;
            if unit.literal != child {
                return None;
            }
            emitter.admit_steps(2)?;
            let negative = self.ctx.terms.mk_not_raw(child);
            let introduced = emitter.proof.add_rule_step(
                AletheRule::OrNeg,
                vec![disjunction, negative],
                Vec::new(),
                Vec::new(),
            );
            let step =
                emitter
                    .proof
                    .add_resolution(vec![disjunction], child, unit.step, introduced);
            return Some(Some(DerivedUnit {
                literal: disjunction,
                step,
            }));
        }
        Some(None)
    }

    /// `and_neg` over `(and c1 .. cn)`, resolved against each conjunct's unit.
    ///
    /// `and_neg` states one `(not ci)` per conjunct POSITION, so a repeated
    /// conjunct leaves the same literal there more than once and a negated
    /// conjunct `(not x)` leaves the double negation `(not (not x))`. The
    /// strict checker resolves literal SETS decoded by negation parity
    /// (`checker/resolution.rs`), so each DISTINCT conjunct is resolved away
    /// once, with every copy of its negation leaving the clause in that one
    /// step; pinned Carcara accepts both spellings. Two distinct conjuncts
    /// over one atom (`x` beside `(not x)` or `(not (not x))`) would leave or
    /// enter that set together, so that shape is declined.
    fn emit_goal_conjunction(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        conjunction: TermId,
        conjuncts: &[TermId],
        depth: usize,
    ) -> Option<DerivedUnit> {
        let distinct = self.distinct_goal_conjuncts(conjuncts)?;
        let mut units = Vec::with_capacity(distinct.len());
        for &conjunct in &distinct {
            units.push(self.emit_ground_goal(emitter, conjunct, depth + 1)?);
        }
        let mut clause = Vec::with_capacity(conjuncts.len() + 1);
        clause.push(conjunction);
        for &conjunct in conjuncts {
            clause.push(self.ctx.terms.mk_not_raw(conjunct));
        }
        let mut step = emitter.proof.add_rule_step(
            AletheRule::AndNeg,
            clause.clone(),
            Vec::new(),
            // The positive conjunction is already the first clause literal.
            // The strict rule reads that same source without an argument;
            // retaining it again duplicates a potentially huge native payload.
            // The wire printer already omits this bookkeeping argument.
            Vec::new(),
        );
        for unit in units {
            let negated = self.ctx.terms.mk_not_raw(unit.literal);
            let before = clause.len();
            clause.retain(|&literal| literal != negated);
            if clause.len() == before {
                return None;
            }
            step = emitter
                .proof
                .add_resolution(clause.clone(), unit.literal, step, unit.step);
        }
        (clause == [conjunction]).then_some(DerivedUnit {
            step,
            literal: conjunction,
        })
    }

    /// The conjuncts of a goal conjunction, each once in first-occurrence
    /// order, or `None` for an empty conjunction or two distinct conjuncts
    /// over one atom (see [`Self::emit_goal_conjunction`]).
    fn distinct_goal_conjuncts(&self, conjuncts: &[TermId]) -> Option<Vec<TermId>> {
        if conjuncts.is_empty() {
            return None;
        }
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let mut atoms = ay_core::kani_compat::DetHashSet::default();
        let mut distinct = Vec::with_capacity(conjuncts.len());
        for &conjunct in conjuncts {
            if !seen.insert(conjunct) {
                continue;
            }
            let mut atom = conjunct;
            while let TermData::Not(inner) = self.ctx.terms.get(atom) {
                atom = *inner;
            }
            if !atoms.insert(atom) {
                return None;
            }
            distinct.push(conjunct);
        }
        Some(distinct)
    }

    /// `(= true Y)` (either orientation) from the unit `Y`: `equiv_neg1`
    /// gives `(cl (= a b) (not a) (not b))`, and resolving the `true` axiom
    /// and `Y`'s unit leaves the equality.
    fn emit_true_equality(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        equality: TermId,
        body: TermId,
        depth: usize,
    ) -> Option<DerivedUnit> {
        let (lhs, rhs) = decode_eq_local(&self.ctx.terms, equality)?;
        let holds = self.emit_ground_goal(emitter, body, depth + 1)?;
        let truth = self.ctx.terms.true_term();
        let axiom =
            emitter
                .proof
                .add_rule_step(AletheRule::True, vec![truth], Vec::new(), Vec::new());
        let clause = vec![
            equality,
            self.ctx.terms.mk_not_raw(lhs),
            self.ctx.terms.mk_not_raw(rhs),
        ];
        let introduced = emitter.proof.add_rule_step(
            AletheRule::EquivNeg1,
            clause.clone(),
            Vec::new(),
            Vec::new(),
        );
        let truth_unit = DerivedUnit {
            step: axiom,
            literal: truth,
        };
        let step = self.resolve_closure_units(
            emitter,
            introduced,
            clause,
            &[truth_unit, holds],
            &[equality],
        )?;
        Some(DerivedUnit {
            step,
            literal: equality,
        })
    }

    /// The empty clause from the negated composite fact `negative` and the
    /// derivation of its body.
    pub(super) fn emit_negated_goal_conflict(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        negative: usize,
    ) -> Option<()> {
        let refuted = self.emit_ground_fact(emitter, negative)?;
        let TermData::Not(body) = self.ctx.terms.get(refuted.literal) else {
            return None;
        };
        let body = *body;
        let holds = self.emit_ground_goal(emitter, body, 0)?;
        if holds.literal != body {
            return None;
        }
        emitter
            .proof
            .add_resolution(Vec::new(), body, holds.step, refuted.step);
        Some(())
    }
}

#[cfg(test)]
#[path = "tests/actual_e1_local.rs"]
mod actual_e1_local;
