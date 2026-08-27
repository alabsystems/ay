// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authenticated array read-over-write ITE repair.

use super::*;

impl Executor {
    /// Recognize a preprocessor-produced Boolean ITE wrapper around one exact
    /// read-over-write consequence of two authored premises.
    pub(super) fn plan_authored_array_ite(
        &mut self,
        clause: &[TermId],
        originals: &[(TermId, FrontendTerm)],
    ) -> Option<AuthoredArrayItePlan> {
        let [target_or] = clause else {
            return None;
        };
        let target_or = *target_or;
        let TermData::App(Symbol::Named(op), disjuncts) = self.ctx.terms.get(target_or) else {
            return None;
        };
        if op != "or"
            || disjuncts.len() != 2
            || !matches!(self.ctx.terms.sort(target_or), Sort::Bool)
        {
            return None;
        }
        let disjuncts = disjuncts.clone();
        if originals
            .iter()
            .any(|(canonical, _)| *canonical == target_or)
        {
            return None;
        }
        let (array_equality, ite_term) = match (
            self.ctx.terms.get(disjuncts[0]),
            self.ctx.terms.get(disjuncts[1]),
        ) {
            (TermData::Not(equality), TermData::Ite(..)) => (*equality, disjuncts[1]),
            (TermData::Ite(..), TermData::Not(equality)) => (*equality, disjuncts[0]),
            _ => return None,
        };
        let (array_lhs, array_rhs) = decode_binary_equality(&self.ctx.terms, array_equality)?;
        let TermData::Ite(guard, then_branch, else_branch) = self.ctx.terms.get(ite_term).clone()
        else {
            return None;
        };
        if [array_equality, guard, then_branch, else_branch, ite_term]
            .into_iter()
            .any(|term| !matches!(self.ctx.terms.sort(term), Sort::Bool))
        {
            return None;
        }

        // Both discharged units must be immutable authored assertions, not
        // merely terms with a convenient spelling. Re-elaborate each exact
        // `(canonical, parsed)` pair locally before granting premise authority.
        let mut guard_surface = None;
        for required in [array_equality, guard] {
            let mut authenticated = false;
            for (canonical, parsed) in originals {
                if *canonical == required
                    && self.ctx.elaborate_surface_subterm(parsed) == Some(required)
                {
                    authenticated = true;
                    if required == guard {
                        guard_surface = Some(parsed.clone());
                    }
                    break;
                }
            }
            if !authenticated {
                return None;
            }
        }
        let guard_source = self.raw_intern_surface(&guard_surface?)?;
        if !matches!(self.ctx.terms.sort(guard_source), Sort::Bool) {
            return None;
        }
        if guard_source != guard {
            let source_complement = complement_of(&mut self.ctx.terms, guard_source);
            if !self.pair_lemma_valid(guard, source_complement) {
                return None;
            }
        }

        let (guard_lhs, guard_rhs) = decode_binary_equality(&self.ctx.terms, guard)?;
        let (then_lhs, then_rhs) = decode_binary_equality(&self.ctx.terms, then_branch)?;
        let same_pair =
            |a: TermId, b: TermId, c: TermId, d: TermId| (a == c && b == d) || (a == d && b == c);

        // Identify exactly one orientation in which the authored array
        // equality relates an array root to `store(base, i, v)`, the ITE guard
        // equates `i` with the read index, and the then arm equates `v` with a
        // read of that same root.  Ambiguous shapes fail closed.
        let mut shapes = Vec::new();
        for (array, stored) in [(array_lhs, array_rhs), (array_rhs, array_lhs)] {
            let TermData::App(Symbol::Named(store_op), store_args) = self.ctx.terms.get(stored)
            else {
                continue;
            };
            if store_op != "store" || store_args.len() != 3 {
                continue;
            }
            let store_index = store_args[1];
            let store_value = store_args[2];
            for (value, read) in [(then_lhs, then_rhs), (then_rhs, then_lhs)] {
                if value != store_value {
                    continue;
                }
                let TermData::App(Symbol::Named(select_op), select_args) = self.ctx.terms.get(read)
                else {
                    continue;
                };
                if select_op != "select" || select_args.len() != 2 || select_args[0] != array {
                    continue;
                }
                let read_index = select_args[1];
                if !same_pair(guard_lhs, guard_rhs, store_index, read_index) {
                    continue;
                }
                let shape = (stored, store_index, store_value, read, read_index);
                if !shapes.contains(&shape) {
                    shapes.push(shape);
                }
            }
        }
        let [(stored, _store_index, store_value, array_read, read_index)] = shapes.as_slice()
        else {
            return None;
        };
        let (stored, store_value, array_read, read_index) =
            (*stored, *store_value, *array_read, *read_index);

        let not_equality = self.ctx.terms.mk_not_raw(array_equality);
        let not_guard = self.ctx.terms.mk_not_raw(guard);
        if !disjuncts.contains(&not_equality)
            || !matches!(self.ctx.terms.get(not_equality), TermData::Not(inner) if *inner == array_equality)
            || !matches!(self.ctx.terms.get(not_guard), TermData::Not(inner) if *inner == guard)
        {
            return None;
        }
        let stored_read = self.ctx.terms.mk_app(
            Symbol::named("select"),
            [stored, read_index],
            self.ctx.terms.sort(store_value).clone(),
        );
        let select_congruence =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [array_read, stored_read], Sort::Bool);
        let store_hit =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [stored_read, store_value], Sort::Bool);
        let not_select_congruence = self.ctx.terms.mk_not_raw(select_congruence);
        let not_store_hit = self.ctx.terms.mk_not_raw(store_hit);
        let congruence_clause = vec![not_equality, select_congruence];
        let row1_clause = vec![not_guard, store_hit];
        let transitivity_clause = vec![not_select_congruence, not_store_hit, then_branch];

        if ay_proof::recognize_array_theory_lemma(&self.ctx.terms, &congruence_clause)
            != Some(TheoryLemmaKind::ArrayRowChain)
            || ay_proof::recognize_array_select_store(&self.ctx.terms, &row1_clause) != Some(true)
        {
            return None;
        }

        // Plan-time validation uses the same strict fragment checker as the
        // final whole-proof gate. The emitter cannot widen the recognized
        // congruence, conditional ROW1, or transitivity shapes merely by
        // attaching the desired rule tags.
        let mut fragment = Proof::new();
        let congruence = fragment.add_theory_lemma_with_kind(
            "array",
            congruence_clause.clone(),
            TheoryLemmaKind::ArrayRowChain,
        );
        let row1 = fragment.add_theory_lemma_with_kind(
            "array",
            row1_clause.clone(),
            TheoryLemmaKind::ArraySelectStore { index_eq: true },
        );
        let transitivity = fragment.add_rule_step(
            AletheRule::EqTransitive,
            transitivity_clause.clone(),
            Vec::new(),
            Vec::new(),
        );
        let authenticated = ay_proof::authenticate_premise_clauses_strict_with_context(
            &fragment,
            &self.ctx.terms,
            None,
            None,
            &[],
        )
        .ok()?;
        if authenticated.clause(congruence) != Some(congruence_clause.as_slice())
            || authenticated.clause(row1) != Some(row1_clause.as_slice())
            || authenticated.clause(transitivity) != Some(transitivity_clause.as_slice())
        {
            return None;
        }

        Some(AuthoredArrayItePlan {
            target_or,
            array_equality,
            guard_source,
            guard,
            then_branch,
            ite_term,
            select_congruence,
            store_hit,
            congruence_clause,
            row1_clause,
            transitivity_clause,
        })
    }

    /// Emit the strict ROW consequence, discharge its two authored premises,
    /// then lift the resulting then-arm unit through `ite_neg2` and `or_neg`.
    pub(super) fn emit_authored_array_ite(
        &mut self,
        new_proof: &mut Proof,
        plan: &AuthoredArrayItePlan,
        equality_assume: ProofId,
        guard_assume: ProofId,
    ) -> Option<ProofId> {
        let [not_equality, select_congruence]: [TermId; 2] =
            plan.congruence_clause.clone().try_into().ok()?;
        let [not_guard, store_hit]: [TermId; 2] = plan.row1_clause.clone().try_into().ok()?;
        let [not_select_congruence, not_store_hit, then_branch]: [TermId; 3] =
            plan.transitivity_clause.clone().try_into().ok()?;
        if select_congruence != plan.select_congruence
            || store_hit != plan.store_hit
            || then_branch != plan.then_branch
            || !matches!(self.ctx.terms.get(not_equality), TermData::Not(inner) if *inner == plan.array_equality)
            || !matches!(self.ctx.terms.get(not_guard), TermData::Not(inner) if *inner == plan.guard)
            || !matches!(self.ctx.terms.get(not_select_congruence), TermData::Not(inner) if *inner == plan.select_congruence)
            || !matches!(self.ctx.terms.get(not_store_hit), TermData::Not(inner) if *inner == plan.store_hit)
        {
            return None;
        }
        let guard_unit = if plan.guard_source == plan.guard {
            guard_assume
        } else {
            let source_complement = complement_of(&mut self.ctx.terms, plan.guard_source);
            if !self.pair_lemma_valid(plan.guard, source_complement) {
                return None;
            }
            let bridge = Self::add_pair_lemma(new_proof, plan.guard, source_complement);
            new_proof.add_resolution(
                vec![plan.guard],
                atom_of(&self.ctx.terms, plan.guard_source),
                guard_assume,
                bridge,
            )
        };
        let congruence = new_proof.add_theory_lemma_with_kind(
            "array",
            plan.congruence_clause.clone(),
            TheoryLemmaKind::ArrayRowChain,
        );
        let congruence_unit = new_proof.add_resolution(
            vec![plan.select_congruence],
            plan.array_equality,
            congruence,
            equality_assume,
        );
        let row1 = new_proof.add_theory_lemma_with_kind(
            "array",
            plan.row1_clause.clone(),
            TheoryLemmaKind::ArraySelectStore { index_eq: true },
        );
        let store_hit_unit =
            new_proof.add_resolution(vec![plan.store_hit], plan.guard, row1, guard_unit);
        let transitivity = new_proof.add_rule_step(
            AletheRule::EqTransitive,
            plan.transitivity_clause.clone(),
            Vec::new(),
            Vec::new(),
        );
        let without_congruence = new_proof.add_resolution(
            vec![not_store_hit, plan.then_branch],
            plan.select_congruence,
            transitivity,
            congruence_unit,
        );
        let then_unit = new_proof.add_resolution(
            vec![plan.then_branch],
            plan.store_hit,
            without_congruence,
            store_hit_unit,
        );

        let not_then = self.ctx.terms.mk_not_raw(plan.then_branch);
        let ite_neg2 = new_proof.add_rule_step(
            AletheRule::IteNeg2,
            vec![plan.ite_term, not_guard, not_then],
            Vec::new(),
            Vec::new(),
        );
        let ite_without_guard = new_proof.add_resolution(
            vec![plan.ite_term, not_then],
            plan.guard,
            ite_neg2,
            guard_unit,
        );
        let ite_unit = new_proof.add_resolution(
            vec![plan.ite_term],
            plan.then_branch,
            ite_without_guard,
            then_unit,
        );

        let not_ite = self.ctx.terms.mk_not_raw(plan.ite_term);
        let or_neg = new_proof.add_rule_step(
            AletheRule::OrNeg,
            vec![plan.target_or, not_ite],
            Vec::new(),
            Vec::new(),
        );
        Some(new_proof.add_resolution(vec![plan.target_or], plan.ite_term, ite_unit, or_neg))
    }

    /// Recognize the exact Boolean dual of one canonical arithmetic
    /// comparison literal and return its resolution pivot atom.
    pub(super) fn comparison_dual_source_literal(
        &mut self,
        source: TermId,
        target: TermId,
    ) -> Option<TermId> {
        let (source_atom, negated) = match self.ctx.terms.get(source) {
            TermData::Not(atom) => (*atom, true),
            _ => (source, false),
        };
        let TermData::App(Symbol::Named(head), args) = self.ctx.terms.get(source_atom) else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }
        let head = head.clone();
        let args = args.clone();
        let (dual_head, swap) = match head.as_str() {
            "<" => ("<=", true),
            "<=" => ("<", true),
            ">" => ("<=", false),
            ">=" => ("<", false),
            _ => return None,
        };
        if self.ctx.terms.sort(args[0]) != self.ctx.terms.sort(args[1])
            || !matches!(self.ctx.terms.sort(args[0]), Sort::Int | Sort::Real)
            || !matches!(self.ctx.terms.sort(source), Sort::Bool)
            || !matches!(self.ctx.terms.sort(target), Sort::Bool)
        {
            return None;
        }
        let (lhs, rhs) = if swap {
            (args[1], args[0])
        } else {
            (args[0], args[1])
        };
        let dual_atom = self
            .ctx
            .terms
            .mk_app(Symbol::named(dual_head), [lhs, rhs], Sort::Bool);
        let exact_target = if negated {
            dual_atom
        } else {
            self.ctx.terms.mk_not_raw(dual_atom)
        };
        if exact_target != target {
            return None;
        }
        let source_complement = complement_of(&mut self.ctx.terms, source);
        self.pair_lemma_valid(target, source_complement)
            .then_some(source_atom)
    }
}
