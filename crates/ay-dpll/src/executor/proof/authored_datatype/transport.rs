// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Selector-transport refutation for the authored datatype planner: carry
//! an authored constructor equality through a (possibly nested) selector
//! chain and close the authored selector disequality.

use super::super::*;
use super::{append_owned_leaf, projected_field, OwnedLeaf};

impl Executor {
    /// Try the selector-transport rebuild over the collected authored
    /// leaves. `true` when a strict-checked candidate replaced `proof`
    /// (the caller then keeps its synthesized-root registration).
    pub(super) fn try_authored_selector_transport(
        &mut self,
        proof: &mut Proof,
        candidate_scope: &[TermId],
        leaves: &[OwnedLeaf],
        selector_decls: &[(String, Vec<String>)],
    ) -> bool {
        for source_leaf in leaves {
            let Some((source_left, source_right)) =
                decode_eq_local(&self.ctx.terms, source_leaf.term)
            else {
                continue;
            };
            for (subject, constructor) in [(source_left, source_right), (source_right, source_left)]
            {
                if !matches!(
                    self.ctx.terms.get(constructor),
                    TermData::App(Symbol::Named(_), _)
                ) {
                    continue;
                }
                for goal_leaf in leaves {
                    let TermData::Not(goal_inner) = self.ctx.terms.get(goal_leaf.term).clone()
                    else {
                        continue;
                    };
                    // Direct selector disequality, or a negated conjunction
                    // with the selector equality as one conjunct (the P22
                    // shape: `not (and <ground BV equality> <selector
                    // equality>)`); sibling conjuncts are discharged at
                    // closing time below.
                    let mut goal_options: Vec<(TermId, Option<Vec<TermId>>)> = Vec::new();
                    if decode_eq_local(&self.ctx.terms, goal_inner).is_some() {
                        goal_options.push((goal_inner, None));
                    } else if let TermData::App(symbol @ Symbol::Named(_), conjuncts) =
                        self.ctx.terms.get(goal_inner).clone()
                    {
                        if symbol.name() == "and" {
                            for &conjunct in &conjuncts {
                                if decode_eq_local(&self.ctx.terms, conjunct).is_some() {
                                    goal_options.push((conjunct, Some(conjuncts.clone())));
                                }
                            }
                        }
                    }
                    for (goal_equality, and_conjuncts) in goal_options {
                        let Some((goal_left, goal_right)) =
                            decode_eq_local(&self.ctx.terms, goal_equality)
                        else {
                            continue;
                        };
                        for (selector_term, field_value) in
                            [(goal_left, goal_right), (goal_right, goal_left)]
                        {
                            // Replay solvers may already carry the
                            // selector equality as a positive authored
                            // leaf (P22's transformed shape); then no
                            // chain derivation is needed — close
                            // directly against that leaf.
                            if let Some(positive_leaf) =
                                leaves.iter().find(|leaf| leaf.term == goal_equality)
                            {
                                // Purely additive shortcut: any failure
                                // here falls through to the chain
                                // derivation below, as before this route
                                // existed.
                                let mut candidate = Proof::new();
                                let direct = append_owned_leaf(
                                    &mut self.ctx.terms,
                                    &mut candidate,
                                    goal_leaf,
                                )
                                .and_then(|goal_unit| {
                                    append_owned_leaf(
                                        &mut self.ctx.terms,
                                        &mut candidate,
                                        positive_leaf,
                                    )
                                    .map(|goal| (goal, goal_unit))
                                });
                                if let Some((goal, goal_unit)) = direct {
                                    if self.close_transport_goal(
                                        &mut candidate,
                                        goal_equality,
                                        goal,
                                        goal_unit,
                                        and_conjuncts.as_deref(),
                                        leaves,
                                    ) && ay_proof::validate_reachable_assumes_in_problem_scope(
                                        &candidate,
                                        candidate_scope,
                                    )
                                    .is_ok()
                                        && Self::proof_derives_empty_clause(&candidate)
                                        && self
                                            .check_proof_strict_with_datatypes(&candidate)
                                            .is_ok()
                                    {
                                        *proof = candidate;
                                        return true;
                                    }
                                }
                            }
                            // Collect the selector chain from the outermost
                            // application down to `subject`, innermost first.
                            // Length 1 is the direct transport; longer chains
                            // come from nested records (`case (f x)` with
                            // `x = mk (g 0)`), needing one congruence +
                            // projection pair per selector.
                            let mut chain: Vec<(Symbol, TermId)> = Vec::new();
                            let mut cursor = selector_term;
                            let chain_complete = loop {
                                if cursor == subject {
                                    break !chain.is_empty();
                                }
                                let TermData::App(symbol @ Symbol::Named(_), args) =
                                    self.ctx.terms.get(cursor).clone()
                                else {
                                    break false;
                                };
                                if args.len() != 1 || chain.len() >= 8 {
                                    break false;
                                }
                                chain.push((symbol, cursor));
                                cursor = args[0];
                            };
                            if !chain_complete {
                                continue;
                            }
                            chain.reverse();

                            // Walk the constructor side through each
                            // intermediate selector to learn the projected
                            // field values the strict recognizer will demand.
                            let mut intermediate_values: Vec<TermId> = Vec::new();
                            let mut constructor_cursor = constructor;
                            let mut projection_known = true;
                            for (symbol, _) in &chain[..chain.len() - 1] {
                                let Some(value) = projected_field(
                                    &self.ctx.terms,
                                    selector_decls,
                                    symbol.name(),
                                    constructor_cursor,
                                ) else {
                                    projection_known = false;
                                    break;
                                };
                                intermediate_values.push(value);
                                constructor_cursor = value;
                            }
                            if !projection_known {
                                continue;
                            }

                            let (outer_symbol, _) = chain[chain.len() - 1].clone();
                            let selector_sort = self.ctx.terms.sort(selector_term).clone();
                            let selector_constructor = self.ctx.terms.mk_app(
                                outer_symbol,
                                [constructor_cursor],
                                selector_sort,
                            );
                            let projection_equality = self.ctx.terms.mk_app(
                                Symbol::named("="),
                                [selector_constructor, field_value],
                                Sort::Bool,
                            );
                            if !ay_proof::recognize_datatype_selector_project(
                                &self.ctx.terms,
                                &[projection_equality],
                                selector_decls,
                            ) {
                                continue;
                            }
                            let congruence_equality = self.ctx.terms.mk_app(
                                Symbol::named("="),
                                [selector_term, selector_constructor],
                                Sort::Bool,
                            );

                            let mut candidate = Proof::new();
                            let Some(source_unit) =
                                append_owned_leaf(&mut self.ctx.terms, &mut candidate, source_leaf)
                            else {
                                continue;
                            };
                            let Some(goal_unit) =
                                append_owned_leaf(&mut self.ctx.terms, &mut candidate, goal_leaf)
                            else {
                                continue;
                            };
                            // Derive `subterm = projected value` for each
                            // intermediate selector in turn, so the final
                            // transport starts from an equality whose left
                            // side is the outermost selector's argument.
                            let mut current_equality = source_leaf.term;
                            let mut current_unit = source_unit;
                            let mut current_constructor = constructor;
                            let mut chain_closed = true;
                            for ((symbol, subterm), value) in chain[..chain.len() - 1]
                                .iter()
                                .zip(intermediate_values.iter().copied())
                            {
                                let subterm_sort = self.ctx.terms.sort(*subterm).clone();
                                let sub_constructor = self.ctx.terms.mk_app(
                                    symbol.clone(),
                                    [current_constructor],
                                    subterm_sort,
                                );
                                let sub_congruence_equality = self.ctx.terms.mk_app(
                                    Symbol::named("="),
                                    [*subterm, sub_constructor],
                                    Sort::Bool,
                                );
                                let sub_projection_equality = self.ctx.terms.mk_app(
                                    Symbol::named("="),
                                    [sub_constructor, value],
                                    Sort::Bool,
                                );
                                if !ay_proof::recognize_datatype_selector_project(
                                    &self.ctx.terms,
                                    &[sub_projection_equality],
                                    selector_decls,
                                ) {
                                    chain_closed = false;
                                    break;
                                }
                                let derived_equality = self.ctx.terms.mk_app(
                                    Symbol::named("="),
                                    [*subterm, value],
                                    Sort::Bool,
                                );
                                let sub_congruence = candidate.add_rule_step(
                                    AletheRule::EqCongruent,
                                    vec![
                                        self.ctx.terms.mk_not_raw(current_equality),
                                        sub_congruence_equality,
                                    ],
                                    Vec::new(),
                                    Vec::new(),
                                );
                                let sub_congruence_unit = candidate.add_resolution(
                                    vec![sub_congruence_equality],
                                    current_equality,
                                    sub_congruence,
                                    current_unit,
                                );
                                let sub_projection = candidate.add_theory_lemma_with_kind(
                                    "datatype",
                                    vec![sub_projection_equality],
                                    TheoryLemmaKind::DatatypeSelectorProject,
                                );
                                let sub_transitivity = candidate.add_rule_step(
                                    AletheRule::EqTransitive,
                                    vec![
                                        self.ctx.terms.mk_not_raw(sub_congruence_equality),
                                        self.ctx.terms.mk_not_raw(sub_projection_equality),
                                        derived_equality,
                                    ],
                                    Vec::new(),
                                    Vec::new(),
                                );
                                let sub_residual = candidate.add_resolution(
                                    vec![
                                        self.ctx.terms.mk_not_raw(sub_projection_equality),
                                        derived_equality,
                                    ],
                                    sub_congruence_equality,
                                    sub_transitivity,
                                    sub_congruence_unit,
                                );
                                current_unit = candidate.add_resolution(
                                    vec![derived_equality],
                                    sub_projection_equality,
                                    sub_residual,
                                    sub_projection,
                                );
                                current_equality = derived_equality;
                                current_constructor = value;
                            }
                            if !chain_closed || current_constructor != constructor_cursor {
                                continue;
                            }
                            let congruence = candidate.add_rule_step(
                                AletheRule::EqCongruent,
                                vec![
                                    self.ctx.terms.mk_not_raw(current_equality),
                                    congruence_equality,
                                ],
                                Vec::new(),
                                Vec::new(),
                            );
                            let congruence_unit = candidate.add_resolution(
                                vec![congruence_equality],
                                current_equality,
                                congruence,
                                current_unit,
                            );
                            let projection = candidate.add_theory_lemma_with_kind(
                                "datatype",
                                vec![projection_equality],
                                TheoryLemmaKind::DatatypeSelectorProject,
                            );
                            let transitivity = candidate.add_rule_step(
                                AletheRule::EqTransitive,
                                vec![
                                    self.ctx.terms.mk_not_raw(congruence_equality),
                                    self.ctx.terms.mk_not_raw(projection_equality),
                                    goal_equality,
                                ],
                                Vec::new(),
                                Vec::new(),
                            );
                            let residual = candidate.add_resolution(
                                vec![
                                    self.ctx.terms.mk_not_raw(projection_equality),
                                    goal_equality,
                                ],
                                congruence_equality,
                                transitivity,
                                congruence_unit,
                            );
                            let goal = candidate.add_resolution(
                                vec![goal_equality],
                                projection_equality,
                                residual,
                                projection,
                            );
                            // Close against the goal leaf. Direct disequality:
                            // one resolution. Negated conjunction: `NotAnd`
                            // splits the leaf into negated conjuncts, the
                            // transport unit discharges the selector conjunct,
                            // and each sibling must be independently derivable
                            // (reflexivity, or a BV/LIA double-negation lemma
                            // whose root is the sibling's negation — the strict
                            // checker re-derives either, so an underivable
                            // sibling simply fails the candidate gates below by
                            // never reaching them).
                            let siblings_closed = self.close_transport_goal(
                                &mut candidate,
                                goal_equality,
                                goal,
                                goal_unit,
                                and_conjuncts.as_deref(),
                                leaves,
                            );
                            if !siblings_closed {
                                continue;
                            }
                            if ay_proof::validate_reachable_assumes_in_problem_scope(
                                &candidate,
                                candidate_scope,
                            )
                            .is_ok()
                                && Self::proof_derives_empty_clause(&candidate)
                                && self.check_proof_strict_with_datatypes(&candidate).is_ok()
                            {
                                // Install keeps the synthesized-root
                                // registration made above, so the authored
                                // spelling restoration can resolve each
                                // synthesized assume as a raw identity root.
                                *proof = candidate;
                                return true;
                            }
                        }
                    }
                }
            }
        }
        false
    }

    /// Close a candidate against its goal leaf once the selector
    /// equality unit exists (derived by transport or already an
    /// authored leaf). Direct disequality: one resolution. Negated
    /// conjunction: `NotAnd` splits the leaf, the selector unit
    /// discharges its conjunct, and each sibling must be independently
    /// derivable (a positive authored leaf, reflexivity, or a BV/LIA
    /// double-negation lemma).
    fn close_transport_goal(
        &mut self,
        candidate: &mut Proof,
        goal_equality: TermId,
        goal: ProofId,
        goal_unit: ProofId,
        and_conjuncts: Option<&[TermId]>,
        leaves: &[OwnedLeaf],
    ) -> bool {
        let mut siblings_closed = true;
        match and_conjuncts {
            None => {
                candidate.add_resolution(Vec::new(), goal_equality, goal, goal_unit);
            }
            Some(conjuncts) => {
                let negatives: Vec<TermId> = conjuncts
                    .iter()
                    .map(|&conjunct| self.ctx.terms.mk_not_raw(conjunct))
                    .collect();
                let mut running = negatives.clone();
                let mut current = candidate.add_rule_step(
                    AletheRule::NotAnd,
                    running.clone(),
                    vec![goal_unit],
                    Vec::new(),
                );
                let not_goal = self.ctx.terms.mk_not_raw(goal_equality);
                match running.iter().position(|&literal| literal == not_goal) {
                    Some(position) => {
                        let _ = running.remove(position);
                        current =
                            candidate.add_resolution(running.clone(), goal_equality, goal, current);
                    }
                    None => siblings_closed = false,
                }
                if siblings_closed {
                    for &sibling in conjuncts.iter().filter(|&&c| c != goal_equality) {
                        let not_sibling = self.ctx.terms.mk_not_raw(sibling);
                        let Some(position) =
                            running.iter().position(|&literal| literal == not_sibling)
                        else {
                            siblings_closed = false;
                            break;
                        };
                        let Some((discharge, pivot)) =
                            self.discharge_transport_sibling(candidate, sibling, leaves)
                        else {
                            siblings_closed = false;
                            break;
                        };
                        let _ = running.remove(position);
                        current =
                            candidate.add_resolution(running.clone(), pivot, current, discharge);
                    }
                }
                if !running.is_empty() {
                    siblings_closed = false;
                }
                let _ = current;
            }
        }
        siblings_closed
    }

    /// One proof step establishing a sibling conjunct, with the literal
    /// the caller resolves on: a positive authored leaf or reflexivity
    /// proves the sibling itself; the BV/LIA double-negation lemma proves
    /// `¬¬sibling`, so its pivot is `¬sibling`.
    fn discharge_transport_sibling(
        &mut self,
        candidate: &mut Proof,
        sibling: TermId,
        leaves: &[OwnedLeaf],
    ) -> Option<(ProofId, TermId)> {
        if let Some(sibling_leaf) = leaves.iter().find(|leaf| leaf.term == sibling) {
            let discharge = append_owned_leaf(&mut self.ctx.terms, candidate, sibling_leaf)?;
            return Some((discharge, sibling));
        }
        if matches!(
            decode_eq_local(&self.ctx.terms, sibling),
            Some((left, right)) if left == right
        ) {
            let discharge = candidate.add_rule_step(
                AletheRule::EqReflexive,
                vec![sibling],
                Vec::new(),
                Vec::new(),
            );
            return Some((discharge, sibling));
        }
        let not_sibling = self.ctx.terms.mk_not_raw(sibling);
        let double_neg = self.ctx.terms.mk_not_raw(not_sibling);
        if !matches!(
            self.ctx.terms.get(double_neg),
            TermData::Not(inner) if *inner == not_sibling
        ) {
            return None;
        }
        let lemma = candidate.add_theory_lemma_with_kind(
            "BV/LIA",
            vec![double_neg],
            TheoryLemmaKind::BvLiaTautology,
        );
        Some((lemma, not_sibling))
    }
}
