// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Rebuild `¬g` plus `g ∨ ¬E` when exact linear roots imply `E`.
    ///
    /// This is the standalone expression-split lane: the Boolean branch is
    /// closed propositionally, while the arithmetic branch is discharged by
    /// two independently checked Farkas implications and
    /// `la_disequality`. Only a binary authored disjunction and an exact
    /// complementary guard literal are accepted.
    ///
    /// # Entry gate
    ///
    /// The lane declines on [`Self::authored_cascade_publishable`], NOT on a
    /// bare strict check. MEASURED on the #6660 standalone expression-split
    /// fixture, which is the exact shape this lane was written for: the
    /// arithmetic branch's blocking clause is recorded as
    /// `ArithClauseTautology`, a kind AY's strict checker RE-DERIVES (through
    /// `nia_linear_ideal`) and the pinned Alethe wire cannot spell. The
    /// document is therefore strict-OK and still prints `:rule hole`, so a
    /// bare `check_proof_strict_with_datatypes(..).is_ok()` returned here and
    /// the lane never ran on the one family it exists to serve. The
    /// publishable predicate is the cascade's own — `!wire_gap &&
    /// strict-complete` — and is the same convention `RepairEntry::Check`
    /// already encodes for the conjunct and equality-chain members. The commit
    /// gate is unchanged, so this widens only WHEN the lane may try, never
    /// what it may commit.
    pub(super) fn replace_with_exact_authored_guarded_linear_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        const MAX_LINEAR_ROOTS: usize = 12;
        const MAX_FARKAS_ROOTS: usize = 6;

        if self.authored_cascade_publishable(proof) {
            return;
        }
        let authored = self.exact_concrete_authored_scope();

        fn numeric_atom(terms: &TermStore, root: TermId) -> bool {
            let atom = match terms.get(root) {
                TermData::Not(inner) => *inner,
                _ => root,
            };
            let TermData::App(Symbol::Named(operator), args) = terms.get(atom) else {
                return false;
            };
            args.len() == 2
                && matches!(operator.as_str(), "=" | "<" | "<=" | ">" | ">=")
                && args
                    .iter()
                    .all(|&arg| matches!(terms.sort(arg), Sort::Int | Sort::Real))
        }

        fn farkas_for_implication(
            terms: &mut TermStore,
            roots: &[TermId],
            conclusion: TermId,
        ) -> Option<(Vec<TermId>, FarkasAnnotation)> {
            let mut clause: Vec<TermId> =
                roots.iter().map(|&root| terms.mk_not_raw(root)).collect();
            clause.push(conclusion);
            let mut farkas = None;
            let mut inferred = TheoryLemmaKind::Generic;
            if !super::super::proof_farkas::try_lra_farkas_reconstruction(
                terms,
                &clause,
                &mut farkas,
                &mut inferred,
            ) {
                return None;
            }
            Some((clause, farkas?))
        }

        fn append_implication(
            terms: &mut TermStore,
            candidate: &mut Proof,
            roots: &[TermId],
            premise_ids: &[ProofId],
            clause: Vec<TermId>,
            farkas: FarkasAnnotation,
            conclusion: TermId,
        ) -> Option<ProofId> {
            let mut current = candidate.add_step(ProofStep::TheoryLemma {
                theory: "LRA".to_string(),
                clause: clause.clone(),
                farkas: Some(farkas),
                kind: TheoryLemmaKind::LraFarkas,
                lia: None,
            });
            let mut residual = clause;
            for (&root, &premise) in roots.iter().zip(premise_ids.iter()) {
                let complement = terms.mk_not_raw(root);
                let position = residual.iter().position(|&lit| lit == complement)?;
                let _ = residual.remove(position);
                current = candidate.add_resolution(residual.clone(), root, current, premise);
            }
            (residual == [conclusion]).then_some(current)
        }

        for &or_root in &authored {
            let TermData::App(Symbol::Named(operator), disjuncts) =
                self.ctx.terms.get(or_root).clone()
            else {
                continue;
            };
            if operator != "or" || disjuncts.len() != 2 {
                continue;
            }

            for guard_index in 0..2 {
                let guard = disjuncts[guard_index];
                let negative_goal = disjuncts[1 - guard_index];
                let guard_atom = match self.ctx.terms.get(guard) {
                    TermData::Not(inner) => *inner,
                    _ => guard,
                };
                if !matches!(self.ctx.terms.get(guard_atom), TermData::Var(..))
                    || !matches!(self.ctx.terms.sort(guard_atom), Sort::Bool)
                {
                    continue;
                }
                let Some(&guard_complement) = authored.iter().find(|&&root| {
                    matches!(
                        (self.ctx.terms.get(guard), self.ctx.terms.get(root)),
                        (TermData::Not(inner), _) if *inner == root
                    ) || matches!(
                        (self.ctx.terms.get(guard), self.ctx.terms.get(root)),
                        (_, TermData::Not(inner)) if *inner == guard
                    )
                }) else {
                    continue;
                };
                let TermData::Not(canonical_goal_equality) = self.ctx.terms.get(negative_goal)
                else {
                    continue;
                };
                let canonical_goal_equality = *canonical_goal_equality;
                let Some((canonical_goal_lhs, canonical_goal_rhs)) =
                    decode_eq_local(&self.ctx.terms, canonical_goal_equality)
                else {
                    continue;
                };
                if !matches!(
                    self.ctx.terms.sort(canonical_goal_lhs),
                    Sort::Int | Sort::Real
                ) || self.ctx.terms.sort(canonical_goal_lhs)
                    != self.ctx.terms.sort(canonical_goal_rhs)
                {
                    continue;
                }

                let linear_roots: Vec<TermId> = authored
                    .iter()
                    .copied()
                    .filter(|&root| root != or_root && root != guard_complement)
                    .filter(|&root| numeric_atom(&self.ctx.terms, root))
                    .collect();
                if linear_roots.is_empty() || linear_roots.len() > MAX_LINEAR_ROOTS {
                    continue;
                }
                // Equality elaboration is allowed to orient a commutative
                // equality differently from its authored spelling.  Alethe's
                // `la_disequality` is position-sensitive, so using the
                // canonical equality with a surface override can print an
                // invalid split even though the in-memory split is valid.
                // Try the surface orientation first and authenticate the
                // resulting raw `or` root against the exact parsed-source
                // roots captured by the original-rebuild pass.  No merely
                // equivalent formula is admitted.
                let flipped_goal_equality = self.ctx.terms.mk_app(
                    Symbol::named("="),
                    [canonical_goal_rhs, canonical_goal_lhs],
                    Sort::Bool,
                );
                for goal_equality in [flipped_goal_equality, canonical_goal_equality] {
                    if goal_equality == canonical_goal_equality
                        && self
                            .last_proof_term_overrides
                            .as_ref()
                            .is_some_and(|overrides| overrides.contains_key(&goal_equality))
                    {
                        // A raw source orientation must be found instead; an
                        // override on this equality can invalidate the rigid
                        // printed operand order.
                        continue;
                    }
                    let Some((goal_lhs, goal_rhs)) =
                        decode_eq_local(&self.ctx.terms, goal_equality)
                    else {
                        continue;
                    };
                    let surface_negative_goal = self.ctx.terms.mk_not_raw(goal_equality);
                    let mut surface_disjuncts = disjuncts.clone();
                    surface_disjuncts[1 - guard_index] = surface_negative_goal;
                    let surface_or_root = self.ctx.terms.mk_app(
                        Symbol::named("or"),
                        surface_disjuncts.clone(),
                        Sort::Bool,
                    );
                    let exact_surface_root = surface_or_root == or_root
                        || self.last_proof_rebuild_originals.contains(&surface_or_root);
                    if !exact_surface_root
                        || self
                            .last_proof_term_overrides
                            .as_ref()
                            .is_some_and(|overrides| {
                                overrides.contains_key(&goal_equality)
                                    || overrides.contains_key(&surface_negative_goal)
                                    || overrides.contains_key(&surface_or_root)
                            })
                    {
                        continue;
                    }
                    let mut candidate_scope = authored.clone();
                    if !candidate_scope.contains(&surface_or_root) {
                        candidate_scope.push(surface_or_root);
                    }

                    let forward = self.ctx.terms.mk_app(
                        Symbol::named("<="),
                        [goal_lhs, goal_rhs],
                        Sort::Bool,
                    );
                    let reverse = self.ctx.terms.mk_app(
                        Symbol::named("<="),
                        [goal_rhs, goal_lhs],
                        Sort::Bool,
                    );
                    let limit = 1_u64 << linear_roots.len();
                    for cardinality in 1..=MAX_FARKAS_ROOTS.min(linear_roots.len()) {
                        for mask in 1_u64..limit {
                            if mask.count_ones() as usize != cardinality {
                                continue;
                            }
                            let selected: Vec<TermId> = linear_roots
                                .iter()
                                .enumerate()
                                .filter_map(|(index, &root)| {
                                    ((mask & (1_u64 << index)) != 0).then_some(root)
                                })
                                .collect();
                            let Some((forward_clause, forward_farkas)) =
                                farkas_for_implication(&mut self.ctx.terms, &selected, forward)
                            else {
                                continue;
                            };
                            let Some((reverse_clause, reverse_farkas)) =
                                farkas_for_implication(&mut self.ctx.terms, &selected, reverse)
                            else {
                                continue;
                            };

                            let mut candidate = Proof::new();
                            let premise_ids: Vec<ProofId> = selected
                                .iter()
                                .map(|&root| candidate.add_assume(root, None))
                                .collect();
                            let guard_assume = candidate.add_assume(guard_complement, None);
                            let or_assume = candidate.add_assume(surface_or_root, None);
                            let Some(forward_unit) = append_implication(
                                &mut self.ctx.terms,
                                &mut candidate,
                                &selected,
                                &premise_ids,
                                forward_clause,
                                forward_farkas,
                                forward,
                            ) else {
                                continue;
                            };
                            let Some(reverse_unit) = append_implication(
                                &mut self.ctx.terms,
                                &mut candidate,
                                &selected,
                                &premise_ids,
                                reverse_clause,
                                reverse_farkas,
                                reverse,
                            ) else {
                                continue;
                            };
                            let not_forward = self.ctx.terms.mk_not_raw(forward);
                            let not_reverse = self.ctx.terms.mk_not_raw(reverse);
                            let split = self.ctx.terms.mk_app(
                                Symbol::named("or"),
                                [goal_equality, not_forward, not_reverse],
                                Sort::Bool,
                            );
                            let split_unit = candidate.add_rule_step(
                                AletheRule::LaDisequality,
                                vec![split],
                                Vec::new(),
                                Vec::new(),
                            );
                            let split_clause = candidate.add_rule_step(
                                AletheRule::Or,
                                vec![goal_equality, not_forward, not_reverse],
                                vec![split_unit],
                                Vec::new(),
                            );
                            let forward_resolved = candidate.add_resolution(
                                vec![goal_equality, not_reverse],
                                forward,
                                split_clause,
                                forward_unit,
                            );
                            let equality_unit = candidate.add_resolution(
                                vec![goal_equality],
                                reverse,
                                forward_resolved,
                                reverse_unit,
                            );
                            let or_clause = candidate.add_rule_step(
                                AletheRule::Or,
                                surface_disjuncts.clone(),
                                vec![or_assume],
                                Vec::new(),
                            );
                            let negative_goal_unit = candidate.add_resolution(
                                vec![surface_negative_goal],
                                guard_atom,
                                or_clause,
                                guard_assume,
                            );
                            candidate.add_resolution(
                                Vec::new(),
                                goal_equality,
                                equality_unit,
                                negative_goal_unit,
                            );

                            if ay_proof::validate_reachable_assumes_in_problem_scope(
                                &candidate,
                                &candidate_scope,
                            )
                            .is_ok()
                                && Self::proof_derives_empty_clause(&candidate)
                                && self.check_proof_strict_with_datatypes(&candidate).is_ok()
                            {
                                *proof = candidate;
                                return;
                            }
                        }
                    }
                }
            }
        }
    }
}
