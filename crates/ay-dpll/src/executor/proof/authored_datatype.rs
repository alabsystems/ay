// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Rebuild an exact datatype projection/tester contradiction from public
    /// query roots, including native-API assertions that have no parsed
    /// SMT-LIB surface.
    ///
    /// The datatype solver can close `selector(C(args)) != arg_i` and
    /// `not (is-C (C(args)))` through an implicit datatype theorem, leaving a
    /// Generic proof leaf.  Reconstruct the theorem explicitly and accept it
    /// only through the strict checker's declaration-backed recognizer.  The
    /// contradictory premise must be an exact authored root; no live solver
    /// axiom or simplified surrogate is eligible.
    pub(super) fn replace_with_exact_authored_datatype_refutation(&mut self, proof: &mut Proof) {
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        let datatype_decls = self.datatype_decls_for_strict_proof();
        let selector_decls = self.ctor_selector_decls_for_strict_proof();
        if datatype_decls.is_empty() && selector_decls.is_empty() {
            return;
        }

        for &root in &authored {
            let (theorem, pivot) = match self.ctx.terms.get(root) {
                TermData::Not(inner) => (*inner, *inner),
                _ => (self.ctx.terms.mk_not_raw(root), root),
            };
            let kind = if !selector_decls.is_empty()
                && ay_proof::recognize_datatype_selector_project(
                    &self.ctx.terms,
                    &[theorem],
                    &selector_decls,
                ) {
                TheoryLemmaKind::DatatypeSelectorProject
            } else if !datatype_decls.is_empty()
                && ay_proof::recognize_datatype_tester_eval(
                    &self.ctx.terms,
                    &[theorem],
                    &datatype_decls,
                )
            {
                TheoryLemmaKind::DatatypeTesterEval
            } else {
                continue;
            };

            let mut candidate = Proof::new();
            let premise = candidate.add_assume(root, None);
            let lemma = candidate.add_theory_lemma_with_kind("datatype", vec![theorem], kind);
            candidate.add_resolution(Vec::new(), pivot, premise, lemma);
            if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_ok()
                && Self::proof_derives_empty_clause(&candidate)
                && self.check_proof_strict_with_datatypes(&candidate).is_ok()
            {
                *proof = candidate;
                return;
            }
        }

        #[derive(Clone)]
        struct OwnedLeaf {
            root: TermId,
            path: Vec<u32>,
            term: TermId,
        }

        fn collect_leaves(
            terms: &TermStore,
            root: TermId,
            term: TermId,
            path: &mut Vec<u32>,
            out: &mut Vec<OwnedLeaf>,
        ) {
            if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
                if name == "and" {
                    for (index, &child) in args.iter().enumerate() {
                        path.push(index as u32);
                        collect_leaves(terms, root, child, path, out);
                        path.pop();
                    }
                    return;
                }
            }
            out.push(OwnedLeaf {
                root,
                path: path.clone(),
                term,
            });
        }

        fn append_owned_leaf(
            terms: &mut TermStore,
            proof: &mut Proof,
            leaf: &OwnedLeaf,
        ) -> Option<ProofId> {
            let mut current = proof.add_assume(leaf.root, None);
            let mut current_term = leaf.root;
            for &position in &leaf.path {
                let TermData::App(Symbol::Named(name), args) = terms.get(current_term) else {
                    return None;
                };
                if name != "and" {
                    return None;
                }
                let child = *args.get(position as usize)?;
                let projection = proof.add_rule_step(
                    AletheRule::AndPos(position),
                    vec![terms.mk_not_raw(current_term), child],
                    Vec::new(),
                    vec![current_term],
                );
                current = proof.add_resolution(vec![child], current_term, projection, current);
                current_term = child;
            }
            (current_term == leaf.term).then_some(current)
        }

        fn tester_subject(terms: &TermStore, term: TermId) -> Option<TermId> {
            let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
                return None;
            };
            (name.starts_with("is-") && args.len() == 1 && terms.sort(term) == &Sort::Bool)
                .then_some(args[0])
        }

        let mut leaves = Vec::new();
        for &root in &authored {
            collect_leaves(&self.ctx.terms, root, root, &mut Vec::new(), &mut leaves);
        }

        // Two positive tester premises over one opaque value contradict the
        // declaration-backed mutual-exclusion theorem.
        if !datatype_decls.is_empty() {
            for (left_index, left) in leaves.iter().enumerate() {
                let Some(left_subject) = tester_subject(&self.ctx.terms, left.term) else {
                    continue;
                };
                for right in leaves.iter().skip(left_index + 1) {
                    if tester_subject(&self.ctx.terms, right.term) != Some(left_subject) {
                        continue;
                    }
                    let not_left = self.ctx.terms.mk_not_raw(left.term);
                    let not_right = self.ctx.terms.mk_not_raw(right.term);
                    let theorem = vec![not_left, not_right];
                    if !ay_proof::recognize_datatype_tester_eval_with_selectors(
                        &self.ctx.terms,
                        &theorem,
                        &datatype_decls,
                        &selector_decls,
                    ) {
                        continue;
                    }
                    let mut candidate = Proof::new();
                    let Some(left_unit) =
                        append_owned_leaf(&mut self.ctx.terms, &mut candidate, left)
                    else {
                        continue;
                    };
                    let Some(right_unit) =
                        append_owned_leaf(&mut self.ctx.terms, &mut candidate, right)
                    else {
                        continue;
                    };
                    let lemma = candidate.add_theory_lemma_with_kind(
                        "datatype",
                        theorem,
                        TheoryLemmaKind::DatatypeTesterEval,
                    );
                    let residual =
                        candidate.add_resolution(vec![not_right], left.term, lemma, left_unit);
                    candidate.add_resolution(Vec::new(), right.term, residual, right_unit);
                    if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored)
                        .is_ok()
                        && Self::proof_derives_empty_clause(&candidate)
                        && self.check_proof_strict_with_datatypes(&candidate).is_ok()
                    {
                        *proof = candidate;
                        return;
                    }
                }
            }

            // A negative tester plus disequality from its nullary sibling
            // contradicts exact two-constructor exhaustiveness.
            for tester_leaf in &leaves {
                let TermData::Not(tester) = self.ctx.terms.get(tester_leaf.term) else {
                    continue;
                };
                if tester_subject(&self.ctx.terms, *tester).is_none() {
                    continue;
                }
                let tester = *tester;
                for equality_leaf in &leaves {
                    let TermData::Not(equality) = self.ctx.terms.get(equality_leaf.term) else {
                        continue;
                    };
                    if decode_eq_local(&self.ctx.terms, *equality).is_none() {
                        continue;
                    }
                    let equality = *equality;
                    let theorem = vec![tester, equality];
                    if !ay_proof::recognize_datatype_tester_eval_with_selectors(
                        &self.ctx.terms,
                        &theorem,
                        &datatype_decls,
                        &selector_decls,
                    ) {
                        continue;
                    }
                    let mut candidate = Proof::new();
                    let Some(tester_unit) =
                        append_owned_leaf(&mut self.ctx.terms, &mut candidate, tester_leaf)
                    else {
                        continue;
                    };
                    let Some(equality_unit) =
                        append_owned_leaf(&mut self.ctx.terms, &mut candidate, equality_leaf)
                    else {
                        continue;
                    };
                    let lemma = candidate.add_theory_lemma_with_kind(
                        "datatype",
                        theorem,
                        TheoryLemmaKind::DatatypeTesterEval,
                    );
                    let residual =
                        candidate.add_resolution(vec![equality], tester, lemma, tester_unit);
                    candidate.add_resolution(Vec::new(), equality, residual, equality_unit);
                    if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored)
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

        // Transport an authored constructor equality through a selector, apply
        // the declaration-backed selector projection theorem, and close the
        // authored selector disequality.
        if !selector_decls.is_empty() {
            for source_leaf in &leaves {
                let Some((source_left, source_right)) =
                    decode_eq_local(&self.ctx.terms, source_leaf.term)
                else {
                    continue;
                };
                for (subject, constructor) in
                    [(source_left, source_right), (source_right, source_left)]
                {
                    if !matches!(
                        self.ctx.terms.get(constructor),
                        TermData::App(Symbol::Named(_), _)
                    ) {
                        continue;
                    }
                    for goal_leaf in &leaves {
                        let TermData::Not(goal_equality) =
                            self.ctx.terms.get(goal_leaf.term).clone()
                        else {
                            continue;
                        };
                        let Some((goal_left, goal_right)) =
                            decode_eq_local(&self.ctx.terms, goal_equality)
                        else {
                            continue;
                        };
                        for (selector_term, field_value) in
                            [(goal_left, goal_right), (goal_right, goal_left)]
                        {
                            let TermData::App(selector_symbol @ Symbol::Named(_), selector_args) =
                                self.ctx.terms.get(selector_term).clone()
                            else {
                                continue;
                            };
                            if selector_args.as_slice() != [subject] {
                                continue;
                            }
                            let selector_sort = self.ctx.terms.sort(selector_term).clone();
                            let selector_constructor = self.ctx.terms.mk_app(
                                selector_symbol,
                                [constructor],
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
                                &selector_decls,
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
                            let congruence = candidate.add_rule_step(
                                AletheRule::EqCongruent,
                                vec![
                                    self.ctx.terms.mk_not_raw(source_leaf.term),
                                    congruence_equality,
                                ],
                                Vec::new(),
                                Vec::new(),
                            );
                            let congruence_unit = candidate.add_resolution(
                                vec![congruence_equality],
                                source_leaf.term,
                                congruence,
                                source_unit,
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
                            candidate.add_resolution(Vec::new(), goal_equality, goal, goal_unit);
                            if ay_proof::validate_reachable_assumes_in_problem_scope(
                                &candidate, &authored,
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
