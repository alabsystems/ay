// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Rebuild a pure total-order / term-ITE contradiction from one exact
    /// authored root.
    ///
    /// Lowering min/max-style code into nested term `ite`s can leave the SAT
    /// reconstruction with a Generic arithmetic leaf even when the negated
    /// authored postcondition is independently decidable by enumerating total
    /// preorders.  Admit only the exact complementary theorem recognized by
    /// `ay-proof`'s bounded order-ITE checker, then resolve it against that
    /// authored premise.  Numeric constants, arithmetic, UFs, Boolean atoms,
    /// and formulas outside the checker's explicit resource bounds remain
    /// unsupported and therefore fail closed.
    pub(super) fn replace_with_exact_authored_order_ite_refutation(&mut self, proof: &mut Proof) {
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        for &root in &authored {
            let (theorem, pivot) = match self.ctx.terms.get(root) {
                TermData::Not(inner) => (*inner, *inner),
                _ => (self.ctx.terms.mk_not_raw(root), root),
            };
            if !ay_proof::recognize_order_ite_tautology(&self.ctx.terms, &[theorem]) {
                continue;
            }

            let mut candidate = Proof::new();
            let premise = candidate.add_assume(root, None);
            let lemma = candidate.add_theory_lemma_with_kind(
                "order-ite",
                vec![theorem],
                TheoryLemmaKind::OrderIteTautology,
            );
            candidate.add_resolution(Vec::new(), pivot, premise, lemma);
            if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_ok()
                && Self::proof_derives_empty_clause(&candidate)
                && self.check_proof_strict_with_datatypes(&candidate).is_ok()
            {
                *proof = candidate;
                return;
            }
        }
    }

    /// Rebuild a small rational-linear contradiction from exact public-query
    /// roots, including `check-sat-assuming` literals and positive conjuncts
    /// projected from those roots.
    ///
    /// Combined-theory preprocessing can replace an authored linking equality
    /// with `true`, or introduce Euclidean `div` identities, before the SAT
    /// trace is reconstructed.  The resulting proof may retain a trust leaf
    /// even though a small subset of the original roots is already an ordinary
    /// Farkas contradiction (for example `select(a, 0) = x`, `x > 0`,
    /// `select(a, 0) <= 0`, or two different equalities for `mod(x, 2)`).
    /// Search bounded small subsets, assume only exact roots, and commit only a
    /// candidate that the strict checker replays against that same scope.
    pub(super) fn replace_with_exact_authored_linear_refutation(&mut self, proof: &mut Proof) {
        const MAX_LINEAR_ROOTS: usize = 12;
        const MAX_FARKAS_ROOTS: usize = 6;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }

        fn is_numeric_literal(terms: &TermStore, term: TermId) -> bool {
            let atom = match terms.get(term) {
                TermData::Not(inner) => *inner,
                _ => term,
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

        #[derive(Clone)]
        struct OwnedLinearRoot {
            root: TermId,
            term: TermId,
            path: Vec<u32>,
        }

        /// Collect only leaves reached through a POSITIVE conjunction.  A
        /// nested disjunction, negation, or implication remains one opaque
        /// leaf: projecting through any of those connectives would not be a
        /// consequence of the authored root.
        fn collect_owned_leaves(
            terms: &TermStore,
            root: TermId,
            term: TermId,
            path: &mut Vec<u32>,
            out: &mut Vec<OwnedLinearRoot>,
        ) {
            if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
                if name == "and" {
                    for (position, &child) in args.iter().enumerate() {
                        path.push(position as u32);
                        collect_owned_leaves(terms, root, child, path, out);
                        path.pop();
                    }
                    return;
                }
            }
            out.push(OwnedLinearRoot {
                root,
                term,
                path: path.clone(),
            });
        }

        /// Assume the exact public root and derive the selected conjunct with
        /// checked Alethe `and_pos` plus resolution steps.  An empty path is a
        /// top-level authored assertion and needs no projection.
        fn append_owned_leaf(
            terms: &mut TermStore,
            candidate: &mut Proof,
            owned: &OwnedLinearRoot,
        ) -> Option<ProofId> {
            let mut current = candidate.add_assume(owned.root, None);
            let mut current_term = owned.root;
            for &position in &owned.path {
                let TermData::App(Symbol::Named(name), args) = terms.get(current_term) else {
                    return None;
                };
                if name != "and" {
                    return None;
                }
                let child = *args.get(position as usize)?;
                let projection = candidate.add_rule_step(
                    AletheRule::AndPos(position),
                    vec![terms.mk_not_raw(current_term), child],
                    Vec::new(),
                    vec![current_term],
                );
                current = candidate.add_resolution(vec![child], current_term, projection, current);
                current_term = child;
            }
            (current_term == owned.term).then_some(current)
        }

        let authored = self.exact_concrete_authored_scope();
        let mut owned_leaves = Vec::new();
        for &root in &authored {
            collect_owned_leaves(
                &self.ctx.terms,
                root,
                root,
                &mut Vec::new(),
                &mut owned_leaves,
            );
        }
        let linear_roots: Vec<OwnedLinearRoot> = owned_leaves
            .iter()
            .filter(|owned| is_numeric_literal(&self.ctx.terms, owned.term))
            .cloned()
            .collect();
        if (2..=MAX_LINEAR_ROOTS).contains(&linear_roots.len()) {
            let limit = 1_u64 << linear_roots.len();
            for cardinality in 2..=MAX_FARKAS_ROOTS.min(linear_roots.len()) {
                for mask in 1_u64..limit {
                    if mask.count_ones() as usize != cardinality {
                        continue;
                    }
                    let selected: Vec<OwnedLinearRoot> = linear_roots
                        .iter()
                        .enumerate()
                        .filter(|&(index, _)| (mask & (1_u64 << index)) != 0)
                        .map(|(_, root)| root.clone())
                        .collect();
                    let blocking_clause: Vec<TermId> = selected
                        .iter()
                        .map(|root| self.ctx.terms.mk_not_raw(root.term))
                        .collect();
                    let mut farkas = None;
                    let mut inferred = TheoryLemmaKind::Generic;
                    if !super::super::proof_farkas::try_lra_farkas_reconstruction(
                        &self.ctx.terms,
                        &blocking_clause,
                        &mut farkas,
                        &mut inferred,
                    ) {
                        continue;
                    }
                    let Some(farkas) = farkas else {
                        continue;
                    };

                    // A rational Farkas certificate is strict-checkable for both
                    // Int and Real roots. Do not inherit a heuristic integer kind:
                    // that would require a separate LiaAnnotation and obscure the
                    // exact certificate we just reconstructed.
                    let mut candidate = Proof::new();
                    let Some(premise_ids) = selected
                        .iter()
                        .map(|owned| append_owned_leaf(&mut self.ctx.terms, &mut candidate, owned))
                        .collect::<Option<Vec<ProofId>>>()
                    else {
                        continue;
                    };
                    let mut current = candidate.add_step(ProofStep::TheoryLemma {
                        theory: "LRA".to_string(),
                        clause: blocking_clause.clone(),
                        farkas: Some(farkas),
                        kind: TheoryLemmaKind::LraFarkas,
                        lia: None,
                    });
                    let mut residual = blocking_clause;
                    let mut failed = false;
                    for (root, &premise) in selected.iter().zip(premise_ids.iter()) {
                        let complement = self.ctx.terms.mk_not_raw(root.term);
                        let Some(position) = residual.iter().position(|&lit| lit == complement)
                        else {
                            failed = true;
                            break;
                        };
                        let _ = residual.remove(position);
                        current =
                            candidate.add_resolution(residual.clone(), root.term, current, premise);
                    }
                    if failed || !residual.is_empty() {
                        continue;
                    }
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

        #[derive(Clone, Copy)]
        struct ArithmeticFact {
            term: TermId,
            unit: ProofId,
        }

        /// Derive `not target` from a bounded subset of already-projected
        /// numeric facts.  The producer does not decide validity: it asks the
        /// rational Farkas reconstructor first, then the strict checker's exact
        /// integer-gap recognizer.  A miss leaves the branch unsupported.
        fn derive_numeric_negation(
            terms: &mut TermStore,
            candidate: &mut Proof,
            facts: &[ArithmeticFact],
            target: TermId,
        ) -> Option<ProofId> {
            const MAX_SUPPORT: usize = 6;
            if facts.len() > MAX_LINEAR_ROOTS {
                return None;
            }
            let target_complement = terms.mk_not_raw(target);
            let limit = 1_u64 << facts.len();
            for cardinality in 0..=MAX_SUPPORT.min(facts.len()) {
                for mask in 0_u64..limit {
                    if mask.count_ones() as usize != cardinality {
                        continue;
                    }
                    let selected: Vec<ArithmeticFact> = facts
                        .iter()
                        .enumerate()
                        .filter_map(|(index, fact)| {
                            ((mask & (1_u64 << index)) != 0 && fact.term != target).then_some(*fact)
                        })
                        .collect();
                    if selected.len() != cardinality {
                        continue;
                    }
                    let mut clause: Vec<TermId> = selected
                        .iter()
                        .map(|fact| terms.mk_not_raw(fact.term))
                        .collect();
                    clause.push(target_complement);

                    let mut farkas = None;
                    let mut inferred = TheoryLemmaKind::Generic;
                    let rational = super::super::proof_farkas::try_lra_farkas_reconstruction(
                        terms,
                        &clause,
                        &mut farkas,
                        &mut inferred,
                    );
                    // The LRA engine can simplify a ground affine conflict
                    // (e.g. `m <= m - 1`) before surfacing coefficients. Try
                    // the smallest deterministic candidate, but grant it no
                    // authority: the exact Farkas checker must replay it over
                    // the final blocking clause before it can be emitted.
                    let direct_farkas =
                        FarkasAnnotation::new(vec![
                            num_rational::Rational64::from(1);
                            clause.len()
                        ]);
                    let checked_direct =
                        super::super::proof_farkas_validation::certificate_valid_for_blocking_clause(
                            terms,
                            &clause,
                            &direct_farkas,
                        );
                    let checked_farkas = if rational {
                        farkas
                    } else if checked_direct {
                        Some(direct_farkas)
                    } else {
                        None
                    };
                    let mut current = if let Some(farkas) = checked_farkas {
                        candidate.add_step(ProofStep::TheoryLemma {
                            theory: "LRA".to_string(),
                            clause: clause.clone(),
                            farkas: Some(farkas),
                            kind: TheoryLemmaKind::LraFarkas,
                            lia: None,
                        })
                    } else if ay_core::proof_validation::recognize_lia_bounds_gap(terms, &clause) {
                        candidate.add_step(ProofStep::TheoryLemma {
                            theory: "LIA".to_string(),
                            clause: clause.clone(),
                            farkas: None,
                            kind: TheoryLemmaKind::LiaGeneric,
                            lia: Some(ay_core::LiaAnnotation::BoundsGap),
                        })
                    } else if ay_core::proof_validation::recognize_lia_divisibility(terms, &clause)
                    {
                        candidate.add_step(ProofStep::TheoryLemma {
                            theory: "LIA".to_string(),
                            clause: clause.clone(),
                            // The Divisibility validator re-derives the exact
                            // integer gap and intentionally ignores this wire
                            // compatibility vector.
                            farkas: Some(FarkasAnnotation::new(vec![
                                num_rational::Rational64::from(
                                    1
                                );
                                clause.len()
                            ])),
                            kind: TheoryLemmaKind::LiaGeneric,
                            lia: Some(ay_core::LiaAnnotation::Divisibility),
                        })
                    } else {
                        continue;
                    };

                    let mut residual = clause;
                    let mut failed = false;
                    for fact in &selected {
                        let blocker = terms.mk_not_raw(fact.term);
                        let Some(position) = residual.iter().position(|&lit| lit == blocker) else {
                            failed = true;
                            break;
                        };
                        let _ = residual.remove(position);
                        current = candidate.add_resolution(
                            residual.clone(),
                            fact.term,
                            current,
                            fact.unit,
                        );
                    }
                    if !failed && residual == [target_complement] {
                        return Some(current);
                    }
                }
            }
            None
        }

        /// Recursively falsify a bounded Boolean formula. Arithmetic leaves are
        /// discharged by `derive_numeric_negation`; `and` needs one false
        /// child, while `or` needs all children false. Every connective step is
        /// an independently checked Alethe tautology.
        fn derive_boolean_negation(
            terms: &mut TermStore,
            candidate: &mut Proof,
            facts: &[ArithmeticFact],
            target: TermId,
            work: &mut usize,
            depth: usize,
        ) -> Option<ProofId> {
            const MAX_BOOLEAN_WORK: usize = 64;
            const MAX_BOOLEAN_DEPTH: usize = 12;
            *work += 1;
            if *work > MAX_BOOLEAN_WORK || depth > MAX_BOOLEAN_DEPTH {
                return None;
            }
            if is_numeric_literal(terms, target) {
                return derive_numeric_negation(terms, candidate, facts, target);
            }
            let TermData::App(Symbol::Named(operator), children) = terms.get(target).clone() else {
                return None;
            };
            match operator.as_str() {
                "and" => {
                    for (position, child) in children.into_iter().enumerate() {
                        let Some(child_negation) = derive_boolean_negation(
                            terms,
                            candidate,
                            facts,
                            child,
                            work,
                            depth + 1,
                        ) else {
                            continue;
                        };
                        let target_complement = terms.mk_not_raw(target);
                        let projection = candidate.add_rule_step(
                            AletheRule::AndPos(position as u32),
                            vec![target_complement, child],
                            Vec::new(),
                            vec![target],
                        );
                        return Some(candidate.add_resolution(
                            vec![target_complement],
                            child,
                            projection,
                            child_negation,
                        ));
                    }
                    None
                }
                "or" => {
                    let target_complement = terms.mk_not_raw(target);
                    let mut clause = Vec::with_capacity(children.len() + 1);
                    clause.push(target_complement);
                    clause.extend(children.iter().copied());
                    let mut current = candidate.add_rule_step(
                        AletheRule::OrPos(0),
                        clause.clone(),
                        Vec::new(),
                        vec![target],
                    );
                    let mut residual = clause;
                    for child in children {
                        let child_negation = derive_boolean_negation(
                            terms,
                            candidate,
                            facts,
                            child,
                            work,
                            depth + 1,
                        )?;
                        let position = residual.iter().position(|&lit| lit == child)?;
                        let _ = residual.remove(position);
                        current = candidate.add_resolution(
                            residual.clone(),
                            child,
                            current,
                            child_negation,
                        );
                    }
                    (residual == [target_complement]).then_some(current)
                }
                _ => None,
            }
        }

        // TrustVC's recursive-decrease obligations are authored as a positive
        // conjunction containing a disjunction of failed lexicographic cases.
        // The SAT engine can decide that formula, but its compact conflict does
        // not retain a strict certificate. Rebuild the small Boolean/arithmetic
        // tree from exact source roots instead of blessing that Generic leaf.
        if linear_roots.len() <= MAX_LINEAR_ROOTS {
            let boolean_targets: Vec<OwnedLinearRoot> = owned_leaves
                .iter()
                .filter(|owned| {
                    matches!(
                        self.ctx.terms.get(owned.term),
                        TermData::App(Symbol::Named(name), _) if name == "and" || name == "or"
                    )
                })
                .cloned()
                .collect();
            for target in &boolean_targets {
                let mut candidate = Proof::new();
                let Some(facts) = linear_roots
                    .iter()
                    .map(|owned| {
                        append_owned_leaf(&mut self.ctx.terms, &mut candidate, owned).map(|unit| {
                            ArithmeticFact {
                                term: owned.term,
                                unit,
                            }
                        })
                    })
                    .collect::<Option<Vec<ArithmeticFact>>>()
                else {
                    continue;
                };
                let Some(target_unit) =
                    append_owned_leaf(&mut self.ctx.terms, &mut candidate, target)
                else {
                    continue;
                };
                let mut work = 0;
                let Some(target_negation) = derive_boolean_negation(
                    &mut self.ctx.terms,
                    &mut candidate,
                    &facts,
                    target.term,
                    &mut work,
                    0,
                ) else {
                    continue;
                };
                candidate.add_resolution(Vec::new(), target.term, target_unit, target_negation);
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

    /// Whether `term` is a literal bitvector constant.
    ///
    /// A cheap necessary condition used to narrow candidate work before a
    /// checker recognizer runs — never a substitute for one.
    pub(super) fn is_bitvec_constant(terms: &TermStore, term: TermId) -> bool {
        matches!(terms.get(term), TermData::Const(Constant::BitVec { .. }))
    }

    /// Whether `left` and `right` are DISTINCT applications of one symbol at
    /// one arity — the cheapest necessary condition for a congruence step.
    ///
    /// Borrow-only and allocation-free, so it can gate the O(n^2) pair scan in
    /// [`Self::replace_with_exact_authored_congruence_refutation`]'s
    /// value-mismatch arm before any term is interned. The
    /// `EufCongruent` validator re-decides all of this on the clause it is
    /// handed; this only decides how much work to spend.
    pub(super) fn is_distinct_same_symbol_application(
        terms: &TermStore,
        left: TermId,
        right: TermId,
    ) -> bool {
        if left == right {
            return false;
        }
        match (terms.get(left), terms.get(right)) {
            (TermData::App(left_symbol, left_args), TermData::App(right_symbol, right_args)) => {
                left_symbol == right_symbol
                    && !left_args.is_empty()
                    && left_args.len() == right_args.len()
            }
            _ => false,
        }
    }

    /// Which strict validator, if any, refutes `(= first second)`.
    ///
    /// The decision belongs entirely to the CHECKER'S OWN recognizers. The
    /// BV-constant test in front of `recognize_bv_bitblast` is a cheap
    /// necessary condition of a ground disequality, not a schema decision: it
    /// keeps the work O(1) instead of pushing every BV-sorted pair through the
    /// deadline-bounded proof-producing bit-blaster only to be correctly
    /// rejected. `recognize_bv_bitblast` still re-derives the clause.
    pub(super) fn endpoint_refutation_for(
        terms: &TermStore,
        first: TermId,
        second: TermId,
        disequality: TermId,
    ) -> Option<EndpointRefutation> {
        if ay_core::proof_validation::recognize_lia_divisibility(terms, &[disequality]) {
            return Some(EndpointRefutation::LiaDivisibility);
        }
        if Self::is_bitvec_constant(terms, first)
            && Self::is_bitvec_constant(terms, second)
            && ay_proof::recognize_bv_bitblast(terms, &[disequality])
        {
            return Some(EndpointRefutation::BvBitBlast);
        }
        None
    }

    /// Emit the unit lemma `(cl (not (= first second)))` under the kind the
    /// checker's recognizer selected in [`Self::endpoint_refutation_for`].
    pub(super) fn add_endpoint_refutation_lemma(
        candidate: &mut Proof,
        refutation: EndpointRefutation,
        disequality: TermId,
    ) -> ProofId {
        match refutation {
            EndpointRefutation::LiaDivisibility => candidate.add_step(ProofStep::TheoryLemma {
                theory: "LIA".to_string(),
                clause: vec![disequality],
                farkas: Some(FarkasAnnotation::new(vec![num_rational::Rational64::from(
                    1,
                )])),
                kind: TheoryLemmaKind::LiaGeneric,
                lia: Some(ay_core::LiaAnnotation::Divisibility),
            }),
            EndpointRefutation::BvBitBlast => candidate.add_theory_lemma_with_kind(
                "bv",
                vec![disequality],
                TheoryLemmaKind::BvBitBlast,
            ),
        }
    }

    /// Rebuild two exact equalities with a shared endpoint and incompatible
    /// values, without relying on solver-generated `mod`/`div` identities.
    /// Treating the shared term opaquely is sound: equality transitivity alone
    /// yields the incompatible endpoint equality, and a strict validator
    /// independently rejects that equality.
    ///
    /// The endpoint refutation has two lanes, and BOTH are decided by a
    /// checker-side recognizer rather than by anything this producer asserts:
    ///
    ///  * INTEGER endpoints — `recognize_lia_divisibility`, closed with
    ///    [`TheoryLemmaKind::LiaGeneric`];
    ///  * BITVECTOR endpoints — `ay_proof::recognize_bv_bitblast`, closed with
    ///    [`TheoryLemmaKind::BvBitBlast`], whose strict validator re-derives the
    ///    unit clause `(not (= c d))` by EXHAUSTIVELY evaluating it over every
    ///    assignment of its bounded Bool/BV variables (and, failing that, by
    ///    bit-blasting it and replaying a surfaced LRAT refutation). A
    ///    satisfiable near-miss — two endpoints that CAN be equal — is falsified
    ///    by some assignment and rejected there.
    ///
    /// The BV lane is what `(select a i) = #x05` together with
    /// `(select a i) = #x06` needs: the shared `select` term is opaque to both
    /// theories, the endpoints are BV constants, and the only fact required is
    /// that `#x05` and `#x06` differ. That was previously unreachable because
    /// the sole endpoint refuter was the INTEGER divisibility recognizer, so
    /// AY computed `unsat`, failed to certify it, and published `unknown`.
    pub(super) fn replace_with_exact_authored_equality_chain_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        for (left_index, &left_root) in authored.iter().enumerate() {
            let Some((left_a, left_b)) = decode_eq_local(&self.ctx.terms, left_root) else {
                continue;
            };
            for &right_root in authored.iter().skip(left_index + 1) {
                let Some((right_a, right_b)) = decode_eq_local(&self.ctx.terms, right_root) else {
                    continue;
                };
                let endpoint_pairs = [
                    (left_a == right_a, left_b, right_b),
                    (left_a == right_b, left_b, right_a),
                    (left_b == right_a, left_a, right_b),
                    (left_b == right_b, left_a, right_a),
                ];
                for (shares_endpoint, first, second) in endpoint_pairs {
                    if !shares_endpoint || self.ctx.terms.sort(first) != self.ctx.terms.sort(second)
                    {
                        continue;
                    }
                    let endpoint_equality =
                        self.ctx
                            .terms
                            .mk_app(Symbol::named("="), [first, second], Sort::Bool);
                    let endpoint_disequality = self.ctx.terms.mk_not_raw(endpoint_equality);
                    // Which lane can refute the endpoint equality is decided by
                    // the CHECKER'S OWN recognizers, never by this producer.
                    let Some(endpoint_lemma) = Self::endpoint_refutation_for(
                        &self.ctx.terms,
                        first,
                        second,
                        endpoint_disequality,
                    ) else {
                        continue;
                    };

                    let mut candidate = Proof::new();
                    let left_assume = candidate.add_assume(left_root, None);
                    let right_assume = candidate.add_assume(right_root, None);
                    let not_left = self.ctx.terms.mk_not_raw(left_root);
                    let not_right = self.ctx.terms.mk_not_raw(right_root);
                    let chain = candidate.add_rule_step(
                        AletheRule::EqTransitive,
                        vec![not_left, not_right, endpoint_equality],
                        Vec::new(),
                        Vec::new(),
                    );
                    let right_residual = candidate.add_resolution(
                        vec![not_right, endpoint_equality],
                        left_root,
                        chain,
                        left_assume,
                    );
                    let equality_unit = candidate.add_resolution(
                        vec![endpoint_equality],
                        right_root,
                        right_residual,
                        right_assume,
                    );
                    let disequality = Self::add_endpoint_refutation_lemma(
                        &mut candidate,
                        endpoint_lemma,
                        endpoint_disequality,
                    );
                    candidate.add_resolution(
                        Vec::new(),
                        endpoint_equality,
                        equality_unit,
                        disequality,
                    );

                    if self.commit_if_strictly_checked(proof, candidate, &authored) {
                        return;
                    }
                }
            }
        }
    }
}
