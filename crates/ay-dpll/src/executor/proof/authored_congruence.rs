// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[path = "authored_congruence_commit.rs"]
mod certified_commit;
#[path = "authored_congruence_support.rs"]
mod support;

impl Executor {
    /// Rebuild a CONGRUENCE refutation directly from exact authored roots
    /// (#trust-count→0, the QF_UFBV/QF_AUFBV `f(x) != f(y)` shape).
    ///
    /// The problem asserts a negated equality between two applications of ONE
    /// function symbol, `(not (= (f a_1 .. a_n) (f b_1 .. b_n)))`, together
    /// with authored equalities `(= a_i b_i)` for the argument positions that
    /// differ. That is unsatisfiable by congruence, and AY decides it — but the
    /// refutation is closed by the EUF lane's level-0 propagation, so no
    /// clause-level conflict reaches the SAT trace,
    /// `derive_empty_via_level0_rup` declines with `RupNoConflict`, and the
    /// reconstruction falls through to the whole-problem `trust` closer. That
    /// clause is the whole problem, so the deferred-trust rescue cannot
    /// discharge it either and the mandatory publication gate correctly refused:
    ///
    /// ```text
    /// computed UNSAT rejected by mandatory strict certification: strict UNSAT
    /// proof validation failed: step t1 uses unverified trust rule
    /// ```
    ///
    /// The refutation itself is small and fully checkable:
    ///
    /// ```text
    /// (assume h0 (= x y))
    /// (assume h1 (not (= (f x) (f y))))
    /// (step t0 (cl (not (= x y)) (= (f x) (f y))) :rule eq_congruent)
    /// (step t1 (cl (= (f x) (f y)))               :rule resolution :premises (t0 h0))
    /// (step t2 (cl)                               :rule resolution :premises (t1 h1))
    /// ```
    ///
    /// `eq_congruent` is [`TheoryLemmaKind::EufCongruent`], whose strict
    /// validator (`ay-proof`'s `validate_euf_congruent`) re-derives the whole
    /// schema from the clause alone: the conclusion must be a POSITIVE equality
    /// between two applications of the SAME symbol at the SAME arity, and there
    /// must be exactly one negated-equality premise per argument position,
    /// each connecting that position's two arguments. Nothing is taken on the
    /// producer's word — a premise for the wrong position, a missing premise,
    /// or a mismatched symbol is rejected there.
    ///
    /// An argument position whose two sides are the SAME term still needs its
    /// premise literal, and no authored equality supplies `(= a a)`. Those are
    /// discharged by [`TheoryLemmaKind::EufReflexive`], whose validator checks
    /// exactly that the unit clause is an equality between one term and itself.
    ///
    /// Fail-closed at every step, mirroring
    /// [`Self::replace_with_exact_authored_store_permutation_refutation`]: it
    /// runs only on a proof the strict checker already rejects; every `assume`
    /// is an exact authored root; and the rebuilt proof must derive the empty
    /// clause, keep every reachable assume inside the authored scope, and pass
    /// `check_proof_strict_with_datatypes` before it replaces anything.
    pub(super) fn replace_with_exact_authored_congruence_refutation(&mut self, proof: &mut Proof) {
        /// Work bound on the VALUE-MISMATCH arm, which pairs authored
        /// equalities. Each surviving pair costs one strict replay, and this
        /// pass runs on every refutation the strict checker rejects. Declining
        /// leaves today's behaviour exactly as it is (the verdict stays
        /// `unknown`).
        const MAX_AUTHORED_EQUALITIES: usize = 64;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();

        // Authored positive equalities, kept with their exact root term so the
        // rebuilt proof assumes the authored syntax rather than a
        // re-normalized copy of it.
        let authored_equalities: Vec<(TermId, TermId, TermId)> = authored
            .iter()
            .filter_map(|&root| {
                decode_eq_local(&self.ctx.terms, root).map(|(lhs, rhs)| (root, lhs, rhs))
            })
            .collect();

        // ARM A — the refuting disequality is itself authored:
        //   `(= a_i b_i)` … plus `(not (= (f a) (f b)))`.
        for &conclusion_root in &authored {
            let TermData::Not(conclusion_equality) = self.ctx.terms.get(conclusion_root) else {
                continue;
            };
            let conclusion_equality = *conclusion_equality;
            let Some((lhs, rhs)) = decode_eq_local(&self.ctx.terms, conclusion_equality) else {
                continue;
            };

            let mut candidate = Proof::new();
            let Some((current, congruence_equality)) = self.derive_authored_congruence_unit(
                &mut candidate,
                lhs,
                rhs,
                &authored_equalities,
            ) else {
                continue;
            };
            // Interning must have returned the AUTHORED equality term, else the
            // final resolution would not pair with the authored assumption.
            if congruence_equality != conclusion_equality {
                continue;
            }
            let conclusion_assume = candidate.add_assume(conclusion_root, None);
            candidate.add_resolution(Vec::new(), conclusion_equality, current, conclusion_assume);

            if self.commit_if_strictly_checked(proof, candidate, &authored) {
                return;
            }
        }

        // ARM B — the refuting disequality is DERIVED: two authored equalities
        // pin the two congruent applications to values that cannot be equal.
        //
        //   `(= x y)` … `(= (f x) c)` … `(= (f y) d)`   with `c != d` checkable
        //
        // Congruence gives `(= (f x) (f y))`; transitivity over that plus the
        // two value equalities gives `(= c d)`; and a ground-disequality lemma
        // refutes it. All three steps are re-derived by the strict checker:
        // `EufCongruent` re-checks the argument premises position by position,
        // `EufTransitive` searches the equality graph for a path from `c` to
        // `d` ITSELF (so a chain that does not actually connect is rejected),
        // and the endpoint lemma re-evaluates the disequality.
        if authored_equalities.len() > MAX_AUTHORED_EQUALITIES {
            return;
        }
        // Each authored equality offers two readings of which side is the
        // congruent application; the schema decides nothing here, the checker
        // does.
        let oriented: Vec<(TermId, TermId, TermId)> = authored_equalities
            .iter()
            .flat_map(|&(root, lhs, rhs)| [(root, lhs, rhs), (root, rhs, lhs)])
            .collect();
        for (left_index, &(left_root, left_app, left_value)) in oriented.iter().enumerate() {
            for &(right_root, right_app, right_value) in oriented.iter().skip(left_index + 1) {
                // Borrow-only pre-filter. The pair scan is O(n^2) and the two
                // `mk_app`/`mk_not_raw` calls below INTERN terms, so deciding
                // cheaply here keeps a rejected proof from growing the term
                // store by thousands of dead equalities. Neither test decides
                // the schema — the checker's validators do.
                if left_root == right_root
                    || !Self::is_distinct_same_symbol_application(
                        &self.ctx.terms,
                        left_app,
                        right_app,
                    )
                    || self.ctx.terms.sort(left_value) != self.ctx.terms.sort(right_value)
                {
                    continue;
                }
                let value_equality = self.ctx.terms.mk_app(
                    Symbol::named("="),
                    [left_value, right_value],
                    Sort::Bool,
                );
                let value_disequality = self.ctx.terms.mk_not_raw(value_equality);
                let Some(refutation) = Self::endpoint_refutation_for(
                    &self.ctx.terms,
                    left_value,
                    right_value,
                    value_disequality,
                ) else {
                    continue;
                };

                let mut candidate = Proof::new();
                let Some((current, congruence_equality)) = self.derive_authored_congruence_unit(
                    &mut candidate,
                    left_app,
                    right_app,
                    &authored_equalities,
                ) else {
                    continue;
                };

                // (cl (not (= (f x) (f y))) (not (= (f x) c)) (not (= (f y) d)) (= c d))
                let transitive_clause = vec![
                    self.ctx.terms.mk_not_raw(congruence_equality),
                    self.ctx.terms.mk_not_raw(left_root),
                    self.ctx.terms.mk_not_raw(right_root),
                    value_equality,
                ];
                let mut chain = candidate.add_theory_lemma_with_kind(
                    "euf",
                    transitive_clause.clone(),
                    TheoryLemmaKind::EufTransitive,
                );
                let mut remaining = transitive_clause;
                let mut discharged = true;
                for (equality, support) in [
                    (congruence_equality, current),
                    (left_root, candidate.add_assume(left_root, None)),
                    (right_root, candidate.add_assume(right_root, None)),
                ] {
                    let negated = self.ctx.terms.mk_not_raw(equality);
                    let Some(position) = remaining.iter().position(|&literal| literal == negated)
                    else {
                        discharged = false;
                        break;
                    };
                    let _ = remaining.remove(position);
                    chain = candidate.add_resolution(remaining.clone(), equality, chain, support);
                }
                if !discharged || remaining != vec![value_equality] {
                    continue;
                }
                let disequality = Self::add_endpoint_refutation_lemma(
                    &mut candidate,
                    refutation,
                    value_disequality,
                );
                candidate.add_resolution(Vec::new(), value_equality, chain, disequality);

                if self.commit_if_strictly_checked(proof, candidate, &authored) {
                    return;
                }
            }
        }

        // ARM C — the refuting disequality is AUTHORED, and it names only ONE
        // of the two congruent applications:
        //
        //   `(= x #x05)` … `(= (f x) #xAA)` … `(not (= (f #x05) #xAA))`
        //
        // Congruence gives `(= (f x) (f #x05))`; transitivity over that plus
        // the authored value equality gives `(= (f #x05) #xAA)`, which the
        // authored disequality refutes directly. ARM A does not fire (its
        // disequality must be BETWEEN the two applications) and neither does
        // ARM B (which needs BOTH applications pinned to values).
        //
        // SCOPE: `f` must be an UNINTERPRETED symbol. This pass is the EUF lane
        // — every lemma it emits is tagged `theory = "euf"` — and ARM C's schema
        // is the only arm whose shape is ALSO within reach of the datatype lane's
        // [`Self::replace_with_exact_authored_equality_closure_refutation`], which
        // runs later. On a datatype CONSTRUCTOR application the two passes
        // therefore overlap and the earlier one silently wins:
        //
        //   (assert (= result (Accept claimed)))
        //   (assert (not (= result (Accept actual))))
        //   (assert (= actual claimed))
        //
        // is `unsat` (z3 5.0.0 agrees), and ARM C closes it by reading `Accept`
        // as an opaque EUF symbol. That refutation is CORRECT — it is strictly
        // re-checked before it is committed — but it misattributes a datatype
        // inference to `euf`, and it splits ONE fixture family across two passes:
        // the sibling shape `red = c1 = c2 = blue` closes on
        // `TheoryLemmaKind::DatatypeDistinct`, which needs the constructor
        // registry and which this pass cannot produce at all. Constructor
        // congruence belongs with constructor distinctness, in the pass that owns
        // both.
        //
        // The test is a REGISTRY lookup, not a name or spelling pattern: the
        // symbol must be declared as a constructor in the same
        // `datatype_decls_for_strict_proof` snapshot the strict checker hands to
        // `recognize_datatype_distinct`. Declining is completeness-only — the
        // later pass either rebuilds the refutation or the verdict stays
        // `unknown` — so a mis-recognition here can never cost soundness.
        //
        // ARMs A, B and D are deliberately left alone: no fixture shows them
        // claiming a constructor application, and narrowing an arm no evidence
        // implicates would risk closures for nothing.
        let datatype_decls = self.datatype_decls_for_strict_proof();
        for &conclusion_root in &authored {
            let TermData::Not(conclusion_equality) = self.ctx.terms.get(conclusion_root).clone()
            else {
                continue;
            };
            let Some((conclusion_lhs, conclusion_rhs)) =
                decode_eq_local(&self.ctx.terms, conclusion_equality)
            else {
                continue;
            };
            for (right_app, shared_value) in [
                (conclusion_lhs, conclusion_rhs),
                (conclusion_rhs, conclusion_lhs),
            ] {
                for &(value_root, value_lhs, value_rhs) in &authored_equalities {
                    let Some(left_app) = pair_other_side_local(value_lhs, value_rhs, shared_value)
                    else {
                        continue;
                    };
                    // Borrow-only pre-filter; the checker's validators decide
                    // the schema.
                    if !Self::is_distinct_same_symbol_application(
                        &self.ctx.terms,
                        left_app,
                        right_app,
                    ) {
                        continue;
                    }
                    // Ownership boundary, not a schema decision (see above).
                    // `is_distinct_same_symbol_application` has already pinned
                    // both sides to the SAME symbol, so testing one is testing
                    // both.
                    if Self::applies_declared_datatype_constructor(
                        &self.ctx.terms,
                        &datatype_decls,
                        left_app,
                    ) {
                        continue;
                    }
                    let mut candidate = Proof::new();
                    let Some((congruence_step, congruence_equality)) = self
                        .derive_authored_congruence_unit(
                            &mut candidate,
                            left_app,
                            right_app,
                            &authored_equalities,
                        )
                    else {
                        continue;
                    };
                    // (cl (not (= (f x) (f c))) (not (= (f x) v)) (= (f c) v))
                    let congruence_negated = self.ctx.terms.mk_not_raw(congruence_equality);
                    let value_negated = self.ctx.terms.mk_not_raw(value_root);
                    let chain = candidate.add_theory_lemma_with_kind(
                        "euf",
                        vec![congruence_negated, value_negated, conclusion_equality],
                        TheoryLemmaKind::EufTransitive,
                    );
                    let partial = candidate.add_resolution(
                        vec![value_negated, conclusion_equality],
                        congruence_equality,
                        chain,
                        congruence_step,
                    );
                    let value_assume = candidate.add_assume(value_root, None);
                    let unit = candidate.add_resolution(
                        vec![conclusion_equality],
                        value_root,
                        partial,
                        value_assume,
                    );
                    let conclusion_assume = candidate.add_assume(conclusion_root, None);
                    candidate.add_resolution(
                        Vec::new(),
                        conclusion_equality,
                        unit,
                        conclusion_assume,
                    );

                    if self.commit_if_strictly_checked(proof, candidate, &authored) {
                        return;
                    }
                }
            }
        }

        // ARM D — the same value-mismatch shape as ARM B, but the two congruent
        // applications are connected by NESTED congruence rather than by one
        // authored equality per argument position:
        //
        //   `(= x y)` … `(= (f (select a x)) #xAA)` … `(= (f (select a y)) #xBB)`
        //
        // `derive_congruence_unit` recurses through `select` to the authored
        // `(= x y)`, and `derive_disequality_unit` separates the two values.
        // Both are re-decided by `ay-proof`: `EufCongruent` per level and
        // `BvBitBlast` on the value disequality.
        /// Work bound on ARM D's pair scan. Each surviving pair costs one
        /// nested congruence derivation; declining the rest leaves the verdict
        /// exactly as it is today.
        const MAX_NESTED_CONGRUENCE_ATTEMPTS: usize = 256;

        let mut nested_attempts = 0_usize;
        for (left_index, &(left_root, left_lhs, left_rhs)) in authored_equalities.iter().enumerate()
        {
            for &(right_root, right_lhs, right_rhs) in
                authored_equalities.iter().skip(left_index + 1)
            {
                for (left_app, left_value) in [(left_lhs, left_rhs), (left_rhs, left_lhs)] {
                    for (right_app, right_value) in [(right_lhs, right_rhs), (right_rhs, right_lhs)]
                    {
                        // Borrow-only pre-filter; the checker's validators
                        // decide the schema.
                        if !Self::is_distinct_same_symbol_application(
                            &self.ctx.terms,
                            left_app,
                            right_app,
                        ) || self.ctx.terms.sort(left_value) != self.ctx.terms.sort(right_value)
                        {
                            continue;
                        }
                        nested_attempts += 1;
                        if nested_attempts > MAX_NESTED_CONGRUENCE_ATTEMPTS {
                            return;
                        }
                        let mut candidate = Proof::new();
                        let Some(congruence) = self.derive_congruence_unit(
                            &mut candidate,
                            left_app,
                            right_app,
                            &authored_equalities,
                        ) else {
                            continue;
                        };
                        let Some(conflict) = self.derive_disequality_unit(
                            &mut candidate,
                            left_value,
                            right_value,
                            &authored,
                            &authored_equalities,
                        ) else {
                            continue;
                        };
                        let TermData::Not(value_equality) =
                            self.ctx.terms.get(conflict.literal).clone()
                        else {
                            continue;
                        };

                        // (cl (not (= (f a) v)) (not (= (f a) (f b))) (not (= (f b) w)) (= v w))
                        let left_negated = self.ctx.terms.mk_not_raw(left_root);
                        let congruence_negated = self.ctx.terms.mk_not_raw(congruence.literal);
                        let right_negated = self.ctx.terms.mk_not_raw(right_root);
                        let mut remaining = vec![
                            left_negated,
                            congruence_negated,
                            right_negated,
                            value_equality,
                        ];
                        let mut chain = candidate.add_theory_lemma_with_kind(
                            "euf",
                            remaining.clone(),
                            TheoryLemmaKind::EufTransitive,
                        );
                        let left_assume = candidate.add_assume(left_root, None);
                        let right_assume = candidate.add_assume(right_root, None);
                        let mut discharged = true;
                        for (equality, support) in [
                            (left_root, left_assume),
                            (congruence.literal, congruence.step),
                            (right_root, right_assume),
                        ] {
                            let negated = self.ctx.terms.mk_not_raw(equality);
                            let Some(position) =
                                remaining.iter().position(|&literal| literal == negated)
                            else {
                                discharged = false;
                                break;
                            };
                            let _ = remaining.remove(position);
                            chain = candidate.add_resolution(
                                remaining.clone(),
                                equality,
                                chain,
                                support,
                            );
                        }
                        if !discharged || remaining != vec![value_equality] {
                            continue;
                        }
                        candidate.add_resolution(Vec::new(), value_equality, chain, conflict.step);

                        if self.commit_if_strictly_checked(proof, candidate, &authored) {
                            return;
                        }
                    }
                }
            }
        }

        self.replace_with_exact_authored_congruence_arithmetic_refutation(proof, &authored);
    }

    /// ARM E — the congruence-derived equality is refuted by ARITHMETIC, not by
    /// a disequality (#trust-count→0, the Nelson-Oppen EUF+LA gate family).
    ///
    /// ```text
    /// (assert (= x y))
    /// (assert (> (f x) 0.0))
    /// (assert (< (f y) 0.0))
    /// ```
    ///
    /// is `unsat` and AY decides it, but the refutation is a COMBINED conflict:
    /// the clause the theory loop materializes mixes the EUF congruence premise
    /// with two arithmetic bounds. `infer_theory_lemma_kind_in_caller_order`
    /// has no closed-theory recognizer for that mixture — it is neither
    /// pure-EUF (so `infer_euf_lemma_from_clause` declines) nor Farkas-pure in
    /// the caller's literal order — so the lemma is recorded `Generic`, and
    /// `check_proof` has no strict validator for a `Generic` theory lemma:
    ///
    /// ```text
    /// computed UNSAT rejected by mandatory strict certification: strict UNSAT
    /// proof validation failed: step t2 uses unsupported theory lemma kind
    /// Generic in strict mode
    /// ```
    ///
    /// These queries also set `:produce-proofs`, so
    /// [`Self::strict_unsat_presentation_required`] is true and BOTH the
    /// independent exact-semantic lanes and `discharge_trust_steps_for_certification`
    /// are excluded by design — the caller asked for that artifact. The only
    /// remedy is to emit a refutation the strict checker accepts, which is what
    /// this arm does: SPLIT the combined conflict into its two checkable halves.
    ///
    /// ```text
    /// (assume h0 (= x y))
    /// (assume h1 (> (f x) 0.0))
    /// (assume h2 (< (f y) 0.0))
    /// (step t0 (cl (not (= x y)) (= (f x) (f y)))          :rule eq_congruent)
    /// (step t1 (cl (= (f x) (f y)))                        :rule resolution)
    /// (step t2 (cl (not (= (f x) (f y)))
    ///              (not (> (f x) 0.0)) (not (< (f y) 0.0))) :rule la_generic)
    /// (step t3 (cl)                                         :rule resolution)
    /// ```
    ///
    /// Nothing is trusted. The congruence half is re-derived by `ay-proof`'s
    /// `EufCongruent` validator (one negated-equality premise per argument
    /// position, each connecting that position's two arguments); the arithmetic
    /// half is a positional Farkas certificate that
    /// `try_lra_farkas_reconstruction` PRODUCES from an independent LRA solve
    /// and then re-verifies against this exact clause, and that the strict
    /// checker's own `LraFarkas`/`LiaGeneric` validator re-checks a third time.
    /// The uninterpreted applications enter the arithmetic reasoning as opaque
    /// terms, which is exactly the Nelson-Oppen interface literal.
    ///
    /// [`Self::derive_congruence_unit`] (not the exact-authored sibling) supplies
    /// the argument premises, so the two-hop authored chain `(= a b)`, `(= b c)`
    /// reaches `(= (f a) (f c))` through the checked `EqTransitive` lane.
    ///
    /// Fail-closed like every other cascade member: it runs only on a proof the
    /// strict checker already rejects, assumes only exact authored roots, and
    /// the rebuilt candidate must derive the empty clause and pass
    /// `check_proof_strict_with_datatypes` before it replaces anything. Every
    /// bound below is a work bound — declining leaves the verdict exactly as it
    /// is today (`unknown`).
    fn replace_with_exact_authored_congruence_arithmetic_refutation(
        &mut self,
        proof: &mut Proof,
        authored: &[TermId],
    ) {
        /// Authored arithmetic literals admitted as Farkas rows.
        const MAX_ARITH_ROOTS: usize = 12;
        /// Largest arithmetic premise set tried per congruence pair.
        const MAX_ARITH_SUBSET: u32 = 3;
        /// Congruent application pairs examined.
        const MAX_CONGRUENCE_PAIRS: usize = 64;
        /// Farkas reconstructions attempted across the whole arm.
        const MAX_FARKAS_PROBES: usize = 512;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }

        fn arithmetic_literal(terms: &TermStore, root: TermId) -> bool {
            let atom = match terms.get(root) {
                TermData::Not(inner) => *inner,
                _ => root,
            };
            let TermData::App(Symbol::Named(operator), args) = terms.get(atom) else {
                return false;
            };
            args.len() == 2
                && matches!(operator.as_str(), "=" | "<" | "<=" | ">" | ">=")
                && terms.sort(args[0]) == terms.sort(args[1])
                && matches!(terms.sort(args[0]), Sort::Int | Sort::Real)
        }

        /// Numeric-sorted applications of a NON-reserved symbol: the terms an
        /// arithmetic literal can only relate through the EUF interface.
        fn collect_opaque_applications(
            terms: &TermStore,
            term: TermId,
            depth: u32,
            out: &mut Vec<TermId>,
        ) {
            /// Work bound on the operand walk.
            const MAX_OPERAND_DEPTH: u32 = 8;

            if depth > MAX_OPERAND_DEPTH {
                return;
            }
            match terms.get(term) {
                TermData::Not(inner) => {
                    collect_opaque_applications(terms, *inner, depth + 1, out);
                }
                TermData::App(symbol, args) => {
                    if !args.is_empty()
                        && matches!(terms.sort(term), Sort::Int | Sort::Real)
                        && !ay_frontend::is_reserved_symbol(symbol.name())
                    {
                        out.push(term);
                    }
                    let args = args.clone();
                    for arg in args {
                        collect_opaque_applications(terms, arg, depth + 1, out);
                    }
                }
                _ => {}
            }
        }

        let arithmetic_roots: Vec<TermId> = authored
            .iter()
            .copied()
            .filter(|&root| arithmetic_literal(&self.ctx.terms, root))
            .collect();
        if arithmetic_roots.len() < 2 || arithmetic_roots.len() > MAX_ARITH_ROOTS {
            return;
        }
        let authored_equalities: Vec<(TermId, TermId, TermId)> = authored
            .iter()
            .filter_map(|&root| {
                decode_eq_local(&self.ctx.terms, root).map(|(lhs, rhs)| (root, lhs, rhs))
            })
            .collect();
        if authored_equalities.is_empty() {
            return;
        }

        let mut applications: Vec<TermId> = Vec::new();
        for &root in &arithmetic_roots {
            collect_opaque_applications(&self.ctx.terms, root, 0, &mut applications);
        }
        applications.sort_unstable_by_key(|term| term.0);
        applications.dedup();

        let Some(subset_limit) = 1_u64.checked_shl(arithmetic_roots.len() as u32) else {
            return;
        };
        let mut pairs = 0_usize;
        let mut probes = 0_usize;
        for (left_index, &left_app) in applications.iter().enumerate() {
            for &right_app in applications.iter().skip(left_index + 1) {
                // Borrow-only pre-filter; every schema decision below belongs to
                // the checker's validators.
                if !Self::is_distinct_same_symbol_application(&self.ctx.terms, left_app, right_app)
                {
                    continue;
                }
                pairs += 1;
                if pairs > MAX_CONGRUENCE_PAIRS {
                    return;
                }
                let congruence_equality =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("="), [left_app, right_app], Sort::Bool);
                let congruence_negated = self.ctx.terms.mk_not_raw(congruence_equality);

                for cardinality in 1..=MAX_ARITH_SUBSET {
                    for mask in 1_u64..subset_limit {
                        if mask.count_ones() != cardinality {
                            continue;
                        }
                        let selected: Vec<TermId> = arithmetic_roots
                            .iter()
                            .enumerate()
                            .filter_map(|(index, &root)| {
                                ((mask & (1_u64 << index)) != 0).then_some(root)
                            })
                            .collect();
                        let mut clause = Vec::with_capacity(selected.len() + 1);
                        clause.push(congruence_negated);
                        for &root in &selected {
                            clause.push(self.ctx.terms.mk_not_raw(root));
                        }
                        // A repeated literal would leave a residual the
                        // discharge loop below cannot remove.
                        let mut distinct = clause.clone();
                        distinct.sort_unstable_by_key(|term| term.0);
                        distinct.dedup();
                        if distinct.len() != clause.len() {
                            continue;
                        }

                        probes += 1;
                        if probes > MAX_FARKAS_PROBES {
                            return;
                        }
                        let mut farkas = None;
                        let mut inferred = TheoryLemmaKind::Generic;
                        if !crate::executor::proof_farkas::try_lra_farkas_reconstruction(
                            &self.ctx.terms,
                            &clause,
                            &mut farkas,
                            &mut inferred,
                        ) {
                            continue;
                        }
                        let Some(farkas) = farkas else {
                            continue;
                        };
                        if inferred.is_trust() {
                            continue;
                        }

                        let mut candidate = Proof::new();
                        let Some(congruence) = self.derive_congruence_unit(
                            &mut candidate,
                            left_app,
                            right_app,
                            &authored_equalities,
                        ) else {
                            // No authored argument evidence connects this pair;
                            // no arithmetic subset can rescue it.
                            break;
                        };
                        if congruence.literal != congruence_equality {
                            break;
                        }
                        let mut remaining = clause.clone();
                        let lemma = candidate
                            .add_theory_lemma_with_farkas_and_kind("LRA", clause, farkas, inferred);
                        let supports: Vec<(TermId, ProofId)> =
                            std::iter::once((congruence_equality, congruence.step))
                                .chain(
                                    selected
                                        .iter()
                                        .map(|&root| (root, candidate.add_assume(root, None))),
                                )
                                .collect();
                        let mut chain = lemma;
                        let mut discharged = true;
                        for (equality, support) in supports {
                            let negated = self.ctx.terms.mk_not_raw(equality);
                            let Some(position) =
                                remaining.iter().position(|&literal| literal == negated)
                            else {
                                discharged = false;
                                break;
                            };
                            let _ = remaining.remove(position);
                            chain = candidate.add_resolution(
                                remaining.clone(),
                                equality,
                                chain,
                                support,
                            );
                        }
                        if !discharged || !remaining.is_empty() {
                            continue;
                        }
                        if self.commit_if_strictly_checked(proof, candidate, authored) {
                            return;
                        }
                    }
                }
            }
        }
    }
}

#[cfg(test)]
#[path = "authored_congruence_tests.rs"]
mod tests;
