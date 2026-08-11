// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

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
    }

    /// Whether `application` applies a symbol the problem DECLARED as a
    /// datatype constructor.
    ///
    /// Re-derived from `datatype_decls_for_strict_proof` — the same declaration
    /// snapshot the strict checker hands to `ay_proof::recognize_datatype_distinct`
    /// — so the answer follows the problem's `declare-datatypes`, never a name
    /// pattern, a spelling, or a capitalization convention. A problem with no
    /// datatype declarations has an empty snapshot and every application answers
    /// `false`.
    ///
    /// This decides OWNERSHIP between two reconstruction passes, never the
    /// validity of a step: both possible answers leave the emitted proof subject
    /// to the same unchanged `check_proof_strict_with_datatypes` gate.
    fn applies_declared_datatype_constructor(
        terms: &TermStore,
        datatype_decls: &[(String, Vec<String>)],
        application: TermId,
    ) -> bool {
        let TermData::App(symbol, arguments) = terms.get(application) else {
            return false;
        };
        if arguments.is_empty() {
            return false;
        }
        let name = symbol.name();
        datatype_decls
            .iter()
            .any(|(_, constructors)| constructors.iter().any(|c| c == name))
    }

    /// Derive the unit clause `(cl (= lhs rhs))` by CONGRUENCE inside
    /// `candidate`, drawing every argument premise from the exact authored
    /// scope, and return the step proving it together with the equality term.
    ///
    /// Declines (leaving `candidate` untouched apart from unreferenced steps)
    /// when the two terms are not applications of one symbol at one arity, or
    /// when some argument position has no exact authored equality. An argument
    /// position whose two sides are the SAME term is discharged by
    /// [`TheoryLemmaKind::EufReflexive`] rather than by a premise no one
    /// authored.
    ///
    /// Nothing here is trusted: the emitted clause is re-decided by the strict
    /// `EufCongruent` validator, which requires exactly one negated-equality
    /// premise per argument position, each connecting that position's two
    /// arguments.
    pub(super) fn derive_authored_congruence_unit(
        &mut self,
        candidate: &mut Proof,
        lhs: TermId,
        rhs: TermId,
        authored_equalities: &[(TermId, TermId, TermId)],
    ) -> Option<(ProofId, TermId)> {
        /// Work bound. Each candidate costs O(arity) authored-scope scans and
        /// one strict replay. Declining an oversized application leaves the
        /// verdict exactly as it is today.
        const MAX_CONGRUENCE_ARITY: usize = 16;

        let (f_symbol, f_args) = as_app_local(&self.ctx.terms, lhs)?;
        let (g_symbol, g_args) = as_app_local(&self.ctx.terms, rhs)?;
        // Cheap necessary conditions of the schema — the checker's validator
        // re-decides all of them on the clause it is handed.
        if f_symbol != g_symbol
            || f_args.len() != g_args.len()
            || f_args.is_empty()
            || f_args.len() > MAX_CONGRUENCE_ARITY
        {
            return None;
        }

        /// How one argument position's premise literal is discharged.
        enum Discharge {
            /// The exact authored equality root proving this position.
            Authored(TermId),
            /// Both sides are the same term: `(= a a)` by `eq_reflexive`.
            Reflexive,
        }
        let mut premises: Vec<(TermId, Discharge)> = Vec::with_capacity(f_args.len());
        for (&left_arg, &right_arg) in f_args.iter().zip(g_args.iter()) {
            if left_arg == right_arg {
                let equality =
                    self.ctx
                        .terms
                        .mk_app(Symbol::named("="), [left_arg, right_arg], Sort::Bool);
                premises.push((equality, Discharge::Reflexive));
                continue;
            }
            // The premise must be an EXACT authored root, in the authored
            // orientation. The validator accepts either orientation, so no
            // normalization happens here.
            let &(root, _, _) = authored_equalities.iter().find(|&&(_, a, b)| {
                (a == left_arg && b == right_arg) || (a == right_arg && b == left_arg)
            })?;
            premises.push((root, Discharge::Authored(root)));
        }

        let congruence_equality = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [lhs, rhs], Sort::Bool);
        // (cl (not (= a_1 b_1)) .. (not (= a_n b_n)) (= (f a) (f b)))
        let mut clause: Vec<TermId> = premises
            .iter()
            .map(|(equality, _)| self.ctx.terms.mk_not_raw(*equality))
            .collect();
        clause.push(congruence_equality);

        let mut current = candidate.add_theory_lemma_with_kind(
            "euf",
            clause.clone(),
            TheoryLemmaKind::EufCongruent,
        );
        let mut remaining = clause;
        for (equality, discharge) in &premises {
            let negated = self.ctx.terms.mk_not_raw(*equality);
            // Resolution removes ONE occurrence; a repeated argument pair would
            // otherwise leave a literal behind and the residual check below
            // rejects the candidate.
            let position = remaining.iter().position(|&literal| literal == negated)?;
            let _ = remaining.remove(position);
            let support = match discharge {
                Discharge::Authored(root) => candidate.add_assume(*root, None),
                Discharge::Reflexive => candidate.add_theory_lemma_with_kind(
                    "euf",
                    vec![*equality],
                    TheoryLemmaKind::EufReflexive,
                ),
            };
            current = candidate.add_resolution(remaining.clone(), *equality, current, support);
        }
        if remaining != vec![congruence_equality] {
            return None;
        }
        Some((current, congruence_equality))
    }

    /// Commit `candidate` over `proof` only when it derives the empty clause
    /// from authored assumptions AND the plain strict checker accepts it.
    ///
    /// This is the single fail-closed gate every reconstruction arm above ends
    /// at: a candidate the checker will not independently re-validate never
    /// replaces anything, so a mis-recognition costs completeness (the verdict
    /// stays `unknown`) and can never cost soundness.
    pub(super) fn commit_if_strictly_checked(
        &mut self,
        proof: &mut Proof,
        candidate: Proof,
        authored: &[TermId],
    ) -> bool {
        if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, authored).is_ok()
            && Self::proof_derives_empty_clause(&candidate)
            && self.check_proof_strict_with_datatypes(&candidate).is_ok()
        {
            self.purge_surface_overrides_for_certified_proof(&candidate);
            *proof = candidate;
            return true;
        }
        false
    }

    /// Override-purge discipline for a committed authored reconstruction:
    /// drop every stale surface spelling attached to a term this proof PRINTS,
    /// so one internal term cannot reach the printer under two spellings.
    ///
    /// Mirrors the same discipline the trichotomy / assume-bridge surgery
    /// already applies (`proof_trust_surgery.rs`). These reconstructions build
    /// every non-`assume` step out of freshly interned canonical terms, while
    /// the ordinary export collected the problem file's spellings for the
    /// authored roots and their subterms. Those two renderings of one `TermId`
    /// collide inside a single certified step whenever elaboration FOLDED the
    /// source — an authored `(bvadd p #x00)` hash-conses to `p`, an authored
    /// `#x01` is the interned constant whose canonical rendering is
    /// `#b00000001` — so the printed `eq_congruent` hypothesis `(= p p)` sits
    /// next to the operand `(bvadd p #x00)`, and the printed ROW1 store value
    /// `#xAA` next to the separately printed `#b10101010`. The printer's
    /// surface validators are RIGHT to refuse those steps: as printed they do
    /// not correspond to the step the checker validated.
    ///
    /// Purging cannot hide such a divergence, because after it there is none:
    /// every operand of every certified step is rendered from the very term
    /// the strict checker just accepted, which is the identity rendering of
    /// the internal proof. It removes information (the problem file's
    /// spelling), never adds authority — and it cannot re-spell a term as
    /// something else, which is precisely what registering the enclosing
    /// spelling on a folded operand would do (see
    /// `bound_override_respells_target`: attaching `(bvadd p #x00)` to `p`
    /// renames the variable everywhere instead of re-spelling the sum).
    ///
    /// Scoped to the terms this candidate prints; unrelated entries survive
    /// for whatever the later export passes still render.
    fn purge_surface_overrides_for_certified_proof(&mut self, candidate: &Proof) {
        /// Work bound on the printed-term closure. An oversized reconstruction
        /// keeps today's spellings and simply stays unexportable.
        const MAX_PRINTED_TERMS: usize = 64 * 1024;

        let Some(mut overrides) = self.last_proof_term_overrides.clone() else {
            return;
        };

        let mut printed: ay_core::kani_compat::DetHashSet<TermId> =
            ay_core::kani_compat::DetHashSet::default();
        let mut stack: Vec<TermId> = Vec::new();
        for step in &candidate.steps {
            match step {
                ProofStep::Assume(term) => stack.push(*term),
                ProofStep::Resolution { clause, pivot, .. } => {
                    stack.extend(clause.iter().copied());
                    stack.push(*pivot);
                }
                ProofStep::TheoryLemma { clause, .. } => stack.extend(clause.iter().copied()),
                ProofStep::Step { clause, args, .. } => {
                    stack.extend(clause.iter().copied());
                    stack.extend(args.iter().copied());
                }
                ProofStep::Anchor { .. } => {}
                // `ProofStep` is `#[non_exhaustive]`. A kind whose terms this
                // walk does not know how to enumerate could leave a stale
                // spelling behind on a term the document prints, so purge
                // NOTHING and keep exactly today's behaviour: the printer then
                // declines the divergence as it does now.
                _ => return,
            }
        }
        while let Some(term) = stack.pop() {
            if printed.len() >= MAX_PRINTED_TERMS {
                return;
            }
            if !printed.insert(term) {
                continue;
            }
            stack.extend(self.ctx.terms.children(term));
        }

        for term in &printed {
            overrides.remove(term);
        }
        self.last_proof_term_overrides = Some(overrides);
    }
}

#[cfg(test)]
#[path = "authored_congruence_tests.rs"]
mod tests;
