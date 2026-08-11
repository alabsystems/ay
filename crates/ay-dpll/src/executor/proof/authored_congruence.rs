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
    fn derive_authored_congruence_unit(
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
            *proof = candidate;
            return true;
        }
        false
    }
}
