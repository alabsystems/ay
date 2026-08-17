// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Collapse `(not (not X))` to `X` inside the clause of a TRUST-kind theory
    /// lemma, so the CHECKER'S OWN schema matcher can see the literal that is
    /// actually there (#trust-count→0, the double-negation blind spot).
    ///
    /// ROOT CAUSE. A theory conflict is recorded as the negation of each
    /// conflicting literal. When the refuted literal is itself an authored
    /// negation — `(not (= v (select (store a i v) j)))` — its negation is built
    /// as the raw term `(not (not (= v (select ...))))`; `mk_not` does not fold
    /// the pair. The resulting clause
    ///
    /// ```text
    /// (cl (not (= i j)) (not (not (= v (select (store a i v) j)))))
    /// ```
    ///
    /// IS the read-over-write-positive axiom under an index-equality premise,
    /// and `ay-proof`'s `matches_row1_conditional` validates exactly that
    /// schema — but only after seeing an EQUALITY literal. `flatten_clause_literals`
    /// flattens a unit `or` and nothing else, so the doubly-negated literal is
    /// opaque to it, `recognize_array_theory_lemma` answers `None`, the lemma
    /// keeps the `Generic` kind, and mandatory certification rejects the proof
    /// with `step t2 uses unsupported theory lemma kind Generic in strict mode`
    /// for a verdict AY computed correctly. Measured on
    /// `executor_tests::smt::qf_ax::test_executor_qf_ax_row1_conflict`:
    ///
    /// ```text
    /// dn=true before=None after=Some(ArraySelectStore { index_eq: true })
    /// ```
    ///
    /// THIS IS A NORMALIZATION, NOT A RELAXATION. `(not (not X))` and `X` are
    /// the same proposition, so rewriting the literal changes the clause's
    /// SYNTAX and not its content. Nothing about the checker changes: the
    /// rewritten clause is handed to the SAME `recognize_array_theory_lemma`
    /// matcher and then to the SAME `check_proof_strict_with_datatypes`, which
    /// re-derives the full read-over-write schema from the clause alone. A
    /// clause that was not a genuine axiom instance before the rewrite is not
    /// one after it, and the pass leaves such a proof — and its `unknown` —
    /// exactly as it found it.
    ///
    /// FAIL-CLOSED at every step, following
    /// [`Self::replace_with_exact_authored_store_permutation_refutation`]:
    /// it runs ONLY on a proof the strict checker already rejects; it rewrites
    /// ONLY trust-kind lemmas (a validated kind is never re-labelled); the new
    /// kind is whatever the CHECKER'S OWN classifier returns, never a
    /// producer-side guess, and a clause the classifier still calls trust is
    /// left alone; and the whole rewritten proof replaces the original only
    /// after `validate_reachable_assumes_in_problem_scope`,
    /// `proof_derives_empty_clause` and the PLAIN
    /// `check_proof_strict_with_datatypes` all accept it.
    pub(super) fn collapse_double_negated_trust_lemma_literals(&mut self, proof: &mut Proof) {
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }

        /// Peel `(not (not X))` pairs down to the first literal that is not a
        /// double negation. Peeling in PAIRS preserves polarity, so the result
        /// is logically identical to the input literal.
        fn collapse(terms: &TermStore, literal: TermId) -> TermId {
            let mut current = literal;
            loop {
                let TermData::Not(inner) = terms.get(current) else {
                    return current;
                };
                let TermData::Not(innermost) = terms.get(*inner) else {
                    return current;
                };
                current = *innermost;
            }
        }

        let mut candidate = proof.clone();
        let mut rewrote = false;
        // #trust->0 C3: same registries the mint-time check uses, so the
        // funnel's DT recognition is re-decided identically by the strict
        // re-check gating the swap below.
        let c3_dt_data = crate::theory_inference::dt_funnel_registry_data(&self.ctx);
        let c3_dt = c3_dt_data
            .as_ref()
            .map(crate::theory_inference::DatatypeRegistries::from_data);
        for step in &mut candidate.steps {
            let ProofStep::TheoryLemma {
                kind,
                clause,
                farkas,
                lia,
                ..
            } = step
            else {
                continue;
            };
            if !kind.is_trust() {
                continue;
            }
            let collapsed: Vec<TermId> = clause
                .iter()
                .map(|&literal| collapse(&self.ctx.terms, literal))
                .collect();
            if collapsed == *clause {
                continue;
            }
            // The checker's own classifier decides what the collapsed clause
            // is. No schema logic is duplicated here.
            let (inferred, ordered) =
                crate::theory_inference::infer_theory_lemma_kind_from_clause_terms_and_farkas(
                    &self.ctx.terms,
                    &collapsed,
                    farkas.as_ref(),
                    c3_dt.as_ref(),
                );
            if inferred.is_trust() {
                continue;
            }
            if (farkas.is_some() || lia.is_some())
                && !matches!(
                    inferred,
                    TheoryLemmaKind::LraFarkas | TheoryLemmaKind::LiaGeneric
                )
            {
                // Positional arithmetic evidence cannot authorize an EUF/DT
                // relabel, even if the collapsed clause is already in the
                // non-arithmetic validator's preferred order.
                continue;
            }
            // #trust->0 C3: adopt the validator-ordered clause (EUF kinds).
            // Collapse preserves position, so a positional Farkas certificate
            // survives it — but not a REORDER; decline those promotions when a
            // certificate is attached (fail-closed).
            let collapsed = match ordered {
                std::borrow::Cow::Owned(reordered) => {
                    if farkas.is_some() || lia.is_some() {
                        continue;
                    }
                    reordered
                }
                std::borrow::Cow::Borrowed(_) => collapsed,
            };
            *clause = collapsed;
            *kind = inferred;
            rewrote = true;
        }
        if !rewrote {
            return;
        }

        let authored = self.exact_concrete_authored_scope();
        if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_ok()
            && Self::proof_derives_empty_clause(&candidate)
            && self.check_proof_strict_with_datatypes(&candidate).is_ok()
        {
            *proof = candidate;
        }
    }
}
