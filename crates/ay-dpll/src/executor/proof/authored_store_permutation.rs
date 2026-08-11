// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Rebuild an n-ary STORE-PERMUTATION refutation directly from exact
    /// authored roots (#trust-count→0, the QF_AX/QF_AUFLIA `storecomm` shape).
    ///
    /// The problem asserts pairwise index disequalities `(not (= i_p i_q))`
    /// together with a negated equality `(not (= L R))` between two `store`
    /// chains over ONE base array that write the same `(index, value)` pairs in
    /// a different order. That is unsatisfiable by extensionality, and AY
    /// decides it — but the refutation is reached through the eager array
    /// lane's level-0 propagation, so no clause-level conflict reaches the SAT
    /// trace, `derive_empty_via_level0_rup` declines with `RupNoConflict`, and
    /// the reconstruction closes on the whole-problem `trust` fallback.
    /// Discharging THAT clause is re-proving the problem, so the deferred-trust
    /// rescue cannot help either and the mandatory certification gate turns a
    /// correct `unsat` into `unknown`.
    ///
    /// The refutation itself is small and fully checkable:
    ///
    /// ```text
    /// (assume h0 (not (= i j)))
    /// (assume h1 (not (= L R)))
    /// (step t0 (cl (= i j) (= L R)) :rule store_permutation)
    /// (step t1 (cl (= L R))         :rule resolution :premises (t0 h0))
    /// (step t2 (cl)                 :rule resolution :premises (t1 h1))
    /// ```
    ///
    /// `store_permutation` is [`TheoryLemmaKind::ArrayStorePermutation`], whose
    /// strict validator (`ay-proof`'s `validate_array_store_permutation`)
    /// re-derives the whole schema from the clause alone: one common base
    /// array, equal chain lengths, pairwise-distinct index terms, equal
    /// `(index, value)` multisets, and one `(= i_p i_q)` literal for EVERY
    /// unordered index pair. Nothing is taken on the producer's word, and the
    /// missing-disequality near-miss (which is falsifiable) is rejected there.
    ///
    /// Fail-closed at every step, mirroring
    /// [`Self::replace_with_exact_authored_array_row2_refutation`]: it runs only
    /// on a proof the strict checker already rejects; the lemma clause is
    /// admitted only when the CHECKER'S OWN matcher
    /// (`ay_proof::recognize_array_theory_lemma`) classifies it as
    /// `ArrayStorePermutation`; every `assume` must be an exact authored root;
    /// and the rebuilt proof must derive the empty clause, keep every reachable
    /// assume inside the authored scope, and pass
    /// `check_proof_strict_with_datatypes` before it replaces anything.
    pub(super) fn replace_with_exact_authored_store_permutation_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();

        // Authored `(not (= p q))` roots paired with the equality they negate.
        // Both the index premises and the conclusion premise are drawn from
        // this one list, so nothing outside the authored scope can enter.
        let negated_equalities: Vec<(TermId, TermId)> = authored
            .iter()
            .filter_map(|&root| {
                let TermData::Not(inner) = self.ctx.terms.get(root) else {
                    return None;
                };
                let inner = *inner;
                decode_eq_local(&self.ctx.terms, inner).map(|_| (root, inner))
            })
            .collect();

        for &(array_root, array_equality) in &negated_equalities {
            let Some((left, right)) = decode_eq_local(&self.ctx.terms, array_equality) else {
                continue;
            };
            let Sort::Array(array_sort) = self.ctx.terms.sort(left).clone() else {
                continue;
            };
            if self.ctx.terms.sort(left) != self.ctx.terms.sort(right) {
                continue;
            }

            // Candidate index-disequality premises: every OTHER authored
            // negated equality between two terms of this array's INDEX sort.
            // The sort filter is a cheap necessary condition of the schema
            // (which quantifies over the chains' index terms), so it narrows
            // the work without deciding anything; which combination is a
            // genuine permutation clause is decided by the checker's matcher.
            let mut premises: Vec<(TermId, TermId)> = negated_equalities
                .iter()
                .copied()
                .filter(|&(root, equality)| {
                    root != array_root
                        && decode_eq_local(&self.ctx.terms, equality).is_some_and(|(p, q)| {
                            self.ctx.terms.sort(p) == &array_sort.index_sort
                                && self.ctx.terms.sort(q) == &array_sort.index_sort
                        })
                })
                .collect();
            // Work bound. The shrink below costs O(premises) matcher calls,
            // each O(premises) in the clause scan, and this pass runs on every
            // refutation the strict checker rejects. Declining an oversized
            // candidate leaves today's behaviour exactly as it is (the verdict
            // stays `unknown`), so the bound can only cost completeness on a
            // shape no chain of realistic depth reaches: a store chain of `n`
            // indices needs `n * (n - 1) / 2` disequalities, so this admits
            // chains up to depth 32.
            const MAX_STORE_PERMUTATION_PREMISES: usize = 512;
            if premises.len() > MAX_STORE_PERMUTATION_PREMISES {
                continue;
            }
            let clause_of = |premises: &[(TermId, TermId)]| -> Vec<TermId> {
                let mut clause: Vec<TermId> =
                    premises.iter().map(|&(_, equality)| equality).collect();
                clause.push(array_equality);
                clause
            };
            if ay_proof::recognize_array_theory_lemma(&self.ctx.terms, &clause_of(&premises))
                != Some(TheoryLemmaKind::ArrayStorePermutation)
            {
                continue;
            }
            // Shrink to the literals the schema actually needs, in authored
            // order, so the rebuilt proof assumes nothing it does not use. The
            // matcher re-decides after every removal, so a literal is dropped
            // only when the SMALLER clause is still a valid instance.
            let mut position = 0;
            while position < premises.len() {
                let mut trimmed = premises.clone();
                let _ = trimmed.remove(position);
                if ay_proof::recognize_array_theory_lemma(&self.ctx.terms, &clause_of(&trimmed))
                    == Some(TheoryLemmaKind::ArrayStorePermutation)
                {
                    premises = trimmed;
                } else {
                    position += 1;
                }
            }

            let clause = clause_of(&premises);
            let mut candidate = Proof::new();
            // Alethe requires the assumption prologue first; the printer hoists
            // assumes anyway, but emitting them in order keeps the rebuilt
            // proof identical to what is exported.
            let index_assumes: Vec<ProofId> = premises
                .iter()
                .map(|&(root, _)| candidate.add_assume(root, None))
                .collect();
            let array_assume = candidate.add_assume(array_root, None);
            let mut current = candidate.add_theory_lemma_with_kind(
                "array",
                clause.clone(),
                TheoryLemmaKind::ArrayStorePermutation,
            );
            let mut remaining = clause.clone();
            for (&(_, equality), &assume) in premises.iter().zip(index_assumes.iter()) {
                remaining.retain(|&literal| literal != equality);
                current = candidate.add_resolution(remaining.clone(), equality, current, assume);
            }
            candidate.add_resolution(Vec::new(), array_equality, current, array_assume);

            if ay_proof::validate_reachable_assumes_in_problem_scope(&candidate, &authored).is_ok()
                && Self::proof_derives_empty_clause(&candidate)
                && self.check_proof_strict_with_datatypes(&candidate).is_ok()
            {
                *proof = candidate;
                return;
            }
        }
    }
}
