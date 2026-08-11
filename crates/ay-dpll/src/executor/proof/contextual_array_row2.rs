// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Replace a context-dependent, guard-less ROW2 trust lemma with a strict
    /// proof of the same UNSAT core.
    ///
    /// The eager array lane may leave this pruned proof:
    ///
    /// ```text
    /// trust  R                         where R := select(store(a,i,v),j)=select(a,j)
    /// assume (not R)
    /// resolution □
    /// ```
    ///
    /// `R` is valid only in the problem context `i ≠ j`; advertising it as a
    /// unit array lemma would be unsound, while leaving it as `trust` loses the
    /// independently checkable proof already present in the input.  When the
    /// original assertion stack contains both exact hypotheses, rebuild:
    ///
    /// ```text
    /// assume (not (= i j))
    /// assume (not R)
    /// ROW2   (= i j) OR R
    /// resolution R
    /// resolution □
    /// ```
    ///
    /// Recognition is structural and exact (same base array/read index), the
    /// guarded clause must be accepted by the strict checker's own ROW
    /// recognizer, and the whole rebuilt proof must pass strict checking before
    /// it is committed.  The two matched assertions alone form an UNSAT core,
    /// so replacing a larger pruned derivation is sound.
    pub(super) fn promote_contextual_array_row2_lemmas(&mut self, proof: &mut Proof) {
        #[derive(Clone)]
        struct OwnedNegativeEquality {
            root: TermId,
            path: Vec<u32>,
            equality: TermId,
        }

        fn find_negative_equality(
            terms: &TermStore,
            root: TermId,
            lhs: TermId,
            rhs: TermId,
        ) -> Option<OwnedNegativeEquality> {
            fn walk(
                terms: &TermStore,
                root: TermId,
                term: TermId,
                lhs: TermId,
                rhs: TermId,
                path: &mut Vec<u32>,
            ) -> Option<OwnedNegativeEquality> {
                if let TermData::Not(equality) = terms.get(term) {
                    if equality_matches_pair_local(terms, *equality, lhs, rhs) {
                        return Some(OwnedNegativeEquality {
                            root,
                            path: path.clone(),
                            equality: *equality,
                        });
                    }
                }
                let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
                    return None;
                };
                if name != "and" {
                    return None;
                }
                for (position, &child) in args.iter().enumerate() {
                    path.push(u32::try_from(position).ok()?);
                    if let Some(found) = walk(terms, root, child, lhs, rhs, path) {
                        return Some(found);
                    }
                    path.pop();
                }
                None
            }

            walk(terms, root, root, lhs, rhs, &mut Vec::new())
        }

        fn derive_owned_conjunct(
            terms: &mut TermStore,
            proof: &mut Proof,
            assume: ProofId,
            root: TermId,
            path: &[u32],
        ) -> Option<ProofId> {
            let mut current_id = assume;
            let mut current_term = root;
            for &position in path {
                let TermData::App(Symbol::Named(name), args) = terms.get(current_term) else {
                    return None;
                };
                if name != "and" {
                    return None;
                }
                let child = *args.get(position as usize)?;
                let not_parent = terms.mk_not_raw(current_term);
                let projection = proof.add_rule_step(
                    AletheRule::AndPos(position),
                    vec![not_parent, child],
                    Vec::new(),
                    vec![current_term],
                );
                current_id =
                    proof.add_resolution(vec![child], current_term, projection, current_id);
                current_term = child;
            }
            Some(current_id)
        }

        let candidates: Vec<(TermId, TermId, TermId)> = proof
            .steps
            .iter()
            .filter_map(|step| {
                let ProofStep::TheoryLemma { kind, clause, .. } = step else {
                    return None;
                };
                if !kind.is_trust() {
                    return None;
                }
                let [row_eq] = clause.as_slice() else {
                    return None;
                };
                let (store_index, read_index) = row2_unit_indices_local(&self.ctx.terms, *row_eq)?;
                Some((*row_eq, store_index, read_index))
            })
            .collect();
        if candidates.is_empty() {
            return;
        }

        // Every new Assume must be owned by the active problem.  Include both
        // asserted roots and `check-sat-assuming` roots; the latter are stored
        // separately from `ctx.assertions` but are equally valid proof inputs.
        let mut owned_roots = self.proof_original_problem_assertions();
        if let Some(assumptions) = &self.last_assumptions {
            for &assumption in assumptions {
                if !owned_roots.contains(&assumption) {
                    owned_roots.push(assumption);
                }
            }
        }

        let original = proof.clone();
        for (candidate_row_eq, store_index, read_index) in candidates {
            let Some((candidate_lhs, candidate_rhs)) =
                decode_eq_local(&self.ctx.terms, candidate_row_eq)
            else {
                continue;
            };

            let mut index_hypothesis = None;
            let mut row_hypothesis = None;
            for &root in &owned_roots {
                if index_hypothesis.is_none() {
                    index_hypothesis =
                        find_negative_equality(&self.ctx.terms, root, store_index, read_index);
                }
                if row_hypothesis.is_none() {
                    row_hypothesis =
                        find_negative_equality(&self.ctx.terms, root, candidate_lhs, candidate_rhs);
                }
            }
            let (Some(index_hypothesis), Some(row_hypothesis)) = (index_hypothesis, row_hypothesis)
            else {
                // A different load-bearing contextual unit may have complete
                // owned roots; do not let the first structural candidate mask it.
                continue;
            };
            let index_eq = index_hypothesis.equality;
            let row_eq = row_hypothesis.equality;
            if index_eq == row_eq
                || !equality_matches_pair_local(
                    &self.ctx.terms,
                    row_eq,
                    candidate_lhs,
                    candidate_rhs,
                )
                || ay_proof::recognize_array_select_store(&self.ctx.terms, &[index_eq, row_eq])
                    != Some(false)
            {
                continue;
            }

            proof.steps.clear();
            proof.named_steps.clear();
            let index_assume = proof.add_assume(index_hypothesis.root, None);
            let Some(index_unit) = derive_owned_conjunct(
                &mut self.ctx.terms,
                proof,
                index_assume,
                index_hypothesis.root,
                &index_hypothesis.path,
            ) else {
                *proof = original.clone();
                continue;
            };
            let row_unit = if row_hypothesis.root == index_hypothesis.root {
                derive_owned_conjunct(
                    &mut self.ctx.terms,
                    proof,
                    index_assume,
                    row_hypothesis.root,
                    &row_hypothesis.path,
                )
            } else {
                let row_assume = proof.add_assume(row_hypothesis.root, None);
                derive_owned_conjunct(
                    &mut self.ctx.terms,
                    proof,
                    row_assume,
                    row_hypothesis.root,
                    &row_hypothesis.path,
                )
            };
            let Some(row_unit) = row_unit else {
                *proof = original.clone();
                continue;
            };
            let row2 = proof.add_theory_lemma_with_kind(
                "array",
                vec![index_eq, row_eq],
                TheoryLemmaKind::ArraySelectStore { index_eq: false },
            );
            let proved_row = proof.add_resolution(vec![row_eq], index_eq, index_unit, row2);
            proof.add_resolution(Vec::new(), row_eq, row_unit, proved_row);

            if self.check_proof_strict_with_datatypes(proof).is_ok() {
                return;
            }
            *proof = original.clone();
        }

        *proof = original;
    }
}
