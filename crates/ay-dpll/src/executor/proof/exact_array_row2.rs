// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Rebuild direct and indirect ROW2 cores directly from exact authored
    /// roots.
    ///
    /// The direct core is
    /// `i≠j ∧ select(store(a,i,v),j)≠select(a,j)`.  The eager ABV lane
    /// rewrites the select-over-store term to an ITE before SAT solving, so the
    /// pruned proof no longer contains a syntactic ROW2 unit for
    /// `promote_contextual_array_row2_lemmas` to recognize.  Recover the proof
    /// from the immutable authored roots instead of granting authority to that
    /// rewritten internal assertion.
    ///
    /// The indirect core is
    /// `b = store(a,i,v) ∧ i≠j ∧ select(b,j)≠select(a,j)`.  Its store
    /// equality is transported through `select` by ordinary congruence.  In
    /// both arms the only array theorem is the strict checker's guarded ROW2
    /// clause, and a candidate replaces the proof only after exact-scope,
    /// empty-clause, and strict-check validation.
    pub(super) fn replace_with_exact_authored_array_row2_refutation(&mut self, proof: &mut Proof) {
        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }

        fn store_parts(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
            let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
                return None;
            };
            if name == "store" && args.len() == 3 {
                Some((args[0], args[1]))
            } else {
                None
            }
        }

        fn select_parts(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
            let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
                return None;
            };
            if name == "select" && args.len() == 2 {
                Some((args[0], args[1]))
            } else {
                None
            }
        }

        let authored = self.exact_concrete_authored_scope();

        // Direct authored ROW2.  This arm is intentionally independent of the
        // current proof shape: ABV select-store expansion changes the SAT-level
        // unit into an ITE equality, while these frozen roots retain the exact
        // source theorem we need to prove.
        for &row_root in &authored {
            let TermData::Not(row_equality) = self.ctx.terms.get(row_root).clone() else {
                continue;
            };
            let Some((row_left, row_right)) = decode_eq_local(&self.ctx.terms, row_equality) else {
                continue;
            };
            for (store_read, base_read) in [(row_left, row_right), (row_right, row_left)] {
                let Some((store_term, read_index)) = select_parts(&self.ctx.terms, store_read)
                else {
                    continue;
                };
                let Some((base, store_index)) = store_parts(&self.ctx.terms, store_term) else {
                    continue;
                };
                let Some((base_array, base_read_index)) = select_parts(&self.ctx.terms, base_read)
                else {
                    continue;
                };
                if base_array != base || base_read_index != read_index {
                    continue;
                }

                for &index_root in &authored {
                    let TermData::Not(index_equality) = self.ctx.terms.get(index_root).clone()
                    else {
                        continue;
                    };
                    if !equality_matches_pair_local(
                        &self.ctx.terms,
                        index_equality,
                        store_index,
                        read_index,
                    ) || ay_proof::recognize_array_select_store(
                        &self.ctx.terms,
                        &[index_equality, row_equality],
                    ) != Some(false)
                    {
                        continue;
                    }

                    let mut candidate = Proof::new();
                    let index_assume = candidate.add_assume(index_root, None);
                    let row_assume = candidate.add_assume(row_root, None);
                    let row2 = candidate.add_theory_lemma_with_kind(
                        "array",
                        vec![index_equality, row_equality],
                        TheoryLemmaKind::ArraySelectStore { index_eq: false },
                    );
                    let row_unit = candidate.add_resolution(
                        vec![row_equality],
                        index_equality,
                        row2,
                        index_assume,
                    );
                    candidate.add_resolution(Vec::new(), row_equality, row_unit, row_assume);

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

        for &store_root in &authored {
            let Some((store_left, store_right)) = decode_eq_local(&self.ctx.terms, store_root)
            else {
                continue;
            };
            for (alias, store_term) in [(store_left, store_right), (store_right, store_left)] {
                let Some((base, store_index)) = store_parts(&self.ctx.terms, store_term) else {
                    continue;
                };
                for &row_root in &authored {
                    let TermData::Not(row_equality) = self.ctx.terms.get(row_root).clone() else {
                        continue;
                    };
                    let Some((row_left, row_right)) =
                        decode_eq_local(&self.ctx.terms, row_equality)
                    else {
                        continue;
                    };
                    for (alias_read, base_read) in [(row_left, row_right), (row_right, row_left)] {
                        let Some((alias_array, read_index)) =
                            select_parts(&self.ctx.terms, alias_read)
                        else {
                            continue;
                        };
                        let Some((base_array, base_read_index)) =
                            select_parts(&self.ctx.terms, base_read)
                        else {
                            continue;
                        };
                        if alias_array != alias
                            || base_array != base
                            || base_read_index != read_index
                        {
                            continue;
                        }
                        for &index_root in &authored {
                            let TermData::Not(index_equality) =
                                self.ctx.terms.get(index_root).clone()
                            else {
                                continue;
                            };
                            if !equality_matches_pair_local(
                                &self.ctx.terms,
                                index_equality,
                                store_index,
                                read_index,
                            ) {
                                continue;
                            }
                            let selected_sort = self.ctx.terms.sort(alias_read).clone();
                            let selected_store = self.ctx.terms.mk_app(
                                Symbol::named("select"),
                                [store_term, read_index],
                                selected_sort,
                            );
                            let congruence_equality = self.ctx.terms.mk_app(
                                Symbol::named("="),
                                [alias_read, selected_store],
                                Sort::Bool,
                            );
                            let row_store_equality = self.ctx.terms.mk_app(
                                Symbol::named("="),
                                [selected_store, base_read],
                                Sort::Bool,
                            );
                            if ay_proof::recognize_array_select_store(
                                &self.ctx.terms,
                                &[index_equality, row_store_equality],
                            ) != Some(false)
                            {
                                continue;
                            }

                            let mut candidate = Proof::new();
                            let store_assume = candidate.add_assume(store_root, None);
                            let read_index_reflexivity = self.ctx.terms.mk_app(
                                Symbol::named("="),
                                [read_index, read_index],
                                Sort::Bool,
                            );
                            let congruence = candidate.add_rule_step(
                                AletheRule::EqCongruent,
                                vec![
                                    self.ctx.terms.mk_not_raw(store_root),
                                    self.ctx.terms.mk_not_raw(read_index_reflexivity),
                                    congruence_equality,
                                ],
                                Vec::new(),
                                Vec::new(),
                            );
                            let congruence_without_store = candidate.add_resolution(
                                vec![
                                    self.ctx.terms.mk_not_raw(read_index_reflexivity),
                                    congruence_equality,
                                ],
                                store_root,
                                congruence,
                                store_assume,
                            );
                            let read_index_reflexive = candidate.add_rule_step(
                                AletheRule::EqReflexive,
                                vec![read_index_reflexivity],
                                Vec::new(),
                                Vec::new(),
                            );
                            let congruence_unit = candidate.add_resolution(
                                vec![congruence_equality],
                                read_index_reflexivity,
                                congruence_without_store,
                                read_index_reflexive,
                            );
                            let index_assume = candidate.add_assume(index_root, None);
                            let row2 = candidate.add_theory_lemma_with_kind(
                                "array",
                                vec![index_equality, row_store_equality],
                                TheoryLemmaKind::ArraySelectStore { index_eq: false },
                            );
                            let row_store_unit = candidate.add_resolution(
                                vec![row_store_equality],
                                index_equality,
                                row2,
                                index_assume,
                            );
                            let transitivity = candidate.add_rule_step(
                                AletheRule::EqTransitive,
                                vec![
                                    self.ctx.terms.mk_not_raw(congruence_equality),
                                    self.ctx.terms.mk_not_raw(row_store_equality),
                                    row_equality,
                                ],
                                Vec::new(),
                                Vec::new(),
                            );
                            let residual = candidate.add_resolution(
                                vec![self.ctx.terms.mk_not_raw(row_store_equality), row_equality],
                                congruence_equality,
                                transitivity,
                                congruence_unit,
                            );
                            let row_unit = candidate.add_resolution(
                                vec![row_equality],
                                row_store_equality,
                                residual,
                                row_store_unit,
                            );
                            let row_assume = candidate.add_assume(row_root, None);
                            candidate.add_resolution(
                                Vec::new(),
                                row_equality,
                                row_unit,
                                row_assume,
                            );

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
