// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    /// Rebuild a COLLECTION-SUBSET refutation directly from exact authored
    /// roots (the `executor_tests::set` subset family).
    ///
    /// Two shapes, both of which AY decides correctly and both of which the
    /// mandatory publication gate was right to refuse.
    ///
    /// (1) TRANSITIVITY. `(set.subset a b)`, `(set.subset b c)` and
    /// `(not (set.subset a c))`. The native set solver closes this by
    /// SKOLEMIZING the negated conclusion — it mints a witness constant and
    /// emits the two halves of `¬(a⊆c) → (w ∈ a ∧ w ∉ c)`:
    ///
    /// ```text
    ///   step t3 clause=[(or (set.subset a c) (select a set_subset_witness_3))]
    ///   step t4 clause=[(or (set.subset a c) (not (select c set_subset_witness_3)))]
    /// ```
    ///
    /// Neither clause is a tautology — each names a constant that appears
    /// nowhere in the problem — so strict mode refuses them
    /// (`step t3 uses unverified trust rule`), discharging them standalone is
    /// impossible, and the deferred-trust rescue cannot help. The verdict
    /// degraded to `unknown`.
    ///
    /// (2) GROUND ALIASES. An authored equality pins a set variable to a
    /// ground carrier — `(= s ((as const (Array Int Bool)) false))` for
    /// `(as set.empty ..)`, `(= s (store ((as const (Array Int Bool)) false) 1 true))`
    /// for `(set.singleton 1)` — and the conflict is one subset atom over
    /// those variables. The solver publishes the atom as a bare unit `trust`
    /// clause (`[(set.subset s t)]`), which is not valid on its own because
    /// `s` and `t` are free variables.
    ///
    /// THE FIX IS A DERIVATION, NOT A RELAXATION. Both shapes are rebuilt out
    /// of the authored roots plus theory lemmas `ay-proof` re-derives from the
    /// clause alone:
    ///
    ///  * [`TheoryLemmaKind::SubsetTransitive`] — `validate_subset_transitive`
    ///    re-derives the CHAIN itself (one operator, one array sort, two
    ///    negated atoms meeting at a shared middle term whose free ends are
    ///    the positive atom's operands), so a triple that does not connect is
    ///    rejected there.
    ///  * [`TheoryLemmaKind::SubsetGroundEval`] — `validate_subset_ground_eval`
    ///    decodes each clause-carried binding's right-hand side into a ground
    ///    carrier normal form and decides the subset relation POINTWISE and
    ///    exactly, demanding an explicitly listed witness index for a negative
    ///    claim. The producer states no schema of its own: it asks the
    ///    checker's own `recognize_subset_theory_lemma` whether the clause it
    ///    is about to emit qualifies.
    ///
    /// Fail-closed at every level, exactly like
    /// [`Self::replace_with_exact_authored_store_permutation_refutation`]: this
    /// runs only on a proof the strict checker ALREADY rejects, every `assume`
    /// is an exact authored root, and `commit_if_strictly_checked` requires
    /// `validate_reachable_assumes_in_problem_scope`,
    /// `proof_derives_empty_clause` AND the plain
    /// `check_proof_strict_with_datatypes` before anything is replaced. A
    /// construction this pass gets wrong costs completeness (the verdict stays
    /// `unknown`), never soundness.
    pub(super) fn replace_with_exact_authored_collection_subset_refutation(
        &mut self,
        proof: &mut Proof,
    ) {
        /// Work bound on the authored scan. Declining an oversized problem
        /// leaves today's behaviour exactly as it is.
        const MAX_AUTHORED_ROOTS: usize = 64;

        if self.check_proof_strict_with_datatypes(proof).is_ok() {
            return;
        }
        let authored = self.exact_concrete_authored_scope();
        if authored.is_empty() || authored.len() > MAX_AUTHORED_ROOTS {
            return;
        }
        if self.try_authored_subset_ground_eval(proof, &authored) {
            return;
        }
        let _ = self.try_authored_subset_transitivity(proof, &authored);
    }

    /// Shape (2): one authored subset atom refuted by deciding it over the
    /// ground carriers its operands are authored to equal.
    fn try_authored_subset_ground_eval(&mut self, proof: &mut Proof, authored: &[TermId]) -> bool {
        let equalities: Vec<(TermId, TermId, TermId)> = authored
            .iter()
            .filter_map(|&root| {
                decode_eq_local(&self.ctx.terms, root).map(|(lhs, rhs)| (root, lhs, rhs))
            })
            .collect();

        for &conflict_root in authored {
            // The authored subset assertion whose NEGATION the lemma states.
            let (atom, conflict_is_positive) = match self.ctx.terms.get(conflict_root).clone() {
                TermData::Not(inner) => (inner, false),
                _ => (conflict_root, true),
            };
            let Some((sub_operand, sup_operand)) = subset_operands_local(&self.ctx.terms, atom)
            else {
                continue;
            };

            // Collect at most one authored binding per operand. An operand the
            // problem does not pin simply contributes no binding literal; the
            // checker then decides whether the claim is universally valid
            // without it.
            let mut binding_roots: Vec<TermId> = Vec::new();
            for operand in [sub_operand, sup_operand] {
                if let Some(&(root, _, _)) = equalities
                    .iter()
                    .find(|&&(_, lhs, rhs)| lhs == operand || rhs == operand)
                {
                    if !binding_roots.contains(&root) {
                        binding_roots.push(root);
                    }
                }
            }

            // The lemma asserts the OPPOSITE polarity of the authored atom, so
            // resolving the two closes the refutation.
            let conclusion = if conflict_is_positive {
                self.ctx.terms.mk_not_raw(atom)
            } else {
                atom
            };
            let mut clause: Vec<TermId> = binding_roots
                .iter()
                .map(|&root| self.ctx.terms.mk_not_raw(root))
                .collect();
            clause.push(conclusion);

            // THE CHECKER'S OWN MATCHER decides whether this qualifies; no
            // schema logic is restated here.
            if ay_proof::recognize_subset_theory_lemma(&self.ctx.terms, &clause)
                != Some(TheoryLemmaKind::SubsetGroundEval)
            {
                continue;
            }

            let mut candidate = Proof::new();
            let mut current = candidate.add_theory_lemma_with_kind(
                "subset",
                clause.clone(),
                TheoryLemmaKind::SubsetGroundEval,
            );
            let mut remaining = clause;
            let mut discharged = true;
            for &root in &binding_roots {
                let negated = self.ctx.terms.mk_not_raw(root);
                let Some(position) = remaining.iter().position(|&literal| literal == negated)
                else {
                    discharged = false;
                    break;
                };
                let _ = remaining.remove(position);
                let support = candidate.add_assume(root, None);
                current = candidate.add_resolution(remaining.clone(), root, current, support);
            }
            if !discharged || remaining != vec![conclusion] {
                continue;
            }
            let conflict = candidate.add_assume(conflict_root, None);
            candidate.add_resolution(Vec::new(), atom, current, conflict);

            if self.commit_if_strictly_checked(proof, candidate, authored) {
                return true;
            }
        }
        false
    }

    /// Shape (1): an authored negated subset atom refuted by chaining authored
    /// positive subset atoms through [`TheoryLemmaKind::SubsetTransitive`].
    ///
    /// The chain is grown by BREADTH-FIRST search over the authored subset
    /// edges, so a four-set chain closes with two transitivity lemmas and an
    /// n-set chain with `n - 2`. Each hop emits its lemma and immediately
    /// resolves away both premises, so the running clause is always the single
    /// derived subset atom.
    fn try_authored_subset_transitivity(&mut self, proof: &mut Proof, authored: &[TermId]) -> bool {
        /// Work bound on the chain length.
        const MAX_CHAIN_HOPS: usize = 16;

        // Authored positive subset edges, as `(root, sub, sup)`.
        let edges: Vec<(TermId, TermId, TermId)> = authored
            .iter()
            .filter_map(|&root| {
                subset_operands_local(&self.ctx.terms, root).map(|(sub, sup)| (root, sub, sup))
            })
            .collect();
        if edges.is_empty() {
            return false;
        }

        for &goal_root in authored {
            let TermData::Not(goal_atom) = self.ctx.terms.get(goal_root).clone() else {
                continue;
            };
            let Some((start, target)) = subset_operands_local(&self.ctx.terms, goal_atom) else {
                continue;
            };
            if start == target {
                continue;
            }

            // Walk the edge graph from `start`, recording the predecessor edge
            // of each reached node, then replay the discovered path.
            let mut reached: Vec<(TermId, Option<usize>)> = vec![(start, None)];
            let mut frontier = 0_usize;
            let mut found = false;
            while frontier < reached.len() && reached.len() <= MAX_CHAIN_HOPS + 1 {
                let (node, _) = reached[frontier];
                frontier += 1;
                for (index, &(_, sub, sup)) in edges.iter().enumerate() {
                    if sub != node || reached.iter().any(|&(seen, _)| seen == sup) {
                        continue;
                    }
                    reached.push((sup, Some(index)));
                    if sup == target {
                        found = true;
                        break;
                    }
                }
                if found {
                    break;
                }
            }
            if !found {
                continue;
            }

            // Recover the edge path from `start` to `target`, outermost-last.
            let mut path: Vec<usize> = Vec::new();
            let mut cursor = target;
            while cursor != start {
                let Some(&(_, Some(edge))) = reached.iter().find(|&&(node, _)| node == cursor)
                else {
                    break;
                };
                path.push(edge);
                cursor = edges[edge].1;
            }
            if cursor != start || path.len() < 2 {
                continue;
            }
            path.reverse();

            if self.try_authored_subset_chain_candidate(
                proof, authored, &edges, &path, goal_root, goal_atom, start,
            ) {
                return true;
            }
        }
        false
    }

    /// Emit one transitivity lemma per hop beyond the first and close against
    /// the authored negated goal, for
    /// [`Self::try_authored_subset_transitivity`].
    #[allow(clippy::too_many_arguments)]
    fn try_authored_subset_chain_candidate(
        &mut self,
        proof: &mut Proof,
        authored: &[TermId],
        edges: &[(TermId, TermId, TermId)],
        path: &[usize],
        goal_root: TermId,
        goal_atom: TermId,
        start: TermId,
    ) -> bool {
        let Some((&first, rest)) = path.split_first() else {
            return false;
        };
        let mut candidate = Proof::new();
        // The running fact is the authored first edge, then each transitivity
        // conclusion in turn.
        let (first_root, _, first_sup) = edges[first];
        let mut current_atom = first_root;
        let mut current_sup = first_sup;
        let mut current_step = candidate.add_assume(first_root, None);

        for &hop in rest {
            let (hop_root, hop_sub, hop_sup) = edges[hop];
            if hop_sub != current_sup {
                return false;
            }
            let conclusion = if hop_sup == start {
                // A cycle back to the start: the conclusion is `start ⊆ start`,
                // which is not the goal shape this pass closes.
                return false;
            } else {
                self.ctx.terms.mk_app(
                    Symbol::named(subset_operator_name_local(&self.ctx.terms, current_atom)),
                    [start, hop_sup],
                    Sort::Bool,
                )
            };
            let negated_current = self.ctx.terms.mk_not_raw(current_atom);
            let negated_hop = self.ctx.terms.mk_not_raw(hop_root);
            let lemma_clause = vec![negated_current, negated_hop, conclusion];
            // THE CHECKER'S OWN MATCHER authorizes the lemma.
            if ay_proof::recognize_subset_theory_lemma(&self.ctx.terms, &lemma_clause)
                != Some(TheoryLemmaKind::SubsetTransitive)
            {
                return false;
            }
            let lemma = candidate.add_theory_lemma_with_kind(
                "subset",
                lemma_clause,
                TheoryLemmaKind::SubsetTransitive,
            );
            let partial = candidate.add_resolution(
                vec![negated_hop, conclusion],
                current_atom,
                lemma,
                current_step,
            );
            let hop_assume = candidate.add_assume(hop_root, None);
            current_step =
                candidate.add_resolution(vec![conclusion], hop_root, partial, hop_assume);
            current_atom = conclusion;
            current_sup = hop_sup;
        }

        if current_atom != goal_atom {
            return false;
        }
        let goal_assume = candidate.add_assume(goal_root, None);
        candidate.add_resolution(Vec::new(), goal_atom, current_step, goal_assume);

        self.commit_if_strictly_checked(proof, candidate, authored)
    }
}

/// The three collection subset predicates, as the checker names them.
const SUBSET_OPERATORS: [&str; 3] = ["set.subset", "map.subset", "multiset.subset"];

/// Decode `(X.subset a b)` for one of the native collection subset predicates.
///
/// This is a cheap NECESSARY condition that decides only how much work to
/// spend; the checker's `decode_subset_atom` re-derives the full native
/// signature when it validates the emitted lemma, so a mis-recognition here
/// costs completeness and can never admit an unchecked clause.
fn subset_operands_local(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if !SUBSET_OPERATORS.contains(&name.as_str()) {
        return None;
    }
    let [left, right] = args.as_slice() else {
        return None;
    };
    Some((*left, *right))
}

/// The operator name of a subset atom, for building its transitive conclusion.
///
/// Falls back to `set.subset` only when the caller passes a non-atom, which the
/// callers above never do; the emitted clause is authorized by the checker's
/// own matcher regardless, so a wrong name simply declines.
fn subset_operator_name_local(terms: &TermStore, term: TermId) -> &'static str {
    if let TermData::App(Symbol::Named(name), _) = terms.get(term) {
        if let Some(op) = SUBSET_OPERATORS
            .iter()
            .find(|&&known| known == name.as_str())
        {
            return op;
        }
    }
    SUBSET_OPERATORS[0]
}
