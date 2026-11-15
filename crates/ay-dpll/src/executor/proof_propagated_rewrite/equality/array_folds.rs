// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact array semantics at the congruence-to-fold boundary. No new rules.

use super::*;

#[cfg(test)]
mod tests;

fn live(terms: &TermStore, term: TermId) -> Option<()> {
    ((term.0 as usize) < terms.len()).then_some(())
}

fn store_parts(terms: &TermStore, term: TermId) -> Option<[TermId; 3]> {
    live(terms, term)?;
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    let [base, key, value] = args.as_slice() else {
        return None;
    };
    if name != "store" {
        return None;
    }
    for &child in args {
        live(terms, child)?;
    }
    let Sort::Array(sort) = terms.sort(term) else {
        return None;
    };
    (terms.sort(*base) == terms.sort(term)
        && terms.sort(*key) == &sort.index_sort
        && terms.sort(*value) == &sort.element_sort)
        .then_some([*base, *key, *value])
}

fn common_payloads(terms: &TermStore, symbol: &Symbol, args: &[TermId]) -> Option<[TermId; 2]> {
    if !matches!(symbol, Symbol::Named(name) if name == "=") {
        return None;
    }
    let [left, right] = args else {
        return None;
    };
    let a = store_parts(terms, *left)?;
    let b = store_parts(terms, *right)?;
    (terms.sort(*left) == terms.sort(*right) && a[..2] == b[..2]).then_some([a[2], b[2]])
}

fn equality_pair(terms: &TermStore, term: TermId, pair: [TermId; 2]) -> bool {
    matches!(terms.get(term), TermData::App(Symbol::Named(name), args)
        if name == "=" && terms.sort(term) == &Sort::Bool
            && (args.as_slice() == pair || args.as_slice() == [pair[1], pair[0]]))
}

fn raw_eq(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [left, right], Sort::Bool)
}

impl PropagationChainPlanner<'_> {
    /// An additive producer-spelling retry, not permission to rewrite ITEs.
    /// The exact no-ITE payload equality must still be the recorded target.
    pub(super) fn plan_array_payload_candidate(
        &mut self,
        cx: &mut PlanCx<'_>,
        symbol: &Symbol,
        args: &[TermId],
    ) -> Option<TermId> {
        if !matches!(symbol, Symbol::Named(name) if name == "=") || args.len() != 2 {
            return None;
        }
        cx.spend(2)?;
        let pair = common_payloads(self.terms, symbol, args)?;
        let candidate = self.terms.mk_eq_coerce_no_ite_expand(pair[0], pair[1]);
        (!cx.refuses_constant_conclusion(candidate) && equality_pair(self.terms, candidate, pair))
            .then_some(candidate)
    }

    pub(super) fn plan_array_fold(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
        folded: TermId,
        symbol: &Symbol,
        args: &[TermId],
        new_args: &[TermId],
        children: &[EqRes],
    ) -> Option<(TermId, ProofId)> {
        let mark = cx.mark();
        let const_read = matches!(symbol, Symbol::Named(name) if name == "select")
            && new_args.first().is_some_and(|&array| {
                live(self.terms, array).is_some() && self.terms.get_const_array(array).is_some()
            });
        let result = if const_read {
            self.plan_const_array_read_fold(cx, term, folded, args, new_args, children)
        } else {
            self.plan_array_fold_inner(cx, term, folded, symbol, args, new_args, children)
        };
        if result.is_none() {
            // Scratch terms may remain interned, but failed proof steps and
            // references to them cannot escape. Work is never refunded.
            cx.rollback(mark);
        }
        result
    }

    fn plan_array_fold_inner(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
        folded: TermId,
        symbol: &Symbol,
        args: &[TermId],
        new_args: &[TermId],
        children: &[EqRes],
    ) -> Option<(TermId, ProofId)> {
        if !matches!(symbol, Symbol::Named(name) if name == "select" || name == "=") {
            return None;
        }
        cx.spend(1)?;
        live(self.terms, term)?;
        live(self.terms, folded)?;
        if args.len() != new_args.len()
            || args.len() != children.len()
            || args.len() != 2
            || cx.refuses_constant_conclusion(folded)
            || self.terms.sort(term) != self.terms.sort(folded)
        {
            return None;
        }
        for &arg in args.iter().chain(new_args) {
            live(self.terms, arg)?;
        }
        if args
            .iter()
            .zip(new_args)
            .any(|(&old, &new)| self.terms.sort(old) != self.terms.sort(new))
        {
            return None;
        }
        if !matches!(self.terms.get(term), TermData::App(actual, original)
            if actual == symbol && original.as_slice() == args)
        {
            return None;
        }
        let is_select = matches!(symbol, Symbol::Named(name) if name == "select");
        if is_select {
            let [_, key, value] = store_parts(self.terms, new_args[0])?;
            if key != new_args[1]
                || value != folded
                || self.terms.sort(new_args[1]) != self.terms.sort(key)
            {
                return None;
            }
            let Sort::Array(original_sort) = self.terms.sort(args[0]) else {
                return None;
            };
            if self.terms.sort(args[1]) != &original_sort.index_sort
                || self.terms.sort(term) != &original_sort.element_sort
            {
                return None;
            }
        } else {
            let payloads = common_payloads(self.terms, symbol, new_args)?;
            if !equality_pair(self.terms, folded, payloads)
                || self.terms.sort(args[0]) != self.terms.sort(args[1])
            {
                return None;
            }
        }
        // Fixed-size nodes/clauses only; original children keep their existing
        // licensing proofs. The final strict checker meters schema replay.
        cx.spend(16)?;
        let premises = Self::congruence_premises(args, children, new_args)?;
        let rebuilt = self
            .terms
            .mk_app(symbol.clone(), new_args, self.terms.sort(term).clone());
        if rebuilt == term || rebuilt == folded {
            return None;
        }
        let first_eq = raw_eq(self.terms, term, rebuilt);
        let first = cx
            .chain
            .add_rule_step(AletheRule::Cong, vec![first_eq], premises, Vec::new());
        let middle_eq = raw_eq(self.terms, rebuilt, folded);
        let middle = if is_select {
            cx.chain.add_theory_lemma_with_kind(
                "arrays",
                vec![middle_eq],
                TheoryLemmaKind::ArraySelectStore { index_eq: true },
            )
        } else {
            self.plan_store_equality_iff(cx, rebuilt, folded, middle_eq)
        };
        let final_eq = raw_eq(self.terms, term, folded);
        let final_id = cx.chain.add_rule_step(
            AletheRule::Trans,
            vec![final_eq],
            vec![first, middle],
            Vec::new(),
        );
        Some((final_eq, final_id))
    }

    /// `(select A i)` whose array argument the pass replaced by the constant
    /// array `K = ((as const (Array I E)) v)`: `mk_select` folds that read to
    /// `v`, so there is no `store` for ROW1 and the pass never mints the
    /// `(select K i)` node the congruence leg above would route through.
    ///
    /// The child's own licensing equality closes it with ONE lemma of the
    /// existing `ArrayRowChain` sub-schema (E) — the exact read of a root
    /// equated to a constant array —
    ///
    /// ```text
    /// (cl (not (= A K)) (= (select A i) v))   ArrayRowChain (E)
    /// (cl (= A K))                            the child's derivation
    /// (cl (= (select A i) v))                 th_resolution
    /// ```
    ///
    /// SOUNDNESS: every model of `A = K` reads `v` from `A` at every index.
    /// The read keeps its AUTHORED index, which (E) admits at any well-sorted
    /// value, so an index rewrite needs no premise. No rule is added and no
    /// schema is widened: the strict checker re-derives the lemma from its
    /// clause alone, and any shape mismatch declines exactly as before.
    ///
    /// SCOPE: only a lane that opted in (`PlanCx::with_const_array_reads`),
    /// only for a target no leg-free plan derives (pinned Carcara has no rule
    /// for (E), so it prints as `hole`; see `PlanCx::const_array_reads`), and
    /// both lanes opt in only for a query that declares no datatype. With a
    /// record constant in play the array is a field constant (`a!data`) whose
    /// constant value is a selector-over-constructor reading of an authored
    /// equation, which no pinned-checker rule derives either: measured on
    /// a628c3b2a with the leg asked last but for datatypes too, two pinned
    /// fail-closed `unknown` answers (`model_checker_consumer_quantified_counterexample/
    /// deep_vec_iteration_query_false_unsat`, the ground-closure nested-`and`
    /// negative twin) became `unsat` with two and four `hole` steps.
    fn plan_const_array_read_fold(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
        folded: TermId,
        args: &[TermId],
        new_args: &[TermId],
        children: &[EqRes],
    ) -> Option<(TermId, ProofId)> {
        // The same unit the store leg spends before it declines a constant
        // array, so a leg-free plan spends exactly what it did before.
        cx.spend(1)?;
        if !cx.const_array_reads {
            cx.const_array_read_deferred = true;
            return None;
        }
        if args.len() != 2
            || new_args.len() != 2
            || children.len() != 2
            || cx.refuses_constant_conclusion(folded)
        {
            return None;
        }
        for &node in [term, folded].iter().chain(args).chain(new_args) {
            live(self.terms, node)?;
        }
        if !matches!(self.terms.get(term), TermData::App(Symbol::Named(name), original)
            if name == "select" && original.as_slice() == args)
        {
            return None;
        }
        let EqRes::Changed { to, eq_term, id } = children[0] else {
            return None;
        };
        let fill = self.terms.get_const_array(to)?;
        let Sort::Array(sort) = self.terms.sort(args[0]).clone() else {
            return None;
        };
        if to != new_args[0]
            || fill != folded
            || self.terms.get_const_array(args[0]).is_some()
            || self.terms.sort(to) != self.terms.sort(args[0])
            || self.terms.sort(args[1]) != &sort.index_sort
            || self.terms.sort(term) != &sort.element_sort
            || self.terms.sort(folded) != &sort.element_sort
            || !equality_pair(self.terms, eq_term, [args[0], to])
        {
            return None;
        }
        cx.spend(4)?;
        let conclusion = raw_eq(self.terms, term, folded);
        if !matches!(self.terms.get(conclusion), TermData::App(Symbol::Named(name), pair)
            if name == "=" && pair.as_slice() == [term, folded])
        {
            return None;
        }
        let premise = self.terms.mk_not_raw(eq_term);
        let lemma = cx.chain.add_theory_lemma_with_kind(
            "arrays",
            vec![premise, conclusion],
            TheoryLemmaKind::ArrayRowChain,
        );
        let resolved = cx.chain.add_rule_step(
            AletheRule::ThResolution,
            vec![conclusion],
            vec![lemma, id],
            Vec::new(),
        );
        Some((conclusion, resolved))
    }

    fn plan_store_equality_iff(
        &mut self,
        cx: &mut PlanCx<'_>,
        array_eq: TermId,
        payload_eq: TermId,
        equivalence: TermId,
    ) -> ProofId {
        let not_array = self.terms.mk_not_raw(array_eq);
        let not_payload = self.terms.mk_not_raw(payload_eq);
        // ArrayRowChain(I) proves the forward implication by reading the
        // common written key. Equal payloads imply equal stores by congruence
        // ONLY because both the base and the key are identical.
        let forward = cx.chain.add_theory_lemma_with_kind(
            "arrays",
            vec![not_array, payload_eq],
            TheoryLemmaKind::ArrayRowChain,
        );
        let reverse = cx.chain.add_theory_lemma_with_kind(
            "euf",
            vec![not_payload, array_eq],
            TheoryLemmaKind::EufCongruent,
        );
        let neg1 = cx.chain.add_rule_step(
            AletheRule::EquivNeg1,
            vec![equivalence, not_array, not_payload],
            Vec::new(),
            Vec::new(),
        );
        let neg2 = cx.chain.add_rule_step(
            AletheRule::EquivNeg2,
            vec![equivalence, array_eq, payload_eq],
            Vec::new(),
            Vec::new(),
        );
        let left = cx.chain.add_rule_step(
            AletheRule::ThResolution,
            vec![equivalence, not_array],
            vec![neg1, forward],
            Vec::new(),
        );
        let right = cx.chain.add_rule_step(
            AletheRule::ThResolution,
            vec![equivalence, array_eq],
            vec![neg2, reverse],
            Vec::new(),
        );
        cx.chain.add_rule_step(
            AletheRule::ThResolution,
            vec![equivalence],
            vec![left, right],
            Vec::new(),
        )
    }
}
