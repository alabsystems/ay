// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact Boolean spelling in the existing original-source array retry.
//! No generic OR policy changes: the record must still match the complete
//! canonical target, and all child equalities retain their original authority.

use super::*;

impl PropagationChainPlanner<'_> {
    pub(super) fn charge_array_connective_retry(
        cx: &mut PlanCx<'_>,
        operands: usize,
    ) -> Option<()> {
        if cx.scalar_equality_mode != ScalarEqualityMode::ArrayCanonical
            || cx.array_units.is_empty()
        {
            return None;
        }
        // Covers the bounded temporary vectors and proof suffix. Existing
        // equivalence/reorder primitives additionally keep their local charges.
        let work = operands.checked_mul(8)?.checked_add(32)?;
        let bytes = operands.checked_add(16)?.checked_mul(256)?;
        if !(cx.array_progress?)(work, bytes) {
            return None;
        }
        cx.spend(work.checked_add(bytes.div_ceil(64))?)
    }

    pub(super) fn plan_array_duplicate_and_fold(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
        folded: TermId,
        symbol: &Symbol,
        args: &[TermId],
        new_args: &[TermId],
        children: &[EqRes],
    ) -> Option<(TermId, ProofId)> {
        if !matches!(symbol, Symbol::Named(name) if name == "and")
            || new_args.len() < 2
            || args.len() != new_args.len()
            || children.len() != args.len()
            || self.terms.sort(term) != &Sort::Bool
            || self.terms.sort(folded) != &Sort::Bool
            || cx.refuses_constant_conclusion(folded)
            || args.iter().any(|&arg| self.terms.sort(arg) != &Sort::Bool)
            || !new_args.iter().all(|&arg| arg == folded)
            || !matches!(self.terms.get(term), TermData::App(head, actual)
                if head == symbol && actual.as_slice() == args)
        {
            return None;
        }
        Self::charge_array_connective_retry(cx, new_args.len())?;
        let premises = Self::congruence_premises(args, children, new_args)?;
        let mark = cx.mark();
        let result = (|| {
            let rebuilt = self.terms.mk_app(symbol.clone(), new_args, Sort::Bool);
            if rebuilt == term || rebuilt == folded {
                return None;
            }
            if !matches!(self.terms.get(rebuilt), TermData::App(head, actual)
                if head == symbol && actual.as_slice() == new_args)
            {
                return None;
            }
            let not_rebuilt = self.terms.mk_not_raw(rebuilt);
            let not_folded = self.terms.mk_not_raw(folded);
            let forward = cx.chain.add_rule_step(
                AletheRule::AndPos(0),
                vec![not_rebuilt, folded],
                Vec::new(),
                vec![rebuilt],
            );
            // AndNeg needs the full original multiplicity. Contraction is an
            // explicit checked step, not silently deduplicated rule arguments.
            let mut clause = vec![rebuilt];
            clause.extend(std::iter::repeat_n(not_folded, new_args.len()));
            let negative =
                cx.chain
                    .add_rule_step(AletheRule::AndNeg, clause, Vec::new(), vec![rebuilt]);
            let backward = cx.chain.add_rule_step(
                AletheRule::Contraction,
                vec![rebuilt, not_folded],
                vec![negative],
                Vec::new(),
            );
            let (_, equivalence) =
                self.plan_equivalence_from_implications(cx, rebuilt, folded, forward, backward)?;
            let first = self
                .terms
                .mk_app(Symbol::named("="), [term, rebuilt], Sort::Bool);
            let congruence =
                cx.chain
                    .add_rule_step(AletheRule::Cong, vec![first], premises, Vec::new());
            let equality = self
                .terms
                .mk_app(Symbol::named("="), [term, folded], Sort::Bool);
            let id = cx.chain.add_rule_step(
                AletheRule::Trans,
                vec![equality],
                vec![congruence, equivalence],
                Vec::new(),
            );
            Some((equality, id))
        })();
        if result.is_none() {
            cx.rollback(mark);
        }
        result
    }
}
