// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact unexpanded BV equality spelling in the source-backed array L1 lane.
//! This is congruence and, when needed, equality symmetry; not an ITE fold.

use super::*;

#[cfg(test)]
mod tests;

const RETRY_WORK: usize = 16;
const RETRY_BYTES: usize = 4096;

fn live(terms: &TermStore, term: TermId) -> bool {
    (term.0 as usize) < terms.len()
}

fn typed_ite(terms: &TermStore, term: TermId, sort: &Sort) -> Option<bool> {
    match terms.get(term) {
        TermData::Ite(condition, yes, no) => ([*condition, *yes, *no]
            .iter()
            .all(|&child| live(terms, child))
            && terms.sort(*condition) == &Sort::Bool
            && terms.sort(*yes) == sort
            && terms.sort(*no) == sort)
            .then_some(true),
        _ => Some(false),
    }
}

impl PropagationChainPlanner<'_> {
    /// Offer only the raw canonical equality that VariableSubstitution records.
    /// Its ordinary fold model may instead expand `ite(g,H,H1) = H` to `g`,
    /// while a positional raw retry misses the canonical operand swap.
    ///
    /// Nonempty immutable array units select this L1-only lane, not authority:
    /// every child equality still needs its freshly source-authenticated proof,
    /// and the enclosing record must match the exact returned target. The c7,
    /// generic propagation, connective and changed-child ITE lanes are untouched.
    pub(super) fn plan_scalar_canonical_fold(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
        symbol: &Symbol,
        args: &[TermId],
        new_args: &[TermId],
        children: &[EqRes],
    ) -> Option<(TermId, (TermId, ProofId))> {
        if cx.scalar_equality_mode != ScalarEqualityMode::ArrayCanonical
            || cx.array_units.is_empty()
            || !matches!(symbol, Symbol::Named(name) if name == "=")
            || args.len() != 2
            || new_args.len() != 2
            || children.len() != 2
        {
            return None;
        }
        if !(cx.array_progress?)(RETRY_WORK, RETRY_BYTES) {
            return None;
        }
        cx.spend(RETRY_WORK + RETRY_BYTES.div_ceil(64))?;
        if !live(self.terms, term)
            || args.iter().chain(new_args).any(|&id| !live(self.terms, id))
            || self.terms.sort(term) != &Sort::Bool
            || !matches!(self.terms.get(term), TermData::App(actual, operands)
                if actual == symbol && operands.as_slice() == args)
        {
            return None;
        }
        let sort = self.terms.sort(args[0]);
        if !matches!(sort, Sort::BitVec(width) if width.width > 0
            && width.width <= crate::api::MAX_API_BITVECTOR_WIDTH)
            || args
                .iter()
                .chain(new_args)
                .any(|&id| self.terms.sort(id) != sort)
        {
            return None;
        }
        // Validate both ITE roots, even when the first already establishes the
        // shape. No branch evaluation, recursive rewrite or carrier enumeration.
        let left_ite = typed_ite(self.terms, new_args[0], sort)?;
        let right_ite = typed_ite(self.terms, new_args[1], sort)?;
        if !left_ite && !right_ite || args == new_args {
            return None;
        }
        Self::congruence_premises(args, children, new_args)?;
        let ordered = if new_args[0] < new_args[1] {
            [new_args[0], new_args[1]]
        } else {
            [new_args[1], new_args[0]]
        };
        if ordered[0] == ordered[1] {
            return None;
        }
        let candidate = self.terms.mk_app(Symbol::named("="), ordered, Sort::Bool);
        if candidate == term || cx.refuses_constant_conclusion(candidate) {
            return None;
        }
        let mark = cx.mark();
        let result = match self.classify_fold_shape(candidate, symbol, args.len(), new_args) {
            FoldShape::Same(folded_args) => {
                self.plan_same_shape_fold(cx, term, candidate, args, &folded_args, children)
            }
            FoldShape::Swapped => self
                .plan_swapped_equality_fold(cx, term, candidate, symbol, args, new_args, children),
            FoldShape::Collapsing => None,
        };
        if result.is_none() {
            cx.rollback(mark);
        }
        result.map(|bridge| (candidate, bridge))
    }
}
