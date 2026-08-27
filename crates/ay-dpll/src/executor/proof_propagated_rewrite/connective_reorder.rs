// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bridge a rebuilt `and`/`or` to the CANONICAL spelling its pass produced.
//!
//! # The gap this closes
//!
//! Congruence reaches only the POSITIONAL rebuild `(and b1 … bn)` — argument
//! `i` replaced by argument `i`. The preprocessing passes rebuild Boolean
//! connectives through `TermStore::mk_and` / `mk_or`, which impose a canonical
//! argument order and drop duplicates, so a rewrite that changes an argument's
//! `TermId` can MOVE it. Measured on `dillig12_m`: `EqDiffVar` folds an
//! `ite`-headed conjunct of a BMC transition block to a freshly interned node,
//! which sorts to the END of its `and`, while congruence rebuilds it in place.
//! The two spellings then differ, the record bridge cannot reach the recorded
//! `after`, and the whole assertion falls back to a premiseless `trust`. This
//! was the single decline behind 172 of them.
//!
//! # The derivation
//!
//! With `A` the positional rebuild and `B` the canonical one, and `E := (= A B)`:
//!
//! ```text
//!   and:  (cl B ¬b1 … ¬bm)          :rule and_neg  :args (B)
//!         (cl ¬A ai)                :rule and_pos  :args (A)   [one per b]
//!         (cl B ¬A)                 resolve
//!   or:   (cl ¬A a1 … an)           :rule or_pos
//!         (cl B ¬ai)                :rule or_neg               [one per a]
//!         (cl B ¬A)                 resolve
//!   …the same with A and B swapped, then equiv_neg1/equiv_neg2 + resolution.
//! ```
//!
//! # Soundness
//!
//! No rule is added and none is widened: `and_pos`, `and_neg`, `or_pos`,
//! `or_neg`, `equiv_neg1`, `equiv_neg2` and resolution are all existing rules
//! the strict checker re-validates, and each emitted step names the exact
//! gate term it is about. The bridge is admitted only when the two argument
//! SETS are equal, which is what makes both implications derivable — the
//! `and` direction needs every canonical conjunct to be an indexed conjunct of
//! the rebuild, and the `or` direction needs every rebuilt disjunct to be a
//! disjunct of the canonical form. Set equality is checked here, and every
//! individual step is re-checked by the checker anyway; a set mismatch
//! declines and leaves today's behaviour.
//!
//! Note what set equality does NOT let through: `mk_and` also collapses a
//! `false` conjunct to `false` and drops `true`, which change the set, so
//! those folds are not this bridge's business and still decline here.

use super::*;

/// Node cost ceiling for one reorder bridge; a wider connective declines
/// rather than emit an unbounded chain.
const MAX_REORDER_ARGS: usize = 64;

impl PropagationChainPlanner<'_> {
    /// `(= term folded)` when `folded` is the canonical re-spelling of the
    /// positional rebuild of `term`.
    pub(super) fn plan_connective_reorder_fold(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
        folded: TermId,
        symbol: &Symbol,
        args: &[TermId],
        new_args: &[TermId],
        child_results: &[EqRes],
    ) -> Option<(TermId, ProofId)> {
        // SCOPED to the `EqDiffVar` lane. The bridge is sound for any producer
        // whose canonical rebuild permutes arguments, and the
        // `PropagateValues`/`VariableSubstitution` replay hits the same shape —
        // but offering it there DERIVES assertions that lane declines today,
        // which changes which UNSATs certify and therefore which lemmas PDR
        // keeps. Measured: doing so is what turns
        // `test_array_ghost_pair_route_certifies_safe_quantified_fixture` red
        // under a full-parallel `cargo test -p ay-chc --lib`. Widening it is a
        // separate change that needs its own corpus evidence.
        cx.eqdv_by_atom.as_ref()?;
        let connective = match symbol.name() {
            "and" => Connective::And,
            "or" => Connective::Or,
            _ => return None,
        };
        let folded_args = match self.terms.get(folded) {
            TermData::App(folded_symbol, folded_args) if folded_symbol == symbol => {
                folded_args.clone()
            }
            _ => return None,
        };
        if new_args.len() > MAX_REORDER_ARGS
            || folded_args.len() > MAX_REORDER_ARGS
            || new_args.is_empty()
            || folded_args.is_empty()
        {
            return None;
        }
        let rebuilt_set: HashSet<TermId> = new_args.iter().copied().collect();
        let folded_set: HashSet<TermId> = folded_args.iter().copied().collect();
        if rebuilt_set != folded_set {
            return None;
        }
        cx.spend(4usize.checked_mul(new_args.len() + folded_args.len())?)?;
        let sort = self.terms.sort(term).clone();
        let rebuilt = self.terms.mk_app(symbol.clone(), new_args, sort);
        if rebuilt == term || rebuilt == folded {
            return None;
        }
        // `mk_app` interns verbatim, but the conclusion must still name the
        // node the premises actually build.
        match self.terms.get(rebuilt) {
            TermData::App(rebuilt_symbol, rebuilt_args)
                if rebuilt_symbol == symbol && rebuilt_args.as_slice() == new_args => {}
            _ => return None,
        }
        let premises = Self::congruence_premises(args, child_results, new_args)?;
        let forward = self.plan_connective_implication(cx, connective, rebuilt, folded)?;
        let backward = self.plan_connective_implication(cx, connective, folded, rebuilt)?;
        let (rebuilt_to_folded, equivalence_id) =
            self.plan_equivalence_from_implications(cx, rebuilt, folded, forward, backward)?;
        let term_to_rebuilt = self
            .terms
            .mk_app(Symbol::named("="), [term, rebuilt], Sort::Bool);
        let congruence = cx.chain.add_rule_step(
            AletheRule::Cong,
            vec![term_to_rebuilt],
            premises,
            Vec::new(),
        );
        let term_to_folded = self
            .terms
            .mk_app(Symbol::named("="), [term, folded], Sort::Bool);
        let _ = rebuilt_to_folded;
        let transitivity = cx.chain.add_rule_step(
            AletheRule::Trans,
            vec![term_to_folded],
            vec![congruence, equivalence_id],
            Vec::new(),
        );
        Some((term_to_folded, transitivity))
    }

    /// `(cl to (not from))` for two `and`s / two `or`s over the same argument
    /// set.
    fn plan_connective_implication(
        &mut self,
        cx: &mut PlanCx<'_>,
        connective: Connective,
        from: TermId,
        to: TermId,
    ) -> Option<ProofId> {
        let from_args = self.connective_args(from)?;
        let to_args = self.connective_args(to)?;
        let not_from = self.terms.mk_not_raw(from);
        match connective {
            Connective::And => {
                // `(cl to ¬t1 … ¬tm)`, then resolve each `¬tj` against the
                // `and_pos` that extracts `tj` from `from`.
                let mut clause = Vec::with_capacity(to_args.len() + 1);
                clause.push(to);
                for &arg in &to_args {
                    clause.push(self.terms.mk_not_raw(arg));
                }
                let mut current = cx.chain.add_rule_step(
                    AletheRule::AndNeg,
                    clause.clone(),
                    Vec::new(),
                    vec![to],
                );
                // Iterate DISTINCT arguments: a resolution removes every
                // occurrence of its pivot, so a repeated argument would make
                // the second step resolve on a literal the clause no longer
                // has. `mk_and`/`mk_or` dedup, but the positional rebuild does
                // not, and `dillig12_m` really does carry duplicate disjuncts.
                for &arg in &distinct(&to_args) {
                    let position = from_args.iter().position(|&candidate| candidate == arg)?;
                    let extracted = cx.chain.add_rule_step(
                        AletheRule::AndPos(u32::try_from(position).ok()?),
                        vec![not_from, arg],
                        Vec::new(),
                        vec![from],
                    );
                    let negated = self.terms.mk_not_raw(arg);
                    clause.retain(|&literal| literal != negated);
                    if !clause.contains(&not_from) {
                        clause.push(not_from);
                    }
                    current = cx.chain.add_rule_step(
                        AletheRule::ThResolution,
                        clause.clone(),
                        vec![current, extracted],
                        Vec::new(),
                    );
                }
                (clause == vec![to, not_from]).then_some(current)
            }
            Connective::Or => {
                // `(cl ¬from f1 … fn)`, then resolve each `fi` against the
                // `or_neg` that folds it back into `to`.
                let mut clause = Vec::with_capacity(from_args.len() + 1);
                clause.push(not_from);
                clause.extend(from_args.iter().copied());
                let mut current = cx.chain.add_rule_step(
                    AletheRule::OrPos(0),
                    clause.clone(),
                    Vec::new(),
                    Vec::new(),
                );
                for &arg in &distinct(&from_args) {
                    if !to_args.contains(&arg) {
                        return None;
                    }
                    let negated = self.terms.mk_not_raw(arg);
                    let folded_back = cx.chain.add_rule_step(
                        AletheRule::OrNeg,
                        vec![to, negated],
                        Vec::new(),
                        Vec::new(),
                    );
                    clause.retain(|&literal| literal != arg);
                    if !clause.contains(&to) {
                        clause.push(to);
                    }
                    current = cx.chain.add_rule_step(
                        AletheRule::ThResolution,
                        clause.clone(),
                        vec![current, folded_back],
                        Vec::new(),
                    );
                }
                (clause == vec![not_from, to]).then_some(current)
            }
        }
    }

    fn connective_args(&self, term: TermId) -> Option<Vec<TermId>> {
        match self.terms.get(term) {
            TermData::App(_, args) => Some(args.clone()),
            _ => None,
        }
    }
}

/// First-occurrence-order deduplication.
fn distinct(args: &[TermId]) -> Vec<TermId> {
    let mut seen: HashSet<TermId> = HashSet::default();
    args.iter()
        .copied()
        .filter(|arg| seen.insert(*arg))
        .collect()
}

#[derive(Clone, Copy)]
pub(super) enum Connective {
    And,
    Or,
}
