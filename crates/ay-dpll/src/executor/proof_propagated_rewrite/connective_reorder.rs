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
//!         (cl ¬A ai)                :rule and_pos  :args (A)   [one per distinct b]
//!         (cl B ¬A)                 ONE n-ary th_resolution over all of them
//!   or:   (cl ¬A a1 … an)           :rule or_pos
//!         (cl B ¬ai)                :rule or_neg               [one per distinct a]
//!         (cl B ¬A)                 ONE n-ary th_resolution over all of them
//!   …the same with A and B swapped, then equiv_neg1/equiv_neg2 + resolution.
//! ```
//!
//! Every step but the gate has a constant-width clause, so the bridge is
//! linear in the arity, and the checker folds the unambiguous chain in the
//! total premise size (`checker/resolution_chain_fold.rs`). There is no arity
//! cap: the binary chain this replaced re-stated the shrinking clause at
//! every step (`Θ(k²)` literals), and a 64-argument cap kept that bounded;
//! a reach-encoded join wider than 64 then lost the bridge and fell back to
//! the replay lane (measured: the a5 row certified at 64 index disjuncts and
//! was withheld at 65 with the replay off).
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
//! # The IDENTITY-DROP half
//!
//! `mk_and`/`mk_or` also DROP the connective's identity element — a `true`
//! conjunct, a `false` disjunct — which changes the argument SET, so exact
//! set equality declined it. That is the dominant shape whenever a
//! substitution turns a conjunct into `true`: `VariableSubstitution` rebuilds
//! through `mk_and`, so the pass really wrote the shorter `and`, while
//! congruence can only reach the positional rebuild that still carries the
//! `true`. (Measured on the deductive-checksgen `a5_two_next_if_ok_sym` obligation:
//! two conjuncts of each `or` branch fold to `true` under the recorded
//! `n |-> a__slice_len` / `_5 |-> (< n m)` chain, the bridge could not reach
//! the recorded `after`, and the whole refutation published
//! `unknown (incomplete self-check-rejected)`.)
//!
//! The set check therefore admits ONE further shape: the rebuilt set minus
//! the connective's identity equals the canonical set. The derivation is the
//! same clause chain, with the identity literal discharged against the
//! premise-free Alethe axiom that proves it — `true` proves `(cl true)`,
//! `false` proves `(cl (not false))` — both re-validated in strict mode by
//! the checker's 0-variable exhaustive Boolean tautology evaluator. Nothing
//! is taken on faith: a wrong identity claim simply fails to resolve and the
//! bridge declines.
//!
//! Note what this still does NOT let through: `mk_and` also COLLAPSES a
//! `false` conjunct to `false` (and `mk_or` a `true` disjunct to `true`),
//! which is not an argument-set relation at all, so those folds are not this
//! bridge's business and still decline here.
//!
//! # Scope
//!
//! The bridge serves the `EqDiffVar` lane, the array lane's canonical retry
//! (after its positional first attempt), and the scalar replay of recorded
//! `VariableSubstitution`/`PropagateValues` rewrites, for `and` and `or`
//! alike. Until 2026-10-02 the scalar lane reordered `and` only: offering
//! `or` there had been measured on 2026-08-21 to turn
//! `test_array_ghost_pair_route_certifies_safe_quantified_fixture` red under a
//! full-parallel `ay-chc` test run, back when that test gave its PDR solve a
//! 4.2 s wall-clock sub-budget that suite-wide contention could exhaust on its
//! own (the test has passed the route a deadline since that evening).
//! Re-measured with `or` admitted: the whole `ay-chc` unit suite and every
//! ghost-pair test pass unchanged, no CHC or SMT corpus row that both builds
//! decide is decided differently, and CHC solver transcripts certify their
//! UNSAT checks sooner (one reached its third verdict at 11 s, not 85 s).
//! The deductive-checksgen `a5_two_next_if_ok_sym` reach row needs it: its authored
//! index disjunction is re-sorted by `mk_or` after `a__slice_len |-> _13`,
//! and without the bridge that leaf stayed a premiseless `trust` step.

use super::*;

mod array_canonical;
#[cfg(test)]
mod tests;

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
        let scoped_retry = cx.scalar_equality_mode == ScalarEqualityMode::ArrayCanonical
            && !cx.array_units.is_empty();
        let mark = cx.mark();
        let result = self.plan_connective_reorder_fold_inner(
            cx,
            term,
            folded,
            symbol,
            args,
            new_args,
            child_results,
        );
        if scoped_retry && result.is_none() {
            cx.rollback(mark);
        }
        result
    }

    fn plan_connective_reorder_fold_inner(
        &mut self,
        cx: &mut PlanCx<'_>,
        term: TermId,
        folded: TermId,
        symbol: &Symbol,
        args: &[TermId],
        new_args: &[TermId],
        child_results: &[EqRes],
    ) -> Option<(TermId, ProofId)> {
        // Exact AND and OR reordering both occur when recorded scalar
        // substitution changes an argument's TermId: `VariableSubstitution`
        // rebuilds Boolean connectives through `mk_and`/`mk_or`, so the pass
        // really wrote the canonical spelling. Permit the same checked
        // set-equality bridge for both connectives without a fresh-definition
        // channel (see the module doc, "Scope"). The array lane's OR retry
        // additionally charges its shared progress callback below.
        let array_retry = cx.scalar_equality_mode == ScalarEqualityMode::ArrayCanonical
            && !cx.array_units.is_empty();
        // The array record bridge first asks for its historical positional
        // spelling. A successful canonical fold would preempt the raw
        // congruence fallback even when that record names the positional form.
        // Keep that first attempt intact; only its ArrayCanonical retry opts
        // into reordering. The no-array lane and the EqDiffVar lane reorder.
        if !cx.array_units.is_empty()
            && cx.scalar_equality_mode == ScalarEqualityMode::Legacy
            && cx.eqdv_by_atom.is_none()
        {
            return None;
        }
        let connective = match symbol.name() {
            "and" => Connective::And,
            "or" => Connective::Or,
            _ => return None,
        };
        if new_args.is_empty()
            || self.terms.sort(term) != &Sort::Bool
            || self.terms.sort(folded) != &Sort::Bool
            || new_args
                .iter()
                .any(|&arg| self.terms.sort(arg) != &Sort::Bool)
        {
            return None;
        }
        if array_retry
            && symbol.name() == "and"
            && new_args.len() >= 2
            && new_args.iter().all(|&arg| arg == folded)
        {
            return self.plan_array_duplicate_and_fold(
                cx,
                term,
                folded,
                symbol,
                args,
                new_args,
                child_results,
            );
        }
        if symbol.name() == "or" && cx.eqdv_by_atom.is_none() {
            if !matches!(symbol, Symbol::Named(name) if name == "or")
                || args.len() != new_args.len()
                || child_results.len() != args.len()
                || args.iter().any(|&arg| self.terms.sort(arg) != &Sort::Bool)
            {
                return None;
            }
            if array_retry {
                // Charge before cloning the folded vector or building argument sets.
                let folded_len = match self.terms.get(folded) {
                    TermData::App(head, children) if head == symbol && !children.is_empty() => {
                        children.len()
                    }
                    _ => return None,
                };
                Self::charge_array_connective_retry(cx, new_args.len() + folded_len)?;
            }
        }
        let folded_args = match self.terms.get(folded) {
            TermData::App(folded_symbol, folded_args)
                if folded_symbol == symbol && !folded_args.is_empty() =>
            {
                folded_args.clone()
            }
            _ => return None,
        };
        let rebuilt_set: HashSet<TermId> = new_args.iter().copied().collect();
        let folded_set: HashSet<TermId> = folded_args.iter().copied().collect();
        // Equal sets are the reorder/dedup shape. The one admitted
        // inequality is the canonical constructors' identity drop — see the
        // module doc; the implication chain below discharges that literal
        // against the matching Alethe axiom, so an identity the pass did not
        // actually drop cannot be smuggled through.
        let identity = self.connective_identity(connective);
        if rebuilt_set != folded_set {
            let mut without_identity = rebuilt_set.clone();
            if !without_identity.remove(&identity) || without_identity != folded_set {
                return None;
            }
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
    /// The connective's identity element: the argument its canonical
    /// constructor drops (`true` from an `and`, `false` from an `or`).
    fn connective_identity(&mut self, connective: Connective) -> TermId {
        match connective {
            Connective::And => self.terms.true_term(),
            Connective::Or => self.terms.false_term(),
        }
    }

    /// The premise-free Alethe axiom proving the identity literal this
    /// bridge has to discharge: `true` proves `(cl true)` and `false` proves
    /// `(cl (not false))`. Both are re-validated in strict mode by the
    /// checker's exhaustive 0-variable Boolean tautology evaluator, so
    /// emitting one grants no authority the checker does not re-derive.
    fn plan_identity_axiom(&mut self, cx: &mut PlanCx<'_>, connective: Connective) -> ProofId {
        match connective {
            Connective::And => {
                let true_term = self.terms.true_term();
                cx.chain
                    .add_rule_step(AletheRule::True, vec![true_term], Vec::new(), Vec::new())
            }
            Connective::Or => {
                let false_term = self.terms.false_term();
                let not_false = self.terms.mk_not_raw(false_term);
                cx.chain
                    .add_rule_step(AletheRule::False, vec![not_false], Vec::new(), Vec::new())
            }
        }
    }

    /// `(cl to (not from))` (`and`) / `(cl (not from) to)` (`or`) for two
    /// applications of one connective over the same argument set, up to the
    /// identity the canonical constructor drops.
    ///
    /// ONE n-ary resolution, linear in the arity: the gate clause of the
    /// connective (`and_neg` of `to`, `or_pos` of `from`) against one
    /// projection per DISTINCT argument (`and_pos` out of `from`, `or_neg`
    /// into `to`; the identity literal against its premise-free axiom). The
    /// projections all carry the same second literal, which resolution
    /// merges, and the checker folds the unambiguous chain incrementally
    /// (`checker/resolution_chain_fold.rs`). The binary chain this replaces
    /// re-stated the whole shrinking clause at every step, `Θ(k²)` literals
    /// for a `k`-ary connective, which is why a `k`-argument cap stood here.
    fn plan_connective_implication(
        &mut self,
        cx: &mut PlanCx<'_>,
        connective: Connective,
        from: TermId,
        to: TermId,
    ) -> Option<ProofId> {
        let from_args = self.connective_args(from)?;
        let to_args = self.connective_args(to)?;
        let identity = self.connective_identity(connective);
        let not_from = self.terms.mk_not_raw(from);
        let mut premises = Vec::new();
        let mut projected = false;
        match connective {
            Connective::And => {
                // `(cl to ¬t1 … ¬tm)`, every `¬tj` resolved against the
                // `and_pos` that extracts `tj` from `from`. A conjunct of `to`
                // that `from` does not carry can only be the identity `true`
                // the canonical constructor dropped; it resolves against the
                // `true` axiom and contributes no `¬from`.
                let mut gate = Vec::with_capacity(to_args.len() + 1);
                gate.push(to);
                for &arg in &to_args {
                    gate.push(self.terms.mk_not_raw(arg));
                }
                premises.push(cx.chain.add_rule_step(
                    AletheRule::AndNeg,
                    gate,
                    Vec::new(),
                    vec![to],
                ));
                let positions = first_positions(&from_args);
                for arg in distinct(&to_args) {
                    let extracted = match positions.get(&arg) {
                        Some(&position) => {
                            projected = true;
                            cx.chain.add_rule_step(
                                AletheRule::AndPos(u32::try_from(position).ok()?),
                                vec![not_from, arg],
                                Vec::new(),
                                vec![from],
                            )
                        }
                        None if arg == identity => self.plan_identity_axiom(cx, connective),
                        None => return None,
                    };
                    premises.push(extracted);
                }
                let conclusion = vec![to, not_from];
                projected.then(|| {
                    cx.chain.add_rule_step(
                        AletheRule::ThResolution,
                        conclusion,
                        premises,
                        Vec::new(),
                    )
                })
            }
            Connective::Or => {
                // `(cl ¬from f1 … fn)`, every `fi` resolved against the
                // `or_neg` that folds it back into `to`. A disjunct of `from`
                // that `to` does not carry can only be the identity `false`;
                // `(cl (not false))` resolves it away and introduces no `to`.
                let mut gate = Vec::with_capacity(from_args.len() + 1);
                gate.push(not_from);
                gate.extend(from_args.iter().copied());
                premises.push(cx.chain.add_rule_step(
                    AletheRule::OrPos(0),
                    gate,
                    Vec::new(),
                    Vec::new(),
                ));
                let to_set: HashSet<TermId> = to_args.iter().copied().collect();
                for arg in distinct(&from_args) {
                    let folded_back = if to_set.contains(&arg) {
                        projected = true;
                        let negated = self.terms.mk_not_raw(arg);
                        cx.chain.add_rule_step(
                            AletheRule::OrNeg,
                            vec![to, negated],
                            Vec::new(),
                            Vec::new(),
                        )
                    } else if arg == identity {
                        self.plan_identity_axiom(cx, connective)
                    } else {
                        return None;
                    };
                    premises.push(folded_back);
                }
                let conclusion = vec![not_from, to];
                projected.then(|| {
                    cx.chain.add_rule_step(
                        AletheRule::ThResolution,
                        conclusion,
                        premises,
                        Vec::new(),
                    )
                })
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

/// Each argument's FIRST position, the index an `and_pos` extraction names.
fn first_positions(args: &[TermId]) -> HashMap<TermId, usize> {
    let mut positions = HashMap::default();
    for (position, &arg) in args.iter().enumerate() {
        positions.entry(arg).or_insert(position);
    }
    positions
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
