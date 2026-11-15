// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifiers nested in guarded instances (#guarded-nested-quantifiers).
//!
//! A guarded instance `B[t̄]` of an un-entailed universal `Q = ∀x̄.B` can
//! itself carry a quantifier. Verus writes `let b = forall|x| P(x) ==>
//! forall|z| R(x, z)` as `(= b (forall ((x Poly)) (=> (P x) (forall ((z Poly))
//! (R x z)))))`: the outer universal sits under a Boolean `=`, so it is not
//! entailed and gets a proxy `q`, and its instance at `x := t` is
//! `(=> (P t) (forall ((z Poly)) (R t z)))`. The guarded lane used to drop
//! such an instance whole, so the inner universal was never instantiated.
//! z3 instantiates it as soon as the instance makes its atom true.
//!
//! Here every maximal quantifier `Q'` of the exact instance gets a fresh
//! Boolean proxy `q'`, exactly as a quantifier of an assertion does. The
//! guarded clause becomes `(or (not q) B[t̄][Q' := q'])`, and the E-matching
//! campaign offers `Q'` to its later rounds as a guarded-only quantifier, so
//! the instances of `Q'` become clauses `(or (not q') C[s̄])` in turn.
//!
//! # Soundness
//!
//! It is the proxy abstraction's model extension, applied once more (see
//! [`super::quantifier_proxy`]). `Q'` is closed: the outer binders are
//! replaced by ground terms, the substitution is capture-safe, and the
//! collector refuses a `let`. So given a model `M` of the authored problem,
//! already extended by `q := ⟦Q⟧_M`, extend it again by `q' := ⟦Q'⟧_M`;
//! `q'` is fresh, so no other assertion changes value. The clause
//! `(or (not q) B[t̄])` holds in that model (the guarded lane's argument), and
//! replacing the closed subterm `Q'` by a symbol with the same value keeps it
//! true. Each clause `(or (not q') C[s̄])` holds by the guarded lane's argument
//! for `Q'`. So a refutation of the extended set refutes the authored one. A
//! nested proxy exists only where its parent's proxy does, so the abstraction
//! is already active and no `sat` is published over it. A position or
//! polarity of `Q'` inside `B` plays no part in the argument.
//!
//! The rewrite is checked by the reverse substitution, as purify's is.
//!
//! # Existential duals (#guarded-existential-duals)
//!
//! `collect_quantifiers` reads `(not (exists x̄ φ))` as the universal
//! `∀x̄.¬φ`, a fresh term no proxy names, so its guarded records used to be
//! dropped. A Verus goal that asserts an existential sits in a disjunct of
//! the negated goal, so exactly those records carry the witness instances.
//! Each is now guarded by the existential's own proxy `q`: `(or q ¬φ[t̄])`.
//! In the extended model `q := ⟦∃x̄.φ⟧`, so either `q` is true or `¬φ[t̄]`
//! holds at every ground `t̄`; the clause is the one
//! #skolem-guarded-proxy-instances asserts at Skolem constants.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Symbol, TermData, TermId, TermStore};
use ay_core::Sort;

use super::super::super::Executor;
use super::quantifier_proxy;
use crate::ematching::{contains_quantifier, ForallInstantiationProvenance};

/// Nested quantifiers the E-matching campaign offers to its rounds, and
/// proxies one guarded pass may mint for them. Past the bound a nested
/// quantifier is not matched, or its record is dropped as before this lane:
/// both cost only completeness.
pub(super) const MAX_NESTED_QUANTIFIERS: usize = 256;

/// The maximal quantifiers of an exact guarded `instance` and its ground
/// skeleton: the instance with each of them replaced by `true`. The skeleton
/// offers the instance's ground terms to later rounds as match-only terms;
/// it is never asserted. `None` when the instance carries no quantifier, or
/// on the collector's refusals.
pub(super) fn nested_parts(
    terms: &mut TermStore,
    instance: TermId,
) -> Option<(Vec<TermId>, TermId)> {
    if !contains_quantifier(terms, instance) {
        return None;
    }
    let nested = quantifier_proxy::maximal_quantifiers_of(terms, instance)?;
    if nested.is_empty() {
        return None;
    }
    let truth = terms.mk_bool(true);
    let map: HashMap<TermId, TermId> = nested
        .iter()
        .map(|&quantifier| (quantifier, truth))
        .collect();
    let skeleton = quantifier_proxy::replace_quantifiers(terms, instance, &map)?;
    if contains_quantifier(terms, skeleton) {
        return None;
    }
    Some((nested, skeleton))
}

/// The NNF dual `∀x̄.¬φ` of `∃x̄.φ`, built as `collect_quantifiers` builds
/// it for `(not (exists ...))`, so the two are the same interned term.
pub(super) fn existential_dual(terms: &mut TermStore, quantifier: TermId) -> Option<TermId> {
    let TermData::Exists(vars, body, triggers) = terms.get(quantifier).clone() else {
        return None;
    };
    let negated = terms.mk_not(body);
    let dual = terms.mk_forall_with_triggers(vars, negated, triggers);
    terms.copy_quantifier_metadata(quantifier, dual);
    Some(dual)
}

/// The proxy that guards a record's clause, and whether the clause's first
/// literal is its negation (a proxied universal) or the proxy itself (the
/// dual of a proxied existential).
struct Guard {
    proxy: TermId,
    negated: bool,
}

/// What one guarded record gave the guarded pass.
pub(super) enum GuardedOutcome {
    /// No guard: neither a proxied universal nor the dual of a proxied
    /// existential (yet; a nested proxy minted later may supply one).
    NoGuard,
    /// The source is not a `Forall`, or the exact substitution was refused.
    NoInstance,
    /// A nested quantifier has no proxy, or the reverse substitution failed.
    NestedRefused,
    /// The guarded clause and the exact instance it carries.
    Clause { clause: TermId, instance: TermId },
}

impl Executor {
    /// The guard of a record of `quantifier`: its own proxy, negated, for a
    /// proxied universal; the existential's proxy for the dual of a proxied
    /// existential (#guarded-existential-duals). A record of the dual
    /// `∀x̄.¬φ` is guarded by the existential's proxy `q` itself: `(or q
    /// ¬φ[t̄])` holds under the proxy model extension, since a false
    /// existential makes `¬φ[t̄]` true at every ground `t̄`. It is the clause
    /// #skolem-guarded-proxy-instances asserts at Skolem constants, here at
    /// E-matched bindings.
    ///
    /// The dual is recognised by its binders, its triggers and its body
    /// being `mk_not` of the existential's, which is how `collect_quantifiers`
    /// builds it; `mk_not` is memoised, so the check mints no term for a dual
    /// that exists.
    fn record_guard(&mut self, quantifier: TermId) -> Option<Guard> {
        if let Some(&proxy) = self.quantifier_proxies.get(&quantifier) {
            return Some(Guard {
                proxy,
                negated: true,
            });
        }
        if let Some(&proxy) = self.guarded_existential_duals.get(&quantifier) {
            return Some(Guard {
                proxy,
                negated: false,
            });
        }
        let TermData::Forall(vars, body, triggers) = self.ctx.terms.get(quantifier).clone() else {
            return None;
        };
        let mut existentials: Vec<(TermId, TermId)> = self
            .quantifier_proxies
            .iter()
            .map(|(&existential, &proxy)| (existential, proxy))
            .collect();
        existentials.sort_unstable_by_key(|(existential, _)| existential.index());
        for (existential, proxy) in existentials {
            let TermData::Exists(e_vars, e_body, e_triggers) =
                self.ctx.terms.get(existential).clone()
            else {
                continue;
            };
            if e_vars == vars && e_triggers == triggers && self.ctx.terms.mk_not(e_body) == body {
                self.guarded_existential_duals.insert(quantifier, proxy);
                return Some(Guard {
                    proxy,
                    negated: false,
                });
            }
        }
        None
    }

    /// Mint a proxy for every maximal quantifier of `instance` that has none,
    /// and record the universal each one is matched through. Returns how
    /// many proxies it minted, at most `budget`.
    fn mint_nested_proxies(&mut self, instance: TermId, budget: usize) -> usize {
        let Some(nested) = quantifier_proxy::maximal_quantifiers_of(&self.ctx.terms, instance)
        else {
            return 0;
        };
        let mut minted = 0;
        for quantifier in nested {
            if minted >= budget {
                break;
            }
            if self.quantifier_proxies.contains_key(&quantifier) {
                continue;
            }
            let proxy = self.ctx.terms.mk_fresh_var("qproxy", Sort::Bool);
            self.quantifier_proxies.insert(quantifier, proxy);
            minted += 1;
            match self.ctx.terms.get(quantifier) {
                TermData::Forall(..) => self.guarded_nested_universals.push(quantifier),
                TermData::Exists(..) => {
                    if let Some(dual) = existential_dual(&mut self.ctx.terms, quantifier) {
                        self.guarded_existential_duals.insert(dual, proxy);
                        self.guarded_nested_universals.push(dual);
                    }
                }
                _ => {}
            }
        }
        minted
    }

    /// The guarded clause of one record, built in the order the guarded pass
    /// always built it (guard, exact instance, then the clause), so a record
    /// without a nested quantifier mints exactly the terms it did before.
    /// `minted` counts the nested proxies of this pass against
    /// [`MAX_NESTED_QUANTIFIERS`].
    pub(super) fn guarded_clause(
        &mut self,
        record: &ForallInstantiationProvenance,
        minted: &mut usize,
    ) -> GuardedOutcome {
        let Some(guard) = self.record_guard(record.quantifier) else {
            return GuardedOutcome::NoGuard;
        };
        // Defence in depth: the matcher already refuses `Exists`, and
        // existential instantiation would be unsound under ANY guard.
        if !matches!(self.ctx.terms.get(record.quantifier), TermData::Forall(..)) {
            debug_assert!(
                false,
                "BUG (#quantifier-guarded-instances): a guarded record's source is not a Forall"
            );
            return GuardedOutcome::NoInstance;
        }
        let Some(instance) = self.exact_forall_instance(record.quantifier, &record.binding) else {
            return GuardedOutcome::NoInstance;
        };
        let body = if contains_quantifier(&self.ctx.terms, instance) {
            let budget = MAX_NESTED_QUANTIFIERS.saturating_sub(*minted);
            *minted += self.mint_nested_proxies(instance, budget);
            match self.abstract_nested_quantifiers(instance) {
                Some(abstracted) => abstracted,
                None => return GuardedOutcome::NestedRefused,
            }
        } else {
            instance
        };
        let literal = if guard.negated {
            self.ctx.terms.mk_not_raw(guard.proxy)
        } else {
            guard.proxy
        };
        let clause = self
            .ctx
            .terms
            .mk_app(Symbol::named("or"), [literal, body], Sort::Bool);
        GuardedOutcome::Clause { clause, instance }
    }

    /// The universals an interleaved E-matching round offers as guarded-only
    /// quantifiers: those a guarded instance brought in, which no assertion
    /// carries.
    pub(in crate::executor::quantifier_loop) fn proxied_universals(&self) -> Vec<TermId> {
        self.guarded_nested_universals.clone()
    }

    /// `instance` with each of its maximal quantifiers replaced by its proxy.
    /// `None` when one has no proxy, on the collector's refusals, or when the
    /// reverse substitution does not give back `instance` exactly.
    pub(super) fn abstract_nested_quantifiers(&mut self, instance: TermId) -> Option<TermId> {
        let nested = quantifier_proxy::maximal_quantifiers_of(&self.ctx.terms, instance)?;
        let mut forward: HashMap<TermId, TermId> = HashMap::default();
        let mut reverse: HashMap<TermId, TermId> = HashMap::default();
        for quantifier in nested {
            let proxy = *self.quantifier_proxies.get(&quantifier)?;
            forward.insert(quantifier, proxy);
            if reverse.insert(proxy, quantifier).is_some() {
                return None;
            }
        }
        let rewritten =
            quantifier_proxy::replace_quantifiers(&mut self.ctx.terms, instance, &forward)?;
        let restored =
            quantifier_proxy::replace_quantifiers(&mut self.ctx.terms, rewritten, &reverse)?;
        if restored != instance || contains_quantifier(&self.ctx.terms, rewritten) {
            return None;
        }
        Some(rewritten)
    }
}
