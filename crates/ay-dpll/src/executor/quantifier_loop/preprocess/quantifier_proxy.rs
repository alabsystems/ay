// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Quantifier-atom purification (#quantifier-proxy-abstraction).
//!
//! `flatten_and_strip_quantifiers` used to end with a single statement:
//!
//! ```text
//! self.ctx.assertions.retain(|&a| !contains_quantifier(&self.ctx.terms, a));
//! ```
//!
//! i.e. every assertion that mentions a quantifier ANYWHERE was deleted whole.
//! For an UltimateAutomizer / Boogie verification condition shaped
//! `(or (not G1) … (not Gn) (forall x̄. ¬φ))` that throws away the GROUND
//! disjuncts as well as the quantifier, and the ground solver then reports
//! `num_conflicts=0 num_decisions=0` — it never saw the goal.
//!
//! This pass replaces each *maximal* quantifier subterm of such an assertion by
//! a fresh Boolean variable and keeps the rewritten (now quantifier-free)
//! assertion, so the ground solver finally sees the goal. It changes nothing
//! about instantiation: instances are still unit-pushed exactly as before, and
//! only for the universals the assertion set entails.
//!
//! # Soundness: the abstraction is an OVER-approximation
//!
//! Let `σ` map each targeted quantifier `Q_i` to its fresh Boolean symbol
//! `q_i`. Each `Q_i` is a maximal quantifier subterm of an assertion, hence a
//! CLOSED Boolean-valued term, so `⟦Q_i⟧_M` is well defined in any model `M` of
//! the authored assertions `A`. `mk_fresh_var` checks `TermStore::names`, so
//! every `q_i` is fresh: it occurs in no authored assertion and in no other
//! `Q_j`. Given `M ⊨ A`, extend it to `M'` by `q_i := ⟦Q_i⟧_M`; `M'` agrees
//! with `M` on every problem symbol, and replacing a Boolean subterm by a
//! symbol carrying the same truth value preserves truth, so `M' ⊨ σ(A)`.
//!
//! Therefore `SAT(A) ⟹ SAT(σ(A))`, equivalently
//!
//! > **`σ(A)` UNSAT ⟹ `A` UNSAT** — at any polarity, in any position.
//!
//! The converse does NOT hold: a model of `σ(A)` assigns the proxies freely and
//! nothing ties `M(q_i)` to `⟦Q_i⟧`. Every solve in which this pass fired must
//! therefore publish `unknown` rather than `sat`; that is enforced by
//! `Executor::quantifier_abstraction_active` (see the head of
//! `classify_quantifier_result` and the publication sweep at the tail of
//! `map_quantifier_result`), not by anything in this module.
//!
//! The baseline behaviour — deleting the assertion — is *also* an
//! over-approximation (dropping a conjunct only weakens). This pass replaces it
//! with a strictly TIGHTER over-approximation, which is why it can only add
//! refutations relative to baseline, never remove the soundness argument for
//! one.
//!
//! # Why the rewrite is owned here
//!
//! `TermStore::substitute_terms_recording` would do the same job today because
//! `substitute_terms_inner` consults the substitution map BEFORE dispatching on
//! `TermData`, so it never descends under a binder whose node is itself a map
//! key. That ordering is undocumented and load-bearing for capture-safety, so
//! this pass owns a walk that stops at every `Forall`/`Exists` node by
//! construction and cannot be broken by a change over in `ay-core`.
//!
//! # Fail-closed refusals
//!
//! * an assertion containing a `TermData::Let` anywhere is left alone (the
//!   binder's scoping is not modelled by this walk);
//! * an assertion containing a `TermData` variant this walk does not recognise
//!   (`TermData` is `#[non_exhaustive]`) is left alone;
//! * an assertion all of whose maximal quantifier subterms are ENTAILED
//!   universals gets no proxy: when it is itself the universal it is left
//!   alone, the pre-existing path; otherwise each universal is replaced by
//!   `true` afterwards, which keeps the assertion's ground content
//!   (`keep_ground_content_of_entailed`);
//! * an assertion whose rewrite does not survive the REVERSE substitution
//!   (`proxy -> quantifier`, checked for `TermId` identity against the original)
//!   is reverted. The abstraction map is the one new single point of
//!   unsoundness for every UNSAT this stage enables, so the differential is
//!   checked on every production rewrite rather than only under `debug_assert`.
//!
//! Every refusal path leaves the assertion exactly as `flatten_and_strip_
//! quantifiers` found it, so the caller's unchanged `retain` deletes it and the
//! solve is byte-identical to baseline for that assertion.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::{TermData, TermId, TermStore};
use ay_core::Sort;

/// What `purify_quantifier_atoms` did, for the caller's state and statistics.
#[derive(Default)]
pub(in crate::executor) struct QuantifierAbstraction {
    /// `quantifier TermId -> fresh Bool proxy TermId`, for every quantifier
    /// occurrence this pass actually rewrote.
    pub(in crate::executor) proxies: DetHashMap<TermId, TermId>,
    /// Number of assertions rewritten in place.
    pub(in crate::executor) rewritten_assertions: usize,
    /// Assertions that met the target predicate but were refused
    /// (`Let`, an unrecognised node, or a failed reverse differential).
    pub(in crate::executor) refused_assertions: usize,
}

impl QuantifierAbstraction {
    /// True when at least one assertion was actually rewritten, i.e. when the
    /// ground problem the solver sees is an over-approximation of the authored
    /// one and no `sat` may be published for it.
    pub(in crate::executor) fn is_active(&self) -> bool {
        self.rewritten_assertions > 0
    }
}

/// Collect the MAXIMAL quantifier subterms of `root` — the `Forall`/`Exists`
/// nodes not contained in another quantifier node reachable from `root`.
///
/// Returns `false` to REFUSE the whole assertion (a `Let`, or a `TermData`
/// variant this walk does not model). On refusal `out` is left in an
/// unspecified state and the caller must discard it.
fn collect_maximal_quantifiers(
    terms: &TermStore,
    root: TermId,
    seen: &mut DetHashSet<TermId>,
    out: &mut Vec<TermId>,
) -> bool {
    if !seen.insert(root) {
        return true;
    }
    match terms.get(root) {
        TermData::Const(_) | TermData::Var(_, _) => true,
        // A quantifier node is maximal by construction: the walk stops here and
        // never inspects the body, so no nested quantifier can be collected.
        TermData::Forall(..) | TermData::Exists(..) => {
            out.push(root);
            true
        }
        TermData::App(_, args) => {
            let args = args.clone();
            args.iter()
                .all(|&arg| collect_maximal_quantifiers(terms, arg, seen, out))
        }
        TermData::Not(inner) => {
            let inner = *inner;
            collect_maximal_quantifiers(terms, inner, seen, out)
        }
        TermData::Ite(cond, then_branch, else_branch) => {
            let (cond, then_branch, else_branch) = (*cond, *then_branch, *else_branch);
            collect_maximal_quantifiers(terms, cond, seen, out)
                && collect_maximal_quantifiers(terms, then_branch, seen, out)
                && collect_maximal_quantifiers(terms, else_branch, seen, out)
        }
        // Fail-closed: `Let` introduces a binder this walk does not model, and
        // `TermData` is `#[non_exhaustive]` so an unknown variant may carry
        // sub-terms that would be silently dropped from the rewrite.
        _ => false,
    }
}

/// The maximal quantifier subterms of `root`, each once, in `TermId` order;
/// `None` on the collector's fail-closed refusals.
pub(in crate::executor) fn maximal_quantifiers_of(
    terms: &TermStore,
    root: TermId,
) -> Option<Vec<TermId>> {
    let mut seen = DetHashSet::default();
    let mut maximal = Vec::new();
    if !collect_maximal_quantifiers(terms, root, &mut seen, &mut maximal) {
        return None;
    }
    maximal.sort_unstable_by_key(|term| term.index());
    maximal.dedup();
    Some(maximal)
}

/// `root` with every maximal quantifier that is a key of `map` replaced by its
/// image, rebuilt with the non-folding constructors; `None` on the
/// collector's refusals. No binder body is entered.
pub(in crate::executor) fn replace_quantifiers(
    terms: &mut TermStore,
    root: TermId,
    map: &DetHashMap<TermId, TermId>,
) -> Option<TermId> {
    let mut cache = DetHashMap::default();
    substitute_top_down(terms, root, map, &mut cache)
}

/// Apply `map` top-down to `root`, rebuilding every node on the path with the
/// NON-folding constructors so the result is structurally exact.
///
/// Returns `None` on the same fail-closed refusals as the collector.
fn substitute_top_down(
    terms: &mut TermStore,
    root: TermId,
    map: &DetHashMap<TermId, TermId>,
    cache: &mut DetHashMap<TermId, TermId>,
) -> Option<TermId> {
    // MAP FIRST. This is what makes the walk capture-safe: every key is a
    // quantifier node (forward) or a fresh Bool proxy (reverse), so a hit ends
    // the descent and no binder body is ever entered.
    if let Some(&replacement) = map.get(&root) {
        return Some(replacement);
    }
    if let Some(&cached) = cache.get(&root) {
        return Some(cached);
    }
    let rewritten = match terms.get(root).clone() {
        TermData::Const(_) | TermData::Var(_, _) => root,
        // Not a map key, so it is an untargeted quantifier: keep it verbatim
        // and do NOT descend (its body may mention bound variables).
        TermData::Forall(..) | TermData::Exists(..) => root,
        TermData::App(symbol, args) => {
            let mut changed = false;
            let mut new_args = Vec::with_capacity(args.len());
            for &arg in &args {
                let new_arg = substitute_top_down(terms, arg, map, cache)?;
                changed |= new_arg != arg;
                new_args.push(new_arg);
            }
            if changed {
                let sort = terms.sort(root).clone();
                terms.mk_app(symbol, new_args, sort)
            } else {
                root
            }
        }
        TermData::Not(inner) => {
            let new_inner = substitute_top_down(terms, inner, map, cache)?;
            if new_inner == inner {
                root
            } else {
                // RAW: the folding `mk_not` would collapse `(not (not p))`,
                // which the reverse differential could not then reproduce.
                terms.mk_not_raw(new_inner)
            }
        }
        TermData::Ite(cond, then_branch, else_branch) => {
            let new_cond = substitute_top_down(terms, cond, map, cache)?;
            let new_then = substitute_top_down(terms, then_branch, map, cache)?;
            let new_else = substitute_top_down(terms, else_branch, map, cache)?;
            if new_cond == cond && new_then == then_branch && new_else == else_branch {
                root
            } else {
                // RAW for the same reason as `mk_not_raw` above.
                terms.mk_ite_raw(new_cond, new_then, new_else)
            }
        }
        _ => return None,
    };
    cache.insert(root, rewritten);
    Some(rewritten)
}

/// Replace every quantifier of an assertion by `true` when all of its maximal
/// quantifiers are in `entailed_foralls` and the assertion is not itself one
/// of them (#entailed-to-true). `protected` assertions (CEGQI counterexample
/// lemmas, keyed by `TermId`) are left alone, as in
/// [`purify_quantifier_atoms`], which runs first and leaves exactly these
/// assertions quantified.
///
/// Such an assertion used to be left for the caller's `retain`, which deletes
/// it whole. That was harmless while its only content was the universal
/// (`(=> g Q)` with `g` a fact), but it also throws away ground content:
/// Verus's extensional-equality axioms give instances shaped
/// `(or (and (= (len s) (len t)) Q) (not (ext_eq s t)))`, where `Q` is entailed
/// once `(ext_eq s t)` is a fact, and deleting the instance loses
/// `(= (len s) (len t))`, which is the whole refutation.
///
/// Sound for UNSAT: every model of the assertion set makes each such `Q` true,
/// hence satisfies the assertion with `Q` replaced by `true`, so a refutation
/// of the rewritten set refutes the authored one. The rewritten set may admit
/// more models (the assertion that entailed `Q` may be the one rewritten), but
/// strictly fewer than deleting the assertion did, and every `sat` still faces
/// the same downstream quantifier checks, so nothing becomes publishable that
/// deletion left unpublishable. No symbol is introduced. The universal itself
/// is instantiated by the entailed lane as before.
///
/// Returns the number of assertions rewritten.
pub(in crate::executor) fn keep_ground_content_of_entailed(
    terms: &mut TermStore,
    assertions: &mut [TermId],
    entailed_foralls: &DetHashSet<TermId>,
    protected: &DetHashSet<TermId>,
) -> usize {
    let truth = terms.mk_bool(true);
    let mut rewritten_count = 0;
    for index in 0..assertions.len() {
        let original = assertions[index];
        if protected.contains(&original) || !crate::ematching::contains_quantifier(terms, original)
        {
            continue;
        }
        let mut seen = DetHashSet::default();
        let mut maximal = Vec::new();
        if !collect_maximal_quantifiers(terms, original, &mut seen, &mut maximal)
            || maximal.is_empty()
            || maximal == [original]
            || !maximal.iter().all(|q| entailed_foralls.contains(q))
        {
            continue;
        }
        let map: DetHashMap<TermId, TermId> = maximal.iter().map(|&q| (q, truth)).collect();
        let mut cache: DetHashMap<TermId, TermId> = DetHashMap::default();
        if let Some(rewritten) = substitute_top_down(terms, original, &map, &mut cache) {
            assertions[index] = rewritten;
            rewritten_count += 1;
        }
    }
    rewritten_count
}

/// Replace the targeted quantifier occurrences in `assertions` by fresh Boolean
/// proxies, in place.
///
/// `entailed_foralls` is the set already computed by `setup_cegqi_for_unhandled`
/// — READ, never recomputed: `entailed_forall_set` takes `&mut TermStore` and
/// mints NNF-dual terms, so recomputing it would shift every later `TermId`.
///
/// `protected` names assertions that must keep their exact `TermId` because
/// other bookkeeping keys on it (the CEGQI counterexample lemmas, whose ids
/// `disambiguate_cegqi_unsat` strips by identity).
pub(in crate::executor) fn purify_quantifier_atoms(
    terms: &mut TermStore,
    assertions: &mut [TermId],
    entailed_foralls: &DetHashSet<TermId>,
    protected: &DetHashSet<TermId>,
) -> QuantifierAbstraction {
    let mut outcome = QuantifierAbstraction::default();

    // 1. Target selection. An assertion is a target when it mentions a
    //    quantifier the assertion set does NOT entail — i.e. exactly the
    //    assertions whose deletion loses ground content the solver could use.
    let mut targets: Vec<(usize, Vec<TermId>)> = Vec::new();
    let mut all_quantifiers: Vec<TermId> = Vec::new();
    for (index, &assertion) in assertions.iter().enumerate() {
        if !crate::ematching::contains_quantifier(terms, assertion) {
            continue;
        }
        if protected.contains(&assertion) {
            continue;
        }
        let mut seen = DetHashSet::default();
        let mut maximal = Vec::new();
        if !collect_maximal_quantifiers(terms, assertion, &mut seen, &mut maximal) {
            outcome.refused_assertions += 1;
            continue;
        }
        if maximal.is_empty() {
            // `contains_quantifier` said yes but no maximal node was reached:
            // defensive, and fail-closed either way.
            continue;
        }
        maximal.sort_unstable_by_key(|term| term.index());
        maximal.dedup();
        // Every maximal universal is entailed: the pre-existing lane already
        // instantiates it soundly as a unit fact and the assertion carries no
        // ground content the ground solver is missing. Leave it byte-identical.
        if maximal
            .iter()
            .all(|quantifier| entailed_foralls.contains(quantifier))
        {
            continue;
        }
        all_quantifiers.extend(maximal.iter().copied());
        targets.push((index, maximal));
    }
    if targets.is_empty() {
        return outcome;
    }

    // 2. Mint one proxy per hash-consed quantifier `TermId`, in deterministic
    //    `TermId` order so two runs of the same query allocate identically.
    all_quantifiers.sort_unstable_by_key(|term| term.index());
    all_quantifiers.dedup();
    let mut map: DetHashMap<TermId, TermId> = DetHashMap::default();
    let mut reverse: DetHashMap<TermId, TermId> = DetHashMap::default();
    for quantifier in all_quantifiers {
        let proxy = terms.mk_fresh_var("qproxy", Sort::Bool);
        map.insert(quantifier, proxy);
        reverse.insert(proxy, quantifier);
    }

    // 3. Rewrite, and check the reverse differential on every assertion before
    //    committing it. A shared forward cache is safe (it is keyed by the
    //    original `TermId` under one fixed map); the reverse check gets a fresh
    //    cache per assertion so a bad entry cannot mask a later failure.
    let mut forward_cache: DetHashMap<TermId, TermId> = DetHashMap::default();
    for (index, quantifiers) in &targets {
        let original = assertions[*index];
        let Some(rewritten) = substitute_top_down(terms, original, &map, &mut forward_cache) else {
            outcome.refused_assertions += 1;
            continue;
        };
        let mut reverse_cache: DetHashMap<TermId, TermId> = DetHashMap::default();
        let restored = substitute_top_down(terms, rewritten, &reverse, &mut reverse_cache);
        debug_assert_eq!(
            restored,
            Some(original),
            "BUG (#quantifier-proxy-abstraction): reverse substitution of the \
             quantifier abstraction did not reproduce the authored assertion"
        );
        if restored != Some(original) {
            outcome.refused_assertions += 1;
            continue;
        }
        if rewritten == original {
            // Nothing was replaced after all; leave the baseline path in charge.
            continue;
        }
        assertions[*index] = rewritten;
        outcome.rewritten_assertions += 1;
        for quantifier in quantifiers {
            if let Some(&proxy) = map.get(quantifier) {
                outcome.proxies.insert(*quantifier, proxy);
            }
        }
    }
    outcome
}

#[cfg(test)]
mod tests;
