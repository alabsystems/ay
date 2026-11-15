// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Skolem-witness guarded instantiation of proxied quantifiers
//! (#skolem-guarded-proxy-instances).
//!
//! # The gap
//!
//! `purify_quantifier_atoms` replaces a quantifier the assertion set does not
//! entail by a fresh Boolean proxy, so the ground solver keeps the surrounding
//! ground disjuncts instead of losing the whole assertion. But the proxy is a
//! FREE Boolean: nothing relates `q` to the quantifier it abstracts, so the
//! ground solver simply guesses it and reports `Sat` over an
//! over-approximation, which the fail-closed head arm of
//! `classify_quantifier_result` turns into `unknown`.
//!
//! Measured on the LIA UltimateAutomizer family (2026-09-07, build 9544), which
//! is the whole of the `LIA` division's parity gap in the campaign's seeded
//! sample. Every file has the shape
//!
//! ```smt2
//! (assert (and G1 .. Gn (exists (x⃗) phi)))          ; the ASSUMED state
//! (assert (not (and G1 .. Gk (exists (y⃗) psi))))    ; the GOAL, negated
//! ```
//!
//! The positive existential is Skolemized to `phi[sk⃗]`, so its witness is a
//! GROUND constant of the problem. The negated one sits in a disjunctive
//! position, is therefore not in `entailed_forall_set`, is proxied, and is
//! never instantiated by any lane: `:ematching-instances-created 0`,
//! `:quantifier.cegqi.ce_lemmas 0`, `:quantifier.mbqi.rounds 0`, and
//! `CERT/qproxy: ground Sat over an abstracted problem -> Unknown`.
//!
//! z3 5.1.0 decides all of them in under 0.01 s. Forced onto its SMT core
//! (`tactic.default_tactic=smt`, i.e. no QSAT/MBP), it still decides them —
//! with **two** `:quant-instantiations`. So the missing mechanism is
//! instantiation, and the instantiating term the problem itself supplies is
//! exactly the Skolem witness of the sibling existential.
//!
//! # What this pass adds
//!
//! For each proxied quantifier `Q` with proxy `q`, and each ground tuple `t⃗`
//! drawn from THIS solve's Skolem constants at the binder sorts, one guarded
//! clause:
//!
//! ```text
//! Q = (exists (x⃗) phi)   ->   (or (not phi[t⃗]) q)
//! Q = (forall (x⃗) phi)   ->   (or (not q) phi[t⃗])
//! ```
//!
//! No instance is ever conjoined unconditionally: the proxy literal guards
//! every one of them, which is what makes this sound for a quantifier in a
//! DISJUNCTIVE position — the shape whose unconditional instantiation is the
//! `#auflia-disjunct-forall-false-unsat` wrong-`unsat`.
//!
//! # Soundness
//!
//! Let `A'` be the assertion set at the moment `purify_quantifier_atoms` runs
//! (post-Skolemization, pre-abstraction) and `sigma` the proxy substitution.
//! Each targeted `Q_i` is a MAXIMAL quantifier subterm of an assertion that
//! contains no `Let` (purify refuses those), hence a CLOSED Boolean term, so
//! `⟦Q_i⟧_M` is defined for any `M ⊨ A'`. Extend `M` to `M'` by
//! `q_i := ⟦Q_i⟧_M` — this is purify's own argument, unchanged.
//!
//! Each clause this pass adds holds in that same `M'`:
//!
//! * `Q = ∃x⃗.phi`: `t⃗` is ground and `phi[t⃗]` mentions no proxy (the
//!   substitution is into the ORIGINAL body), so `M' ⊨ phi[t⃗]` iff
//!   `M ⊨ phi[t⃗]`, which implies `M ⊨ ∃x⃗.phi`, i.e. `M'(q) = true`. Hence
//!   `M' ⊨ (or (not phi[t⃗]) q)`.
//! * `Q = ∀x⃗.phi`: if `M'(q) = true` then `⟦Q⟧_M = true`, so `M ⊨ phi[t⃗]` for
//!   the ground `t⃗`, so `M' ⊨ phi[t⃗]`. Hence `M' ⊨ (or (not q) phi[t⃗])`.
//!
//! So `SAT(A') ⟹ SAT(sigma(A') ∪ guards)`, i.e. a refutation of the guarded
//! abstract problem refutes `A'`, and Skolemization is equisatisfiable with the
//! authored set. The converse still fails — the guards constrain the proxies
//! but do not define them — so `quantifier_abstraction_active` continues to
//! forbid every `sat` publication, exactly as before. **This pass can only turn
//! an `unknown` into an `unsat`; it can publish no `sat` that the abstraction
//! did not already forbid.**
//!
//! # Fail-closed refusals (each leaves the assertion vector untouched)
//!
//! * a body containing a nested quantifier or a `Let` — the substitution's
//!   capture reasoning is only trivial for a quantifier- and let-free body, and
//!   a clause that still carried a quantifier would be deleted by
//!   `flatten_and_strip_quantifiers`'s `retain` anyway;
//! * more than [`MAX_BINDERS`] binders, or no binder at all;
//! * a binder sort with no Skolem constant;
//! * the per-quantifier and global tuple budgets.
//!
//! Skolem FUNCTION applications (`sk_x(y)`, minted when the existential is
//! under a universal) are deliberately excluded: they are not ground.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::{TermData, TermId, TermStore};
use ay_core::Sort;

use crate::ematching::subst_vars;

/// Binder count beyond which a proxied quantifier is skipped. The tuple
/// enumeration is a cross product, so this is the exponent.
const MAX_BINDERS: usize = 3;
/// Skolem constants offered per binder sort, in `TermId` order.
const MAX_CANDIDATES_PER_BINDER: usize = 4;
/// Guarded clauses one proxied quantifier may contribute.
const MAX_TUPLES_PER_QUANTIFIER: usize = 8;
/// Guarded clauses this pass may add to one `check-sat`.
const MAX_TOTAL_CLAUSES: usize = 24;
/// Node budget for the body scan that rejects nested binders.
const MAX_SCAN_NODES: usize = 20_000;

/// What the pass did, for the caller's statistics.
#[derive(Default, Debug, PartialEq, Eq)]
pub(in crate::executor) struct GuardedInstanceOutcome {
    /// Guarded clauses built (before duplicate filtering).
    pub(in crate::executor) created: usize,
    /// Guarded clauses actually appended to the assertion vector.
    pub(in crate::executor) asserted: usize,
}

/// Ground Skolem CONSTANTS reachable from `assertions`, grouped by sort and
/// ordered by `TermId` so two runs of the same query agree.
fn skolem_constants_by_sort(
    terms: &TermStore,
    assertions: &[TermId],
) -> DetHashMap<Sort, Vec<TermId>> {
    let mut seen: DetHashSet<TermId> = DetHashSet::default();
    let mut found: Vec<TermId> = Vec::new();
    let mut stack: Vec<TermId> = assertions.to_vec();
    let mut work = 0usize;
    while let Some(term) = stack.pop() {
        work += 1;
        if work > MAX_SCAN_NODES {
            break;
        }
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Var(name, _) => {
                if terms.is_skolem_symbol(name) {
                    found.push(term);
                }
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(cond, then_branch, else_branch) => {
                stack.push(*cond);
                stack.push(*then_branch);
                stack.push(*else_branch);
            }
            // A quantifier body may hold a Skolem constant minted for a
            // sibling; descending is safe because only the CONSTANT is
            // collected, never a bound variable.
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    stack.push(*value);
                }
                stack.push(*body);
            }
            _ => {}
        }
    }
    found.sort_unstable_by_key(|term| term.index());
    found.dedup();
    let mut by_sort: DetHashMap<Sort, Vec<TermId>> = DetHashMap::default();
    for term in found {
        let sort = terms.sort(term).clone();
        let slot = by_sort.entry(sort).or_default();
        if slot.len() < MAX_CANDIDATES_PER_BINDER {
            slot.push(term);
        }
    }
    by_sort
}

/// `true` when `term` carries a binder (`forall`/`exists`/`let`) anywhere, or
/// the scan budget ran out. Conservative in the refusing direction.
fn has_binder_or_overruns(terms: &TermStore, term: TermId) -> bool {
    let mut seen: DetHashSet<TermId> = DetHashSet::default();
    let mut stack = vec![term];
    let mut work = 0usize;
    while let Some(current) = stack.pop() {
        work += 1;
        if work > MAX_SCAN_NODES {
            return true;
        }
        if !seen.insert(current) {
            continue;
        }
        match terms.get(current) {
            TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => return true,
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(cond, then_branch, else_branch) => {
                stack.push(*cond);
                stack.push(*then_branch);
                stack.push(*else_branch);
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            // `TermData` is `#[non_exhaustive]`: an unmodelled node refuses.
            _ => return true,
        }
    }
    false
}

/// Append one guarded clause per (proxied quantifier, Skolem tuple).
///
/// `assertions` is the live vector `flatten_and_strip_quantifiers` is about to
/// `retain` over; every clause added here is quantifier-free by construction
/// and therefore survives it.
pub(in crate::executor) fn assert_skolem_guarded_instances(
    terms: &mut TermStore,
    assertions: &mut Vec<TermId>,
    proxies: &DetHashMap<TermId, TermId>,
) -> GuardedInstanceOutcome {
    let mut outcome = GuardedInstanceOutcome::default();
    if proxies.is_empty() {
        return outcome;
    }
    let by_sort = skolem_constants_by_sort(terms, assertions);
    if by_sort.is_empty() {
        return outcome;
    }

    // Deterministic quantifier order: the clause set must not depend on hash
    // iteration order, or two runs of the same query differ.
    let mut targets: Vec<(TermId, TermId)> = proxies.iter().map(|(&q, &p)| (q, p)).collect();
    targets.sort_unstable_by_key(|(quantifier, _)| quantifier.index());

    let existing: DetHashSet<TermId> = assertions.iter().copied().collect();
    let mut added: DetHashSet<TermId> = DetHashSet::default();

    for (quantifier, proxy) in targets {
        if outcome.asserted >= MAX_TOTAL_CLAUSES {
            break;
        }
        let (vars, body, is_exists) = match terms.get(quantifier) {
            TermData::Exists(vars, body, _) => (vars.clone(), *body, true),
            TermData::Forall(vars, body, _) => (vars.clone(), *body, false),
            _ => continue,
        };
        if vars.is_empty() || vars.len() > MAX_BINDERS {
            continue;
        }
        if has_binder_or_overruns(terms, body) {
            continue;
        }
        let mut candidates_per_var: Vec<&Vec<TermId>> = Vec::with_capacity(vars.len());
        let mut tuples: usize = 1;
        let mut refused = false;
        for (_, sort) in &vars {
            match by_sort.get(sort) {
                Some(candidates) if !candidates.is_empty() => {
                    tuples = tuples.saturating_mul(candidates.len());
                    candidates_per_var.push(candidates);
                }
                _ => {
                    refused = true;
                    break;
                }
            }
        }
        if refused || tuples > MAX_TUPLES_PER_QUANTIFIER {
            continue;
        }

        let names: Vec<String> = vars.iter().map(|(name, _)| name.clone()).collect();
        // `tuples` is the cross-product size and is bounded by
        // `MAX_TUPLES_PER_QUANTIFIER`, so decode each index directly rather
        // than carrying an odometer.
        for tuple_index in 0..tuples {
            if outcome.asserted >= MAX_TOTAL_CLAUSES {
                break;
            }
            let mut rest = tuple_index;
            let mut binding: DetHashMap<String, TermId> = DetHashMap::default();
            for slot in (0..names.len()).rev() {
                let width = candidates_per_var[slot].len();
                binding.insert(names[slot].clone(), candidates_per_var[slot][rest % width]);
                rest /= width;
            }
            let instance = subst_vars(terms, body, &binding);
            outcome.created += 1;
            let clause = if is_exists {
                let negated = terms.mk_not(instance);
                terms.mk_or(vec![negated, proxy])
            } else {
                let guard = terms.mk_not(proxy);
                terms.mk_or(vec![guard, instance])
            };
            // A clause that folded to a constant, or that the assertion set
            // already carries, adds nothing.
            if !matches!(terms.get(clause), TermData::Const(_))
                && !existing.contains(&clause)
                && added.insert(clause)
            {
                assertions.push(clause);
                outcome.asserted += 1;
            }
        }
    }
    outcome
}

#[cfg(test)]
mod tests;
