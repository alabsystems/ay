// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rewriter-level quantifier eliminations: destructive equality resolution
//! (DER), z3-style `qe-lite` arithmetic variable solving, and unused-variable
//! elimination.
//!
//! All three are applied bottom-up to EVERY quantifier node (not only top-level
//! assertions), matching where z3 runs them (`der` inside `th_rewriter`,
//! `elim_unused_vars` in `var_subst.cpp`, `qe_lite` in `qe/lite/qe_lite.cpp`).
//! Each is an EQUIVALENCE over the same signature:
//!
//! * DER, `∀`: `∀v x̄. (v ≠ r ∨ C) ≡ ∀x̄. C[v := r]` when `v` does not occur in
//!   `r` (the clause can only fail at `v = r`). Dually for `∃`:
//!   `∃v x̄. (v = r ∧ C) ≡ ∃x̄. C[v := r]`. An empty `∀` residual is `false`;
//!   an empty `∃` residual is `true` (sorts are non-empty).
//! * qe-lite: the same one-point rule after SOLVING an arithmetic literal for
//!   `v`: `a ≠ b` with `a − b = c·v + R`, `v ∉ R`, gives `v = −R/c`. Over `Int`
//!   only `c = ±1` is solved (the solution must be an integer term); over
//!   `Real` any `c ≠ 0`.
//! * elim-unused-vars: `∀x̄ y. C ≡ ∀x̄. C` when `y` is not free in `C`.
//!
//! Substitution goes through [`crate::ematching::subst_vars`], the capture-
//! avoiding substitution E-matching instantiates with; after every elimination
//! the eliminated names are checked to be absent from the rebuilt body, so a
//! substitution that silently declined can only make the rule decline.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

use super::fold::{rebuild_app, refold};
use super::linear_solve::ArithSolver;
use super::terms::{
    as_binary_diseq, as_binary_eq, as_quantifier, body_literals, free_names, is_var_named,
    mentions_any_name, rebuild_quantifier, triggers_without, Binder, Quantifier,
};
use super::WorkBudget;

/// Maximum number of consecutive rule applications at one quantifier node.
const MAX_RULE_STEPS_PER_NODE: usize = 8;

/// A simplification of one quantifier node whose body is already simplified.
pub(super) trait QuantifierRule {
    /// Return the simplified node, or `None` when the rule does not apply (or
    /// declines on the budget).
    fn try_simplify(
        &mut self,
        terms: &mut TermStore,
        node: TermId,
        q: &Quantifier,
        budget: &mut WorkBudget<'_>,
    ) -> Option<TermId>;
}

/// Rewrite every window assertion that contains a quantifier bottom-up with
/// `rule`. An assertion whose walk runs out of budget is kept unchanged.
/// Returns the number of rule applications committed.
pub(super) fn rewrite_window(
    terms: &mut TermStore,
    window: &mut [TermId],
    rule: &mut dyn QuantifierRule,
    budget: &mut WorkBudget<'_>,
) -> usize {
    let mut cache: HashMap<TermId, TermId> = HashMap::default();
    let mut applied_total = 0;
    for slot in window.iter_mut() {
        if !crate::ematching::contains_quantifier(terms, *slot) {
            continue;
        }
        let mut applied = 0;
        match rewrite(terms, *slot, rule, &mut cache, budget, &mut applied) {
            Some(new) => {
                if new != *slot {
                    *slot = new;
                    applied_total += applied;
                }
            }
            None => break,
        }
    }
    applied_total
}

fn rewrite(
    terms: &mut TermStore,
    t: TermId,
    rule: &mut dyn QuantifierRule,
    cache: &mut HashMap<TermId, TermId>,
    budget: &mut WorkBudget<'_>,
    applied: &mut usize,
) -> Option<TermId> {
    if let Some(&done) = cache.get(&t) {
        return Some(done);
    }
    if !budget.tick() {
        return None;
    }
    let result = stacker::maybe_grow(32 * 1024, 1024 * 1024, || -> Option<TermId> {
        Some(match terms.get(t).clone() {
            TermData::Const(_) | TermData::Var(_, _) | TermData::Let(_, _) => t,
            TermData::Not(inner) => {
                let ni = rewrite(terms, inner, rule, cache, budget, applied)?;
                if ni == inner {
                    t
                } else {
                    terms.mk_not(ni)
                }
            }
            TermData::Ite(c, a, b) => {
                let nc = rewrite(terms, c, rule, cache, budget, applied)?;
                let na = rewrite(terms, a, rule, cache, budget, applied)?;
                let nb = rewrite(terms, b, rule, cache, budget, applied)?;
                if (nc, na, nb) == (c, a, b) {
                    t
                } else {
                    terms.mk_ite(nc, na, nb)
                }
            }
            TermData::App(sym, args) => {
                let mut new_args = Vec::with_capacity(args.len());
                for &arg in &args {
                    new_args.push(rewrite(terms, arg, rule, cache, budget, applied)?);
                }
                if new_args == args {
                    t
                } else {
                    rebuild_app(terms, &sym, new_args, t)
                }
            }
            TermData::Forall(..) | TermData::Exists(..) => {
                let q = as_quantifier(terms, t)?;
                let nb = rewrite(terms, q.body, rule, cache, budget, applied)?;
                let mut node = if nb == q.body {
                    t
                } else {
                    rebuild_quantifier(terms, t, q.binder, q.vars.clone(), nb, q.triggers.clone())
                };
                for _ in 0..MAX_RULE_STEPS_PER_NODE {
                    let Some(current) = as_quantifier(terms, node) else {
                        break;
                    };
                    match rule.try_simplify(terms, node, &current, budget) {
                        Some(next) if next != node => {
                            *applied += 1;
                            node = next;
                        }
                        _ => break,
                    }
                }
                node
            }
            _ => t,
        })
    })?;
    cache.insert(t, result);
    Some(result)
}

/// How a rule solves one literal for one bound variable.
pub(super) trait LiteralSolver {
    /// For a literal of the quantifier's clause view (`∀`: a disjunct, `∃`: a
    /// conjunct), return `r` such that the literal is `v ≠ r` (`∀`) or `v = r`
    /// (`∃`) up to equivalence, with `v` not occurring in `r`.
    fn solve(
        &mut self,
        terms: &mut TermStore,
        lit: TermId,
        var: &str,
        sort: &Sort,
        binder: Binder,
    ) -> Option<TermId>;
}

/// The shared one-point elimination engine behind DER and qe-lite.
fn one_point_eliminate(
    terms: &mut TermStore,
    node: TermId,
    q: &Quantifier,
    solver: &mut dyn LiteralSolver,
    budget: &mut WorkBudget<'_>,
) -> Option<TermId> {
    // A binder list that repeats a name is ill-formed for name-based scoping.
    let mut names: HashSet<&str> = HashSet::default();
    if !q.vars.iter().all(|(n, _)| names.insert(n.as_str())) {
        return None;
    }
    let mut lits = body_literals(terms, q.body, q.binder);
    let mut vars = q.vars.clone();
    let mut eliminated: HashSet<String> = HashSet::default();
    let mut fold_cache: HashMap<TermId, TermId> = HashMap::default();
    loop {
        if !budget.tick() {
            return None;
        }
        let mut found: Option<(usize, usize, TermId)> = None;
        'search: for (vi, (vname, vsort)) in vars.iter().enumerate() {
            for (li, &lit) in lits.iter().enumerate() {
                if let Some(r) = solver.solve(terms, lit, vname, vsort, q.binder) {
                    let mut single = HashSet::default();
                    single.insert(vname.clone());
                    if terms.sort(r) == vsort && !mentions_any_name(terms, r, &single) {
                        found = Some((vi, li, r));
                        break 'search;
                    }
                }
            }
        }
        let Some((vi, li, r)) = found else {
            break;
        };
        let (vname, _) = vars.remove(vi);
        let _resolved = lits.remove(li);
        let mut subst: HashMap<String, TermId> = HashMap::default();
        subst.insert(vname.clone(), r);
        for lit in &mut lits {
            let substituted = crate::ematching::subst_vars(terms, *lit, &subst);
            // Fold now, so a constant solution decides guards (`ite`,
            // comparisons) before the next variable is searched for.
            *lit = refold(terms, substituted, &mut fold_cache, budget)?;
        }
        eliminated.insert(vname);
        // A literal that folded to a constant settles the clause (`true`) or
        // drops out of it (`false`); the same holds dually for `∃`.
        let (absorbing, neutral) = match q.binder {
            Binder::Forall => (terms.true_term(), terms.false_term()),
            Binder::Exists => (terms.false_term(), terms.true_term()),
        };
        if lits.contains(&absorbing) {
            lits = vec![absorbing];
            vars.clear();
            break;
        }
        lits.retain(|&lit| lit != neutral);
    }
    if eliminated.is_empty() {
        return None;
    }
    let body = match q.binder {
        Binder::Forall => terms.mk_or(lits),
        Binder::Exists => terms.mk_and(lits),
    };
    let body = refold(terms, body, &mut fold_cache, budget)?;
    // Contract check: every eliminated variable is gone from the body.
    let free = free_names(terms, body)?;
    if eliminated.iter().any(|name| free.contains(name)) {
        return None;
    }
    let triggers = triggers_without(terms, &q.triggers, &eliminated);
    Some(rebuild_quantifier(
        terms, node, q.binder, vars, body, triggers,
    ))
}

/// Destructive equality resolution: the literal is literally `v ≠ r` / `v = r`.
pub(super) struct DerRule;

struct SyntacticSolver;

impl LiteralSolver for SyntacticSolver {
    fn solve(
        &mut self,
        terms: &mut TermStore,
        lit: TermId,
        var: &str,
        _sort: &Sort,
        binder: Binder,
    ) -> Option<TermId> {
        let (a, b) = match binder {
            Binder::Forall => as_binary_diseq(terms, lit)?,
            Binder::Exists => as_binary_eq(terms, lit)?,
        };
        if is_var_named(terms, a, var) && !is_var_named(terms, b, var) {
            Some(b)
        } else if is_var_named(terms, b, var) && !is_var_named(terms, a, var) {
            Some(a)
        } else {
            None
        }
    }
}

impl QuantifierRule for DerRule {
    fn try_simplify(
        &mut self,
        terms: &mut TermStore,
        node: TermId,
        q: &Quantifier,
        budget: &mut WorkBudget<'_>,
    ) -> Option<TermId> {
        one_point_eliminate(terms, node, q, &mut SyntacticSolver, budget)
    }
}

/// z3-style qe-lite: solve a linear arithmetic literal for the variable.
pub(super) struct QeLiteRule;

impl QuantifierRule for QeLiteRule {
    fn try_simplify(
        &mut self,
        terms: &mut TermStore,
        node: TermId,
        q: &Quantifier,
        budget: &mut WorkBudget<'_>,
    ) -> Option<TermId> {
        one_point_eliminate(terms, node, q, &mut ArithSolver, budget)
    }
}

/// Drop bound variables that do not occur free in the body.
pub(super) struct ElimUnusedVarsRule;

impl QuantifierRule for ElimUnusedVarsRule {
    fn try_simplify(
        &mut self,
        terms: &mut TermStore,
        node: TermId,
        q: &Quantifier,
        _budget: &mut WorkBudget<'_>,
    ) -> Option<TermId> {
        let free = free_names(terms, q.body)?;
        let (kept, dropped): (Vec<_>, Vec<_>) =
            q.vars.iter().cloned().partition(|(n, _)| free.contains(n));
        if dropped.is_empty() {
            return None;
        }
        // A repeated binder name makes "unused" ambiguous; decline.
        let mut seen: HashSet<&str> = HashSet::default();
        if !q.vars.iter().all(|(n, _)| seen.insert(n.as_str())) {
            return None;
        }
        let eliminated: HashSet<String> = dropped.into_iter().map(|(n, _)| n).collect();
        let triggers = triggers_without(terms, &q.triggers, &eliminated);
        Some(rebuild_quantifier(
            terms, node, q.binder, kept, q.body, triggers,
        ))
    }
}
