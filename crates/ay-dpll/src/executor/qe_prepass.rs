// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deep quantifier-elimination pre-pass for the check-sat path.
//!
//! Runs immediately after `simplify_vacuous_quantifiers()` (before the
//! closed-universal precheck and `process_quantifiers()`), gated on the
//! presence of quantified assertions. Where the `qe-light` tactic pass
//! ([`crate::preprocess::qe_light`]) only replaces top-fragment
//! single-variable existentials, this pass descends INTO binders and layers
//! four logical identities over the same soundness-gated elimination engines:
//!
//! 1. **Binder currying** — `∃y,z.φ ≡ ∃y.(∃z.φ)`: bound variables are peeled
//!    one at a time, last-to-first (dually for `∀`).
//! 2. **∀-duality** — `∀v.ψ ≡ ¬∃v.¬ψ`, applied per variable innermost-out.
//! 3. **NNF** — negations are pushed through `and`/`or`/`not` only, leaving
//!    `Not(atom)` literals intact (Cooper's `parse_negated` handles those
//!    natively). Bool-sorted `=`/`xor`/`ite` are NOT pushed through; they stay
//!    opaque atoms for the eliminators to refuse.
//! 4. **∃-over-∨ distribution** — `∃v.(A ∨ B) ≡ (∃v.A) ∨ (∃v.B)`: the matrix
//!    is distributed into DNF-lite under hard caps, each disjunct is
//!    eliminated independently, and the results are OR-ed back together.
//!
//! Per-variable elimination dispatches on the bound variable's sort:
//! [`Sort::Int`] goes to Cooper ([`crate::qe::eliminate_exists`]) and
//! [`Sort::Real`] to Loos-Weispfenning virtual substitution
//! ([`crate::qe::eliminate_exists_real`]); anything else is refused. Both
//! engines only return `Eliminated` after their independent per-elimination
//! equivalence self-check passes (fail-closed).
//!
//! # Soundness discipline (HARD requirements)
//!
//! * **Every refusal degrades to the status quo.** On ANY per-variable
//!   failure (out-of-fragment matrix, cap/budget exhaustion, self-check
//!   refusal, unrecoverable bound variable) the ORIGINAL quantifier node is
//!   kept byte-for-byte — never a partially-peeled / NNF'd / redistributed
//!   form — so the downstream quantifier loop sees exactly the shapes it sees
//!   today. We never construct new `Forall`/`Exists` nodes at all (no trigger
//!   list to get wrong).
//! * **All-or-nothing per assertion.** A rewritten assertion is adopted only
//!   when it is fully quantifier-free; otherwise the original `TermId` is
//!   kept. All target shapes eliminate fully, and this removes the
//!   partial-rewrite regression surface (the quantifier loop's routing
//!   pattern-matches syntactic shape).
//! * **Vacuous binders are conservatively KEPT** (matching `qe_light`):
//!   `find_bound_var → None` does not prove non-occurrence (`TermData` is
//!   `#[non_exhaustive]` and unrecognized nodes are not traversed), and
//!   dropping a binder whose variable still occurs would free it — the
//!   dangling-binder UNSAT→SAT hazard. Vacuous binders are already collapsed
//!   upstream by `simplify_vacuous_quantifiers`.
//! * **Length preservation.** The `&mut [TermId]` slice signature makes the
//!   1:1 in-place rewrite unable to change the assertion count, so the
//!   scope-frame `assertion_count` invariant (#incremental-pushpop-soundness)
//!   holds even on the path where the quantifier loop's own snapshot/restore
//!   persists the rewritten set (`qr.original_assertions` is `Some`). That
//!   persistence is sound because every per-assertion rewrite is
//!   equivalence-preserving.
//!
//! # Budgets (fail-closed, degrade to status quo)
//!
//! * DNF distribution: at most [`MAX_DNF_DISJUNCTS`] disjuncts and
//!   [`MAX_DNF_NODES`] produced nodes per matrix; over cap refuses the
//!   variable.
//! * At most [`MAX_ELIMINATIONS_PER_APPLY`] eliminator invocations (each pays
//!   a ~200-sample self-check) per `deep_qe` call, i.e. per check-sat.
//! * A cheap fragment screen refuses matrices mentioning UF / arrays /
//!   nonlinear terms / unsupported sorts BEFORE any NNF/DNF work, so
//!   quantifier-heavy UF suites pay ~zero.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use std::collections::HashSet;
use std::sync::atomic::{AtomicBool, Ordering};

use crate::ematching::contains_quantifier;
use crate::preprocess::qe_light::{find_bound_var, mentions_var};
use crate::qe::{eliminate_exists, eliminate_exists_real, QeResult};

/// Hard cap on the number of DNF disjuncts a single matrix may distribute
/// into. Refusing over cap keeps pathological inputs at the status quo.
///
/// #quantprod-g: raised 32 -> 512. The measured `∀x∃y` box probes (G04/G12
/// class) eliminate the inner `y` into a 2-lower x 2-upper LW disjunction
/// whose outer `∀x` peel (negation + ∃-over-∨ distribution) produces a few
/// hundred disjuncts — the engine decides the shape correctly (each disjunct
/// elimination stays individually self-checked; adoption remains all-or-
/// nothing quantifier-free) and only these abort constants blocked it. The
/// real cost bound is the per-elimination `budget.interrupted()` solve-
/// deadline poll, which is wall-clock-based and unchanged.
const MAX_DNF_DISJUNCTS: usize = 512;

/// Hard cap on nodes produced while building the DNF of a single matrix
/// (#quantprod-g: raised 4096 -> 65536 alongside `MAX_DNF_DISJUNCTS`; the
/// wall-clock interrupt poll remains the operative bound).
const MAX_DNF_NODES: usize = 65536;

/// Hard cap on eliminator invocations (Cooper / LW, each self-checked) per
/// `deep_qe` call, i.e. per check-sat. Exhaustion refuses further variables;
/// already-adopted (fully eliminated) rewrites remain valid.
///
/// #quantprod-g: raised 64 -> 8192 so a several-hundred-disjunct distributed
/// matrix (one self-checked elimination per disjunct) completes instead of
/// exhausting mid-assertion. Each invocation still polls the solve-deadline
/// interrupt first, so pathological inputs are wall-clock-bounded, not
/// constant-bounded.
const MAX_ELIMINATIONS_PER_APPLY: usize = 8192;

/// Per-apply elimination budget, shared across all assertions of one call.
struct Budget<'a> {
    eliminations: usize,
    /// The executor's solve-interrupt flag (#clusterD divergence backstop):
    /// polled coarsely — once per eliminator invocation — so an application
    /// watchdog can always land even if an eliminator's per-call work grows.
    /// An observed interrupt refuses the remaining work (status quo kept for
    /// the untouched assertions), never a partial rewrite.
    interrupt: Option<&'a AtomicBool>,
}

impl Budget<'_> {
    fn interrupted(&self) -> bool {
        self.interrupt
            .is_some_and(|flag| flag.load(Ordering::Relaxed))
    }
}

/// Deep QE pre-pass over the assertion set. Each assertion is rewritten
/// post-order with binder descent; the rewrite is adopted only if it is fully
/// quantifier-free (all-or-nothing per assertion), otherwise the original
/// `TermId` is kept verbatim. Returns whether any assertion changed.
///
/// The `&mut [TermId]` signature is load-bearing: the rewrite must be 1:1 and
/// length-preserving (see the module docs).
///
/// `interrupt` is the executor's solve-interrupt flag; when it is set the
/// pre-pass refuses all further elimination work (status quo for the
/// remaining assertions), so an application watchdog can always land.
pub(crate) fn deep_qe(
    terms: &mut TermStore,
    assertions: &mut [TermId],
    interrupt: Option<&AtomicBool>,
) -> bool {
    deep_qe_with_budget(terms, assertions, interrupt, MAX_ELIMINATIONS_PER_APPLY)
}

/// [`deep_qe`] with an explicit per-apply elimination budget.
///
/// Production always passes [`MAX_ELIMINATIONS_PER_APPLY`]; the seam exists
/// so the budget-exhaustion degradation contract stays cheap to exercise in
/// unit tests after the production cap raise (#quantprod-g: 64 -> 8192 —
/// materializing 8192+ self-checked eliminations per test run is minutes of
/// pure test overhead for the same code path).
pub(crate) fn deep_qe_with_budget(
    terms: &mut TermStore,
    assertions: &mut [TermId],
    interrupt: Option<&AtomicBool>,
    eliminations: usize,
) -> bool {
    let mut progress = false;
    // Memoize over the shared hash-consed DAG; sound because the rewrite of a
    // subterm depends only on the subterm itself (each replacement is
    // equivalent for ALL valuations of its free variables, including
    // outer-bound ones). Local to this `deep_qe` call.
    let mut cache: HashMap<TermId, TermId> = HashMap::default();
    let mut budget = Budget {
        eliminations,
        interrupt,
    };
    for a in assertions.iter_mut() {
        if budget.interrupted() {
            break;
        }
        if !contains_quantifier(terms, *a) {
            continue;
        }
        let rewritten = rewrite(terms, *a, &mut cache, &mut budget);
        // All-or-nothing per assertion: adopt only fully-eliminated rewrites.
        if rewritten != *a && !contains_quantifier(terms, rewritten) {
            // #quantprod-a (expansion-over-mod-adoption): refuse an adoption
            // whose rewrite minted `mod`/`div`/`divisible` atoms when the
            // bounded-Int finite-domain expansion can ground the ORIGINAL
            // assertion exactly (probe = the expansion's own analysis,
            // read-only). Cooper's elimination of a guard-bounded forall over
            // a constant-coefficient bound is correct but lands constant-
            // divisor divisibility atoms the ground LIA lane cannot decide
            // (`UnsupportedArithmetic`), pre-empting an exact expansion whose
            // ground verdict is model-gated / proof-backed. Keeping the
            // original changes engines, never semantics; every adoption
            // WITHOUT divisibility atoms (including the pure-arithmetic
            // nested-solve obligations Cooper decides instantly) proceeds
            // byte-identically.
            if rewrite_mints_divisibility(terms, rewritten)
                && crate::skolemize::bounded_expansion_grounds_all_quantifiers(terms, *a)
            {
                continue;
            }
            *a = rewritten;
            progress = true;
        }
    }
    progress
}

/// Does the adopted rewrite contain an integer divisibility construct
/// (`mod` / `div` / `(_ divisible n)` application) anywhere in its DAG?
/// Screen for the #quantprod-a adoption refusal above: these are exactly the
/// atoms Cooper's elimination mints for constant-coefficient bounds and the
/// ground LIA lane then fails closed on.
fn rewrite_mints_divisibility(terms: &TermStore, t: TermId) -> bool {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack = vec![t];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::App(Symbol::Named(name), args) => {
                if name == "mod" || name == "div" || name == "divisible" {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => {
                stack.push(*c);
                stack.push(*a);
                stack.push(*b);
            }
            TermData::Let(bindings, body) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            _ => {}
        }
    }
    false
}

/// Post-order rewrite of `term`: rebuild children, eliminating quantifier
/// nodes whose every bound variable can be peeled. Structured like
/// `preprocess::qe_light::rewrite`, but WITH binder descent.
fn rewrite(
    terms: &mut TermStore,
    term: TermId,
    cache: &mut HashMap<TermId, TermId>,
    budget: &mut Budget<'_>,
) -> TermId {
    if let Some(&cached) = cache.get(&term) {
        return cached;
    }

    let result = match terms.get(term).clone() {
        // Leaves: nothing to rewrite.
        TermData::Const(_) | TermData::Var(_, _) => term,

        TermData::App(sym, args) => {
            let mut changed = false;
            let new_args: Vec<TermId> = args
                .iter()
                .map(|&arg| {
                    let na = rewrite(terms, arg, cache, budget);
                    changed |= na != arg;
                    na
                })
                .collect();
            if changed {
                let sort = terms.sort(term).clone();
                terms.mk_app(sym, new_args, sort)
            } else {
                term
            }
        }

        TermData::Not(inner) => {
            let ni = rewrite(terms, inner, cache, budget);
            if ni == inner {
                term
            } else {
                terms.mk_not(ni)
            }
        }

        TermData::Ite(c, t, e) => {
            let nc = rewrite(terms, c, cache, budget);
            let nt = rewrite(terms, t, cache, budget);
            let ne = rewrite(terms, e, cache, budget);
            if nc == c && nt == t && ne == e {
                term
            } else {
                terms.mk_ite(nc, nt, ne)
            }
        }

        // A `let` should have been expanded before solving; leave it untouched.
        TermData::Let(_, _) => term,

        TermData::Forall(vars, body, _) => {
            try_eliminate_quantifier(terms, term, &vars, body, true, cache, budget)
        }

        TermData::Exists(vars, body, _) => {
            try_eliminate_quantifier(terms, term, &vars, body, false, cache, budget)
        }

        // `TermData` is `#[non_exhaustive]`: any future node kind is left
        // UNCHANGED (faithful identity), never silently rewritten.
        _ => term,
    };

    cache.insert(term, result);
    result
}

/// Attempt to fully eliminate one quantifier node (`∀` via duality). Returns
/// the quantifier-free equivalent when EVERY bound variable peels; returns the
/// ORIGINAL node on any failure (all-or-nothing per node — the downstream
/// quantifier loop must see today's shapes, and rebuilding a binder would also
/// have to decide what to do with the trigger lists).
fn try_eliminate_quantifier(
    terms: &mut TermStore,
    original: TermId,
    vars: &[(String, Sort)],
    body: TermId,
    is_forall: bool,
    cache: &mut HashMap<TermId, TermId>,
    budget: &mut Budget<'_>,
) -> TermId {
    // Innermost-out: rewrite the body first so nested quantifiers are already
    // eliminated (or kept verbatim) before this binder is peeled.
    let mut matrix = rewrite(terms, body, cache, budget);

    // Peel bound variables LAST-to-FIRST: ∃y,z.φ ≡ ∃y.(∃z.φ), dually for ∀.
    for (name, sort) in vars.iter().rev() {
        // Constant fold: Int/Real are nonempty, so ∃v.c ≡ ∀v.c ≡ c.
        if matches!(terms.get(matrix), TermData::Const(Constant::Bool(_))) {
            continue;
        }
        // Recover the EXACT bound-variable node occurring in the matrix.
        // Re-interning by name would mint a phantom variable (mk_fresh_var
        // does not register fresh names; see preprocess::qe_light). `None`
        // does NOT prove non-occurrence (vacuous binder, ambiguous duplicate
        // name, or an untraversed future node kind), so conservatively KEEP
        // the original node, matching qe_light — dropping the binder could
        // free a still-occurring variable (dangling-binder UNSAT→SAT hazard).
        let Some(var) = find_bound_var(terms, matrix, name) else {
            return original;
        };
        // Defensive: the recovered node must carry the binder's declared sort.
        if terms.sort(var) != sort {
            return original;
        }
        let eliminated = if is_forall {
            // ∀-duality: ∀v.ψ ≡ ¬∃v.¬ψ. `mk_not` folds the negation through
            // and/or (De Morgan) and constants; atoms keep a plain `Not`.
            let negated = terms.mk_not(matrix);
            try_eliminate_one(terms, negated, var, budget).map(|qf| terms.mk_not(qf))
        } else {
            try_eliminate_one(terms, matrix, var, budget)
        };
        match eliminated {
            Some(qf) => matrix = qf,
            None => return original,
        }
    }
    matrix
}

/// Eliminate `∃var. matrix` where `matrix` is an arbitrary and/or/not
/// combination of literals: NNF + ∃-over-∨ DNF distribution (hard-capped),
/// per-disjunct sort-dispatched elimination (each independently
/// self-checked), OR of the results, and a final defence-in-depth
/// `mentions_var` gate. Returns `None` on any refusal (fail-closed).
fn try_eliminate_one(
    terms: &mut TermStore,
    matrix: TermId,
    var: TermId,
    budget: &mut Budget<'_>,
) -> Option<TermId> {
    // A constant matrix needs no elimination (∃v.c ≡ c over nonempty Int/Real).
    if matches!(terms.get(matrix), TermData::Const(Constant::Bool(_))) {
        return Some(matrix);
    }
    let var_sort = terms.sort(var).clone();
    // Dedicated `is_int`-only eliminator: LW's fragment screen refuses any
    // matrix containing an `is_int` atom, so try this first on the WHOLE matrix
    // (it handles arbitrary and/or/not/ite structure itself via witness
    // substitution, not per-disjunct). Returns `None` — and we fall through to
    // the LW path — whenever the matrix is not in its fragment (no `is_int`
    // over `var`, a non-unit coefficient, `var` occurring outside an `is_int`,
    // or the self-check refusing). The result is quantifier-free and verified.
    if var_sort == Sort::Real {
        if let Some(qf) = crate::qe::isint::eliminate_exists_isint(terms, matrix, var) {
            // Defence-in-depth: never adopt a result still mentioning `var`.
            if !mentions_var(terms, qf, var) {
                return Some(qf);
            }
        }
    }
    // Cheap fragment screen: refuse UF / arrays / nonlinear / unsupported
    // sorts BEFORE any NNF/DNF work, so out-of-fragment suites pay ~zero.
    if !fragment_screen(terms, matrix, &var_sort) {
        return None;
    }

    // NNF + ∃-over-∨ DNF distribution, hard-capped (fail-closed over cap).
    let mut produced = 0usize;
    let disjuncts = dnf(terms, matrix, true, &mut produced)?;

    // ∃v.(A ∨ B) ≡ (∃v.A) ∨ (∃v.B): eliminate each disjunct independently.
    let mut results: Vec<TermId> = Vec::with_capacity(disjuncts.len());
    for lits in disjuncts {
        let body = terms.mk_and(lits);
        // The folding constructor may collapse the disjunct to a constant
        // (complement pair, empty conjunction); ∃v.c ≡ c.
        if matches!(terms.get(body), TermData::Const(Constant::Bool(_))) {
            results.push(body);
            continue;
        }
        // ∃v.D ≡ D when v does not occur in D. Complete within the screened
        // fragment: every node kind admitted by the screen is traversed by
        // `mentions_var`.
        if !mentions_var(terms, body, var) {
            results.push(body);
            continue;
        }
        if budget.eliminations == 0 {
            return None;
        }
        // Watchdog backstop: refuse (fail-closed) instead of starting another
        // eliminator invocation once an external interrupt has landed.
        if budget.interrupted() {
            return None;
        }
        budget.eliminations -= 1;
        // Sort-dispatched, individually self-checked elimination. EVERY
        // disjunct must eliminate, else the whole variable is refused.
        let elim = match var_sort {
            Sort::Int => eliminate_exists(terms, body, var),
            Sort::Real => eliminate_exists_real(terms, body, var),
            _ => return None,
        };
        match elim {
            QeResult::Eliminated(qf) => results.push(qf),
            QeResult::NotSupported => return None,
        }
    }
    let result = terms.mk_or(results);
    // Defence-in-depth capture gate (mirrors qe_light): never emit a result
    // that still references the eliminated variable.
    if mentions_var(terms, result, var) {
        return None;
    }
    Some(result)
}

/// NNF + DNF-lite: distribute `term` (under the given polarity) into a
/// disjunction of conjunctions of literals. Negation is pushed through
/// `and`/`or`/`not` ONLY; everything else is an atom (negative-polarity atoms
/// are wrapped via `mk_not`, which leaves non-and/or atoms as `Not(atom)` —
/// Cooper's `parse_negated` handles those). Returns `None` when the
/// disjunct/node caps are exceeded (fail-closed).
fn dnf(
    terms: &mut TermStore,
    term: TermId,
    positive: bool,
    produced: &mut usize,
) -> Option<Vec<Vec<TermId>>> {
    *produced += 1;
    if *produced > MAX_DNF_NODES {
        return None;
    }
    match terms.get(term).clone() {
        TermData::Const(Constant::Bool(b)) => {
            if b == positive {
                // Effective `true`: one empty conjunction.
                Some(vec![Vec::new()])
            } else {
                // Effective `false`: empty disjunction.
                Some(Vec::new())
            }
        }
        TermData::Not(inner) => dnf(terms, inner, !positive, produced),
        TermData::App(Symbol::Named(name), args) if name == "and" || name == "or" => {
            // Polarity propagates unchanged to children; only the
            // conjunctive/disjunctive ROLE flips under negation (De Morgan):
            // and⁺/or⁻ are conjunctive, or⁺/and⁻ are disjunctive.
            let conjunctive = (name == "and") == positive;
            if conjunctive {
                // Distribute: cartesian product of the children's disjuncts.
                let mut acc: Vec<Vec<TermId>> = vec![Vec::new()];
                for &arg in &args {
                    let sub = dnf(terms, arg, positive, produced)?;
                    if acc.len() * sub.len() > MAX_DNF_DISJUNCTS {
                        return None;
                    }
                    let mut next: Vec<Vec<TermId>> = Vec::with_capacity(acc.len() * sub.len());
                    for a in &acc {
                        for s in &sub {
                            *produced += a.len() + s.len();
                            if *produced > MAX_DNF_NODES {
                                return None;
                            }
                            let mut merged = a.clone();
                            merged.extend(s.iter().copied());
                            next.push(merged);
                        }
                    }
                    acc = next;
                }
                Some(acc)
            } else {
                // Concatenate the children's disjuncts.
                let mut acc: Vec<Vec<TermId>> = Vec::new();
                for &arg in &args {
                    let sub = dnf(terms, arg, positive, produced)?;
                    acc.extend(sub);
                    if acc.len() > MAX_DNF_DISJUNCTS {
                        return None;
                    }
                }
                Some(acc)
            }
        }
        // Atom. `mk_not` folds double negation / constants; and/or shapes
        // were consumed above, so a negative atom stays a `Not(atom)` literal
        // (or a normalized equivalent).
        _ => {
            let lit = if positive { term } else { terms.mk_not(term) };
            Some(vec![vec![lit]])
        }
    }
}

/// Cheap pre-NNF fragment screen: `true` iff every node of `matrix` is a
/// shape the NNF/DNF layer plus the sort-dispatched eliminator could possibly
/// accept — boolean structure over linear Int/Real atoms. Anything else
/// (UF, arrays, ite, let, nested quantifiers, nonlinear multiplication,
/// non-constant divisors, unsupported sorts, future node kinds) refuses
/// immediately, BEFORE any NNF/DNF work is spent.
fn fragment_screen(terms: &TermStore, matrix: TermId, elim_sort: &Sort) -> bool {
    let mut stack = vec![matrix];
    let mut seen: HashSet<TermId> = HashSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Const(Constant::Bool(_) | Constant::Int(_) | Constant::Rational(_)) => {}
            TermData::Const(_) => return false,
            TermData::Var(_, _) => {
                if !matches!(terms.sort(t), Sort::Bool | Sort::Int | Sort::Real) {
                    return false;
                }
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::App(Symbol::Named(name), args) => {
                match name.as_str() {
                    "and" | "or" | "not" | "=" | "<" | "<=" | ">" | ">=" | "+" | "-" => {}
                    "*" => {
                        // Linear only: at most one non-constant factor.
                        let nonconst = args
                            .iter()
                            .filter(|&&a| !matches!(terms.get(a), TermData::Const(_)))
                            .count();
                        if nonconst > 1 {
                            return false;
                        }
                    }
                    // Cooper accepts `mod` only in the divisibility form with
                    // a constant divisor; anything else it refuses anyway.
                    "mod" if *elim_sort == Sort::Int => {
                        if args.len() != 2
                            || !matches!(terms.get(args[1]), TermData::Const(Constant::Int(_)))
                        {
                            return false;
                        }
                    }
                    // LW accepts `/` only with a constant divisor (linear).
                    "/" if *elim_sort == Sort::Real => {
                        if args.len() != 2 || !matches!(terms.get(args[1]), TermData::Const(_)) {
                            return false;
                        }
                    }
                    // Mixed-sort bridge (Real-var elimination only): LW
                    // purifies `(to_real t)` with Int-sorted `t` into a fresh
                    // Real variable (`qe::lw::purify_to_real`). Refused when
                    // the builtin is shadowed by a user declaration
                    // (uninterpreted — rewriting would fabricate semantics)
                    // and for Int-var elimination, where an un-eliminated
                    // `to_real(x)` over the eliminated Int var is genuinely
                    // out of fragment; refusal degrades to the status quo.
                    // KNOWN LIMIT: multi-`to_real` atoms (e.g.
                    // `to_real(n) - to_real(m) ≤ 1/2`) back-substitute to a
                    // Real atom the constructors don't fold; an OUTER Int-var
                    // peel then refuses via this same screen → status-quo
                    // unknown, never wrong.
                    "to_real" if *elim_sort == Sort::Real => {
                        if terms.to_real_is_shadowed()
                            || args.len() != 1
                            || !matches!(terms.sort(args[0]), Sort::Int)
                        {
                            return false;
                        }
                    }
                    // UF / arrays / div / distinct / xor / …: out of fragment.
                    _ => return false,
                }
                stack.extend(args.iter().copied());
            }
            // Ite / Let / nested quantifiers / any future node kind: refuse.
            _ => return false,
        }
    }
    true
}

#[cfg(test)]
#[path = "qe_prepass_tests.rs"]
mod tests;
