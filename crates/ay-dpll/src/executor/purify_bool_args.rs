// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boolean-argument purification for uninterpreted-function applications.
//!
//! When a Boolean-valued *compound* term `b` (e.g. `(and ...)`, `(= x y)`)
//! appears directly as an argument to an uninterpreted function `f`, the EUF
//! solver cannot reliably congruence-close over `f(b)`: the compound Boolean
//! term never receives a truth assignment that EUF sees, so two applications
//! `f(b1)` and `f(b2)` whose arguments share a truth value are not equated.
//! That gap produced false-SAT results on QF_UF / QF_UFLIA benchmarks
//! (B-method CLEARSY proof obligations: `bool((and ... (= x TRUE)))`).
//!
//! This pass replaces each such compound Boolean argument `b` with a fresh
//! Boolean variable `p` and adds the defining assertion `(= p b)`. The proxy
//! `p` is a plain Boolean variable, which is registered as a theory atom and
//! merged by truth value through the existing EUF machinery — restoring
//! congruence over `f(p)`. The rewrite is equisatisfiable (`p` is fresh and
//! fully defined by `p = b`).

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::{Symbol, TermData, TermId, TermStore};
use ay_core::Sort;

/// Builtin Boolean/term operators whose applications are owned by the SAT
/// layer rather than treated as uninterpreted functions.
fn is_builtin(name: &str) -> bool {
    matches!(
        name,
        "and" | "or" | "xor" | "=>" | "not" | "=" | "distinct" | "ite"
    )
}

/// FP rounding-mode constants were HISTORICALLY stored as Bool-sorted nullary
/// applications (e.g. `(RNA)`), because the FP theory matches them structurally
/// by symbol name rather than by truth value (see `ay-frontend`
/// elaborate/term.rs and `ay-fp::RoundingMode::from_name`). They are NOT
/// logical Booleans: replacing one with a fresh `boolarg` proxy destroys the
/// mode the FP solver needs, which then silently defaults to RNE and yields
/// wrong FP results (a wrong-answer/false-theorem bug for any non-RNE mode).
/// Such a term must never be purified.
///
/// Since the #P0.2 sort fix, RM literals elaborate with
/// `Sort::Uninterpreted("RoundingMode")`, so `needs_proxy`'s `Sort::Bool`
/// check already excludes them and this guard is defense-in-depth only (it
/// still protects any embedder-built Bool-sorted RM app). Keep it.
fn is_rounding_mode_constant(terms: &TermStore, arg: TermId) -> bool {
    match terms.get(arg) {
        TermData::App(Symbol::Named(name), args) if args.is_empty() => {
            matches!(
                name.as_str(),
                "RNE"
                    | "RNA"
                    | "RTP"
                    | "RTN"
                    | "RTZ"
                    | "roundNearestTiesToEven"
                    | "roundNearestTiesToAway"
                    | "roundTowardPositive"
                    | "roundTowardNegative"
                    | "roundTowardZero"
            )
        }
        _ => false,
    }
}

/// A Boolean-sorted argument needs purification iff it is a *compound* term
/// (anything other than a plain variable or constant). Plain Bool variables
/// already flow through EUF's Bool-value merge correctly.
fn needs_proxy(terms: &TermStore, arg: TermId) -> bool {
    if terms.sort(arg) != &Sort::Bool {
        return false;
    }
    // FP rounding-mode constants share the Bool sort but carry FP-theory
    // semantics read structurally; purifying them is unsound (see helper).
    if is_rounding_mode_constant(terms, arg) {
        return false;
    }
    !matches!(terms.get(arg), TermData::Var(_, _) | TermData::Const(_))
}

/// Collect every compound Boolean term that appears as an argument to a
/// (non-builtin) uninterpreted function application. Does not descend into
/// quantifier bodies, so collected terms are closed (capture-safe to hoist).
fn collect(
    terms: &TermStore,
    root: TermId,
    seen: &mut DetHashSet<TermId>,
    targets: &mut DetHashSet<TermId>,
) {
    if !seen.insert(root) {
        return;
    }
    match terms.get(root).clone() {
        TermData::Const(_) | TermData::Var(_, _) => {}
        TermData::App(sym, args) => {
            let uf = matches!(&sym, Symbol::Named(n) if !is_builtin(n));
            for &a in &args {
                if uf && needs_proxy(terms, a) {
                    targets.insert(a);
                }
                collect(terms, a, seen, targets);
            }
        }
        TermData::Not(x) => collect(terms, x, seen, targets),
        TermData::Ite(c, t, e) => {
            collect(terms, c, seen, targets);
            collect(terms, t, seen, targets);
            collect(terms, e, seen, targets);
        }
        TermData::Let(binds, body) => {
            for (_, v) in binds {
                collect(terms, v, seen, targets);
            }
            collect(terms, body, seen, targets);
        }
        // Do not descend into quantifier bodies: a compound Bool arg there may
        // reference bound variables (not a closed term) and must not be hoisted
        // to a global proxy. The target divisions (QF_UF / QF_UFLIA) are
        // quantifier-free.
        TermData::Forall(..) | TermData::Exists(..) => {}
        // TermData is #[non_exhaustive]; unknown constructs are left
        // un-purified (conservative — never unsound).
        _ => {}
    }
}

/// Purify compound Boolean arguments to uninterpreted functions in `assertions`.
///
/// Returns `true` if any purification occurred. Appends `(= proxy original)`
/// definitions to `assertions`. Equisatisfiable.
pub(crate) fn purify_bool_args(terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
    let mut seen = DetHashSet::default();
    let mut targets = DetHashSet::default();
    for &root in assertions.iter() {
        collect(terms, root, &mut seen, &mut targets);
    }
    if targets.is_empty() {
        return false;
    }

    // Deterministic order for fresh-var allocation.
    let mut ordered: Vec<TermId> = targets.iter().copied().collect();
    ordered.sort_unstable_by_key(|t| t.0);

    let mut map: DetHashMap<TermId, TermId> = DetHashMap::default();
    let mut defs: Vec<TermId> = Vec::with_capacity(ordered.len());
    for b in ordered {
        let p = terms.mk_fresh_var("boolarg", Sort::Bool);
        map.insert(b, p);
        // Defining constraint p = b (uses the original, un-rewritten b).
        defs.push(terms.mk_eq(p, b));
    }

    for root in assertions.iter_mut() {
        *root = terms.substitute_terms(*root, &map);
    }
    assertions.extend(defs);
    true
}

#[cfg(test)]
mod tests;
