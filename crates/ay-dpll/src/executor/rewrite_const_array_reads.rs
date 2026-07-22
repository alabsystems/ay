// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preprocessing rewrite of const-array reads through a ground equality.
//!
//! `mk_select` already simplifies a *syntactic* read of a constant array —
//! `select(const-array(v), i) -> v` (`ay-core/src/term/array.rs`). But when the
//! array is a *variable* `V` that is only tied to a constant array by a separate
//! ground assertion `V = const-array(c)`, the read `select(V, i)` stays opaque:
//! the array is `V`, not the const-array term, so the term-level rewrite never
//! fires. LRA/LIA then treats `select(V, i)` as an unknown function (traces show
//! `[LRA] Unknown function: const-array`), and any arithmetic that consumes the
//! read — e.g. the set-length definition
//! `(= len_{n} (+ len_{n-1} (ite (select V k) 0 1)))` — is left with the read
//! unconstrained. The read value only reaches the array theory *late*, via the
//! LRA ite-link lemmas created on the first SAT, by which point the length aux
//! vars have already been committed with a stale value, so a genuinely
//! satisfiable formula (a real counterexample, e.g. `4 ∉ {1,2,3}`) stalls to
//! `unknown` under strict BV-backed-array model validation.
//!
//! This pass closes that gap up front. For every top-level *unit* assertion of
//! the form `V = const-array(c)` (an unconditional ground fact — not nested
//! inside an `ite`, disjunction, or quantifier), it rewrites every syntactic
//! read `select(V, idx)` — wherever it appears — to the default value `c`. The
//! rewrite runs before theory setup, so the len-definition ites collapse
//! (`(ite false 0 1) -> 1`) and LIA computes the lengths concretely, with no
//! opaque read and no reliance on late ite-link registration.
//!
//! SOUNDNESS. `select(const-array(c), idx) = c` is universally valid, and under
//! the ground equality `V = const-array(c)` (asserted as a top-level unit fact,
//! true in every model of the assertion set) `select(V, idx) = c` holds in every
//! model. Replacing each such read with `c` therefore neither adds nor removes a
//! model — it is equisatisfiable (no wrong-SAT, no wrong-UNSAT). The equality
//! assertion itself is left in place, so array-theory reasoning that depends on
//! it (default, extensionality) is unaffected. The gate is deliberately narrow:
//! only a top-level assertion that *is* the equality qualifies, so the fact is
//! never speculative; a `V` bound to two different const-array defaults is
//! dropped (its models are contradictory, and UNSAT is preserved by the retained
//! equalities regardless). The read's index may be a bound variable inside a
//! quantifier — replacing the whole read with the closed term `c` is still
//! valid (`select(const-array(c), x) = c` for every `x`) and capture-free.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::{Symbol, TermData, TermId, TermStore};

/// Collect `V -> c` for every top-level unit assertion `V = const-array(c)`.
/// A `V` mapped to two distinct defaults is dropped (recorded as conflicted),
/// so only an unambiguous ground default is ever propagated.
fn collect_ground_const_arrays(
    terms: &TermStore,
    assertions: &[TermId],
) -> DetHashMap<TermId, TermId> {
    let mut const_of: DetHashMap<TermId, TermId> = DetHashMap::default();
    let mut conflicted: DetHashSet<TermId> = DetHashSet::default();

    for &root in assertions {
        let TermData::App(Symbol::Named(n), args) = terms.get(root) else {
            continue;
        };
        if n != "=" || args.len() != 2 {
            continue;
        }
        let (a, b) = (args[0], args[1]);
        // Exactly one side must be a const-array term; the other is `V`.
        let (v, c) = if let Some(c) = terms.get_const_array(a) {
            if terms.get_const_array(b).is_some() {
                // Both sides const-array: a pure const-array equality, nothing to
                // propagate a variable read through.
                continue;
            }
            (b, c)
        } else if let Some(c) = terms.get_const_array(b) {
            (a, c)
        } else {
            continue;
        };

        match const_of.get(&v) {
            Some(&existing) if existing != c => {
                conflicted.insert(v);
            }
            _ => {
                const_of.insert(v, c);
            }
        }
    }

    for v in conflicted {
        const_of.remove(&v);
    }
    const_of
}

/// Walk the Boolean/arithmetic skeleton and, for every `select(V, idx)` whose
/// array `V` has a ground const-array default, record `select_term -> c`.
///
/// Does NOT descend into quantifier bodies. Rewriting `select(V, x)` for a bound
/// index `x` would be perfectly *sound* (`select(const-array(c), x) = c` for
/// every `x`), but the read term is frequently the E-matching *trigger* the
/// quantifier instantiation is keyed on; eliminating it perturbs the
/// instantiation heuristics and can turn a previously-discharged quantified
/// proof (e.g. multiset extensional equality) into `unknown`. Restricting to the
/// quantifier-free skeleton — exactly as `purify_int_uf_arith` does — keeps the
/// completeness-preserving guarantee: the set-length ite-definitions this pass
/// targets are ground, so they are still rewritten, while quantified proofs are
/// left untouched.
fn collect_reads(
    terms: &TermStore,
    root: TermId,
    const_of: &DetHashMap<TermId, TermId>,
    seen: &mut DetHashSet<TermId>,
    reads: &mut DetHashMap<TermId, TermId>,
) {
    if !seen.insert(root) {
        return;
    }
    match terms.get(root).clone() {
        TermData::App(sym, args) => {
            if matches!(&sym, Symbol::Named(n) if n == "select") && args.len() == 2 {
                if let Some(&c) = const_of.get(&args[0]) {
                    reads.insert(root, c);
                }
            }
            for a in args {
                collect_reads(terms, a, const_of, seen, reads);
            }
        }
        TermData::Not(x) => collect_reads(terms, x, const_of, seen, reads),
        TermData::Ite(c, t, e) => {
            collect_reads(terms, c, const_of, seen, reads);
            collect_reads(terms, t, const_of, seen, reads);
            collect_reads(terms, e, const_of, seen, reads);
        }
        TermData::Let(binds, body) => {
            for (_, v) in binds {
                collect_reads(terms, v, const_of, seen, reads);
            }
            collect_reads(terms, body, const_of, seen, reads);
        }
        // Do not descend into quantifier bodies: a read there is often the
        // E-matching trigger the instantiation is keyed on, and eliminating it
        // (though sound) can regress a quantified proof to `unknown`.
        TermData::Forall(..) | TermData::Exists(..) => {}
        TermData::Const(_) | TermData::Var(_, _) => {}
        // TermData is #[non_exhaustive]; unknown constructs are left untouched
        // (conservative — never unsound).
        _ => {}
    }
}

/// Collect every const-array read term that occurs anywhere inside a quantifier
/// body into `tainted`. Because `substitute_terms` rewrites by `TermId` and
/// descends into quantifier bodies, a read that is *also* used under a quantifier
/// (a shared subterm) must be excluded from the rewrite entirely — otherwise the
/// quantifier body would be altered and a working quantified proof could regress.
fn collect_quantifier_tainted(
    terms: &TermStore,
    root: TermId,
    const_of: &DetHashMap<TermId, TermId>,
    under_quantifier: bool,
    seen: &mut DetHashSet<(TermId, bool)>,
    tainted: &mut DetHashSet<TermId>,
) {
    if !seen.insert((root, under_quantifier)) {
        return;
    }
    match terms.get(root).clone() {
        TermData::App(sym, args) => {
            if under_quantifier
                && matches!(&sym, Symbol::Named(n) if n == "select")
                && args.len() == 2
                && const_of.contains_key(&args[0])
            {
                tainted.insert(root);
            }
            for a in args {
                collect_quantifier_tainted(terms, a, const_of, under_quantifier, seen, tainted);
            }
        }
        TermData::Not(x) => {
            collect_quantifier_tainted(terms, x, const_of, under_quantifier, seen, tainted)
        }
        TermData::Ite(c, t, e) => {
            collect_quantifier_tainted(terms, c, const_of, under_quantifier, seen, tainted);
            collect_quantifier_tainted(terms, t, const_of, under_quantifier, seen, tainted);
            collect_quantifier_tainted(terms, e, const_of, under_quantifier, seen, tainted);
        }
        TermData::Let(binds, body) => {
            for (_, v) in binds {
                collect_quantifier_tainted(terms, v, const_of, under_quantifier, seen, tainted);
            }
            collect_quantifier_tainted(terms, body, const_of, under_quantifier, seen, tainted);
        }
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
            collect_quantifier_tainted(terms, body, const_of, true, seen, tainted);
        }
        _ => {}
    }
}

/// Rewrite const-array reads through ground `V = const-array(c)` equalities.
///
/// Returns `true` if any read was rewritten. Equisatisfiable; a no-op when there
/// is no ground const-array equality with a matching syntactic read.
pub(crate) fn rewrite_const_array_reads(terms: &mut TermStore, assertions: &mut [TermId]) -> bool {
    let const_of = collect_ground_const_arrays(terms, assertions);
    if const_of.is_empty() {
        return false;
    }

    let mut seen = DetHashSet::default();
    let mut reads: DetHashMap<TermId, TermId> = DetHashMap::default();
    for &root in assertions.iter() {
        collect_reads(terms, root, &const_of, &mut seen, &mut reads);
    }
    if reads.is_empty() {
        return false;
    }

    // Drop any read that also appears inside a quantifier body: rewriting it
    // would alter the quantifier (a shared trigger term) and can regress an
    // otherwise-discharged quantified proof to `unknown`.
    let mut tseen = DetHashSet::default();
    let mut tainted = DetHashSet::default();
    for &root in assertions.iter() {
        collect_quantifier_tainted(terms, root, &const_of, false, &mut tseen, &mut tainted);
    }
    reads.retain(|k, _| !tainted.contains(k));
    if reads.is_empty() {
        return false;
    }

    for root in assertions.iter_mut() {
        let substituted = terms.substitute_terms(*root, &reads);
        // `substitute_terms` interns the rewritten equality raw, bypassing the
        // folding builders, so a read replaced by a constant can leave a fully
        // constant atom like `(= 2 1)` unfolded. Re-simplify so such ground-false
        // (or -true) atoms collapse to `false`/`true`; otherwise a constant
        // (dis)equality survives as an opaque theory atom that the array-logic
        // route never refutes, stalling a decidable formula to `unknown`.
        *root = terms.simplify(substituted);
    }
    true
}

#[cfg(test)]
mod tests;
