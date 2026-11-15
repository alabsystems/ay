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

mod closure;

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
/// quantifier bodies. These are candidates: retained raw binders require the
/// complete occurrence-sensitive closure admission before global hoisting.
fn collect(
    terms: &TermStore,
    root: TermId,
    seen: &mut DetHashSet<TermId>,
    targets: &mut DetHashSet<TermId>,
    retained_binders: &mut bool,
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
                collect(terms, a, seen, targets, retained_binders);
            }
        }
        TermData::Not(x) => collect(terms, x, seen, targets, retained_binders),
        TermData::Ite(c, t, e) => {
            collect(terms, c, seen, targets, retained_binders);
            collect(terms, t, seen, targets, retained_binders);
            collect(terms, e, seen, targets, retained_binders);
        }
        TermData::Let(binds, body) => {
            *retained_binders = true;
            for (_, v) in binds {
                collect(terms, v, seen, targets, retained_binders);
            }
            collect(terms, body, seen, targets, retained_binders);
        }
        // Do not descend into quantifier bodies: a compound Bool arg there may
        // reference bound variables (not a closed term) and must not be hoisted
        // to a global proxy. The target divisions (QF_UF / QF_UFLIA) are
        // quantifier-free.
        TermData::Forall(..) | TermData::Exists(..) => *retained_binders = true,
        // Unknown binding syntax requires the closure analysis to decline the
        // whole rewrite; it must not be mistaken for a free-name-empty term.
        _ => *retained_binders = true,
    }
}

/// Purify compound Boolean arguments to uninterpreted functions in `assertions`.
///
/// Appends `(= proxy original)` definitions to `assertions`. Equisatisfiable.
///
/// RETURNS the ORPHAN INDEX: `original UF application -> rewritten counterpart`
/// for every uninterpreted-function application this pass rewrote. The solver
/// only ever sees the rewritten term, so it is the only one a model pins; the
/// ORIGINAL is what every post-solve consumer (`get-value`, in-loop validation,
/// and the independent model gate, all of which run against the RESTORED
/// original assertions) asks about. Without the index those consumers find no
/// committed value for an application the solve decided, and a genuine `sat`
/// fails closed to `unknown` (#boolarg-orphan).
///
/// Empty when nothing was purified — callers overwrite their stored index
/// unconditionally so a previous check-sat's proxies can never be read back.
pub(crate) fn purify_bool_args(
    terms: &mut TermStore,
    assertions: &mut Vec<TermId>,
) -> DetHashMap<TermId, TermId> {
    let mut seen = DetHashSet::default();
    let mut targets = DetHashSet::default();
    let mut retained_binders = false;
    for &root in assertions.iter() {
        collect(terms, root, &mut seen, &mut targets, &mut retained_binders);
    }
    if targets.is_empty() {
        return DetHashMap::default();
    }
    // Ground inputs retain the existing allocation/rewrite path. Raw binders
    // require one complete immutable admission before any proxy is allocated.
    let binder_names = if retained_binders {
        let Some(names) = closure::retain_closed(terms, assertions, &mut targets) else {
            return DetHashMap::default();
        };
        if targets.is_empty() {
            return DetHashMap::default();
        }
        names
    } else {
        DetHashSet::default()
    };

    // Deterministic order for fresh-var allocation.
    let mut ordered: Vec<TermId> = targets.iter().copied().collect();
    ordered.sort_unstable_by_key(|t| t.0);

    let mut map: DetHashMap<TermId, TermId> = DetHashMap::default();
    let mut defs: Vec<TermId> = Vec::with_capacity(ordered.len());
    for b in ordered {
        let p = loop {
            let proxy = terms.mk_fresh_var("boolarg", Sort::Bool);
            let TermData::Var(name, _) = terms.get(proxy) else {
                // Constructor shape is not permission to rewrite on an
                // unexpected future representation. No root has changed yet.
                return DetHashMap::default();
            };
            // Unused raw binder strings need not occur in the variable-name
            // registry mk_fresh_var checks. Do not insert a captured proxy.
            if !binder_names.contains(name.as_str()) {
                break proxy;
            }
        };
        map.insert(b, p);
        // Defining constraint p = b (uses the original, un-rewritten b).
        defs.push(terms.mk_eq(p, b));
    }

    // One shared rewrite cache across every assertion: it accumulates
    // `original -> rewritten` for each sub-term the walk RECONSTRUCTED, which
    // is exactly the set of terms the solve orphaned.
    let mut rewritten: DetHashMap<TermId, TermId> = DetHashMap::default();
    for root in assertions.iter_mut() {
        *root = terms.substitute_terms_recording(*root, &map, &mut rewritten);
    }
    assertions.extend(defs);

    // Keep only genuine UF APPLICATIONS that actually changed. Unchanged
    // entries (`t -> t`) carry no information, and a rewritten BUILT-IN
    // connective must NEVER be indexed: the independent model gate computes
    // `and`/`or`/`not`/`=` from its own leaf reads, and letting it adopt the
    // solver's value for a rewritten connective instead would replace an
    // independent computation with the solver's claim — the one thing the gate
    // exists to avoid.
    rewritten.retain(|orig, twin| {
        orig != twin
            && matches!(
                terms.get(*orig),
                TermData::App(Symbol::Named(n), args) if !is_builtin(n) && !args.is_empty()
            )
    });
    rewritten
}

/// [`purify_bool_args`] over the assertions NOT in `settled` only.
///
/// For assertions added after the check-sat purification (quantifier
/// instances). The settled assertions, already purified, are left exactly as
/// they are: the new proxies are substituted into the new assertions alone,
/// so no earlier assertion or proxy definition is rewritten. Returns the
/// orphan index of the new rewrites, for the caller to add to its own.
pub(crate) fn purify_new_bool_args(
    terms: &mut TermStore,
    assertions: &mut Vec<TermId>,
    settled: &DetHashSet<TermId>,
) -> DetHashMap<TermId, TermId> {
    let fresh: Vec<usize> = (0..assertions.len())
        .filter(|&i| !settled.contains(&assertions[i]))
        .collect();
    if fresh.is_empty() {
        return DetHashMap::default();
    }
    let mut window: Vec<TermId> = fresh.iter().map(|&i| assertions[i]).collect();
    let orphans = purify_bool_args(terms, &mut window);
    for (slot, &i) in fresh.iter().enumerate() {
        assertions[i] = window[slot];
    }
    assertions.extend_from_slice(&window[fresh.len()..]);
    orphans
}

impl crate::executor::Executor {
    /// [`Self::process_quantifiers`], then, in a solve that publishes without
    /// a proof, [`purify_new_bool_args`] over the assertions it added.
    ///
    /// The instances quantifier preprocessing adds are built after check-sat's
    /// Boolean-argument purification, so a compound Boolean argument of an
    /// instance (`(B (< 10 (%I t)))` from a definition's body) would reach EUF
    /// as an argument it cannot congruence-close over. The already-purified
    /// assertions are left untouched, and the new rewrites join the orphan
    /// index the model gate reads.
    ///
    /// A proof-carrying solve keeps the instances as they are: a refutation
    /// through an instance's proxy rests on an EUF lemma the strict proof
    /// checker rejects (`EufCongruentPred` over a proxy predicate), so that
    /// solve would end `unknown` on queries it refutes unpurified.
    pub(in crate::executor) fn process_quantifiers_purifying_bool_args(
        &mut self,
    ) -> crate::executor::quantifier_loop::QuantifierProcessingResult {
        if !self.competition_shedding_active() {
            return self.process_quantifiers();
        }
        let settled: DetHashSet<TermId> = self.ctx.assertions.iter().copied().collect();
        let processed = self.process_quantifiers();
        let instance_orphans =
            purify_new_bool_args(&mut self.ctx.terms, &mut self.ctx.assertions, &settled);
        self.bool_arg_orphan_index.extend(instance_orphans);
        processed
    }
}

#[cfg(test)]
mod tests;
