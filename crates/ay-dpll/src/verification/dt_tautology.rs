// Copyright 2026 Andrew Yates
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0

//! Datatype *tautology* axioms for conflict re-verification (#8123).
//!
//! The semantic conflict verifier ([`crate::verification::verify_euf_conflict`])
//! re-solves a theory conflict in a fresh EUF solver. For datatype conflicts the
//! relevant facts — distinct constructors are disjoint (`Ok(a) != Err(b)`),
//! and testers evaluate on constructor values (`is-Ok(Ok(a)) = true`,
//! `is-Err(Ok(a)) = false`) — are *implicit* in the production DT solver and are
//! never materialized into the conflict literals. A fresh EUF solver therefore
//! sees `Ok`/`Err` as ordinary uninterpreted functions and reports the conflict
//! `self = Ok(a) AND self = Err(b)` as SAT, causing a spurious rejection.
//!
//! This module generates the datatype **tautology** literals (true in every
//! model) so the verifier can assert them alongside the conflict and confirm a
//! genuine UNSAT. Soundness: every generated literal is a datatype tautology, so
//!  - asserting them can only let the verifier CONFIRM genuine conflicts (an
//!    UNSAT-given-true-axioms set is genuinely UNSAT), and
//!  - it can NEVER manufacture a spurious conflict (a truly-SAT literal set
//!    already satisfies these tautologies, so it stays SAT).
//!
//! The literals are generated eagerly at DT-solver setup time, where a mutable
//! `TermStore` borrow is available, and stashed on `DpllT` for the verifier to
//! re-assert. This avoids threading a `&mut TermStore` through the verification
//! path (which only holds `&TermStore`).

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::Symbol;
use ay_core::{Sort, TermData, TermId, TermStore, TheoryLit};
use std::collections::HashMap;

/// Build the datatype tautology literals for every constructor application
/// reachable in `terms`.
///
/// # Arguments
/// * `terms` - mutable term store (axiom terms are interned here; `mk_*` dedups)
/// * `dt_ctors` - map from datatype name to its constructor names
///
/// # Returns
/// A vector of `TheoryLit`s, each a datatype tautology, suitable for assertion
/// into a fresh verification solver:
/// - **Disjointness**: `(not (= C(a) C'(b)))` for every pair of constructor
///   applications of the same datatype with distinct constructors `C != C'`.
/// - **Tester evaluation**: `(= (is-C' C(a)) true|false)` for each constructor
///   application `C(a)` and each constructor `C'` of its datatype.
///
/// Returns an empty vector when no datatypes are declared.
pub(crate) fn build_datatype_tautology_axioms(
    terms: &mut TermStore,
    dt_ctors: &HashMap<String, Vec<String>>,
) -> Vec<TheoryLit> {
    if dt_ctors.is_empty() {
        return Vec::new();
    }

    // Reverse map: constructor name -> datatype name.
    let mut ctor_to_dt: HashMap<&str, &str> = HashMap::new();
    for (dt_name, ctors) in dt_ctors {
        for ctor in ctors {
            ctor_to_dt.insert(ctor.as_str(), dt_name.as_str());
        }
    }

    // Collect every constructor application term currently in the store, grouped
    // by datatype. A constructor application is `App(Named(name), _)` where
    // `name` is a registered constructor. (Nullary constructors such as `None`
    // are `App(Named("None"), [])` after elaboration; they are included so that
    // `is-None(None) = true` is available.)
    //
    // Group key is the datatype name; value is a list of (ctor_app_term,
    // ctor_name) so that disjointness and tester-eval axioms can be produced.
    let mut by_dt: HashMap<&str, Vec<(TermId, &str)>> = HashMap::new();
    for id in terms.term_ids() {
        if let TermData::App(Symbol::Named(name), _args) = terms.get(id) {
            if let Some(&dt_name) = ctor_to_dt.get(name.as_str()) {
                // Resolve to the registered constructor name slice for stable
                // lifetime (the &str from `name` borrows `terms`, which we will
                // mutate below; switch to the registry's &str instead).
                let ctor_name = dt_ctors[dt_name]
                    .iter()
                    .find(|c| c.as_str() == name.as_str())
                    .map(String::as_str)
                    .expect("ctor_to_dt entry implies registry membership");
                by_dt.entry(dt_name).or_default().push((id, ctor_name));
            }
        }
    }

    if by_dt.values().all(Vec::is_empty) {
        return Vec::new();
    }

    let true_term = terms.true_term();
    let false_term = terms.false_term();

    let mut axioms: Vec<TheoryLit> = Vec::new();
    let mut seen: HashSet<TermId> = HashSet::default();

    // Deterministic iteration order over datatypes for reproducible axiom sets.
    let mut dt_names: Vec<&str> = by_dt.keys().copied().collect();
    dt_names.sort_unstable();

    for dt_name in dt_names {
        let ctor_apps = &by_dt[dt_name];
        let all_ctors = &dt_ctors[dt_name];

        // (1) Disjointness: distinct-constructor applications are unequal.
        // `(not (= C(a) C'(b)))` for every unordered pair with C != C'.
        for i in 0..ctor_apps.len() {
            let (app_i, ctor_i) = ctor_apps[i];
            for &(app_j, ctor_j) in &ctor_apps[i + 1..] {
                if ctor_i == ctor_j {
                    continue;
                }
                let eq = terms.mk_eq(app_i, app_j);
                let neq = terms.mk_not(eq);
                if seen.insert(neq) {
                    axioms.push(TheoryLit::new(neq, true));
                }
            }
        }

        // (2) Tester evaluation: `is-C'(C(a)) = (C' == C)`.
        // For each constructor application `C(a)` and each constructor `C'` of
        // the same datatype, the recognizer evaluates concretely. This closes
        // tester-shaped conflicts and reinforces disjointness through testers.
        for &(app, ctor) in ctor_apps {
            for other_ctor in all_ctors {
                let tester_name = format!("is-{other_ctor}");
                let tester_app = terms.mk_app(Symbol::named(&tester_name), vec![app], Sort::Bool);
                let expected = if other_ctor.as_str() == ctor {
                    true_term
                } else {
                    false_term
                };
                let eq = terms.mk_eq(tester_app, expected);
                if seen.insert(eq) {
                    axioms.push(TheoryLit::new(eq, true));
                }
            }
        }
    }

    axioms
}
