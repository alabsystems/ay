// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `count_free_fd_classes` checks its union-find forest once, not per lookup.

use super::super::union_find::whole_forest_scans;
use crate::LiaSolver;
use ay_core::kani_compat::DetHashMap;
use ay_core::term::{TermId, TermStore};
use ay_core::{Sort, TheorySolver};
use num_bigint::BigInt;

/// The whole-forest check was moved, not dropped: 1,023 equality edges (2,046
/// lookups) and 1,024 class lookups scan the forest exactly once in a debug
/// build (never in release, where `debug_assert!` is compiled out), where the
/// per-lookup form scanned it 3,070 times.
#[test]
fn count_free_fd_classes_checks_its_forest_once() {
    const N: usize = 1024;
    let mut store = TermStore::new();
    let vars: Vec<TermId> = (0..N)
        .map(|i| store.mk_var(format!("x{i}"), Sort::Int))
        .collect();
    // x0 = x1 = ... = x1023: one equality class.
    let eqs: Vec<TermId> = vars
        .iter()
        .zip(vars.iter().skip(1))
        .map(|(&a, &b)| store.mk_eq(a, b))
        .collect();
    let mut lia = LiaSolver::new(&store);
    for &eq in &eqs {
        lia.assert_literal(eq, true);
    }
    let mut term_to_idx: DetHashMap<TermId, usize> = DetHashMap::default();
    for (i, &v) in vars.iter().enumerate() {
        term_to_idx.insert(v, i);
    }
    // Every column has a two-value domain, so every column is looked up.
    let domains = vec![vec![BigInt::from(0), BigInt::from(1)]; N];
    let before = whole_forest_scans();
    assert_eq!(lia.count_free_fd_classes(&term_to_idx, &domains), 1);
    assert_eq!(
        whole_forest_scans().saturating_sub(before),
        usize::from(cfg!(debug_assertions)),
        "one whole-forest check per call, zero per lookup"
    );
}

/// Build the opaque UF application `f(1)`, the constants `0` and `5`, and the
/// bound atoms `0 <= f(1)` and `f(1) <= 0`, returned in that order.
fn pinned_uf_application(store: &mut TermStore) -> (TermId, TermId, TermId, TermId, TermId) {
    use ay_core::term::Symbol;
    let one = store.mk_int(BigInt::from(1));
    let zero = store.mk_int(BigInt::from(0));
    let five = store.mk_int(BigInt::from(5));
    let f1 = store.mk_app(Symbol::named("f"), [one], Sort::Int);
    let lower = store.mk_le(zero, f1);
    let upper = store.mk_le(f1, zero);
    (f1, zero, five, lower, upper)
}

/// AY-SMT-2 (2026-11-19): the finite-domain lane saw only the asserted
/// literals, so with `0 <= f(1) <= 0` asserted and the EUF disequality
/// `f(1) != 0` forwarded as a SHARED pair, it returned the witness
/// `f(1) = 0` and LIA answered `Sat` on an UNSAT set. In the conflict
/// verifier's combiner that `Sat` rejected the genuine conflict and turned
/// the query `unknown` (`(<= 0 (f 1)) (<= (f 1) 0) (not (= 0 (f 1)))`).
#[test]
fn finite_domain_witness_respects_shared_disequalities() {
    use ay_core::TheoryLit;
    let mut store = TermStore::new();
    let (f1, zero, _five, lower, upper) = pinned_uf_application(&mut store);
    let diseq_atom = store.mk_eq(zero, f1);
    let mut lia = LiaSolver::new(&store);
    lia.set_combined_theory_mode(true);
    for atom in [lower, upper, diseq_atom] {
        lia.register_atom(atom);
    }
    lia.assert_literal(lower, true);
    lia.assert_literal(upper, true);
    lia.assert_shared_disequality(f1, zero, &[TheoryLit::new(diseq_atom, false)]);
    assert!(
        !matches!(
            lia.try_finite_domain_search(),
            crate::DirectEnumResult::SatWitness
        ),
        "the witness f(1) = 0 violates the shared disequality f(1) != 0"
    );
}

/// Control for the test above: a shared disequality the witness satisfies
/// (`f(1) != 5`) still lets the finite-domain lane answer with its witness,
/// so the check is not a blanket refusal.
#[test]
fn finite_domain_witness_kept_when_shared_disequality_holds() {
    use ay_core::TheoryLit;
    let mut store = TermStore::new();
    let (f1, _zero, five, lower, upper) = pinned_uf_application(&mut store);
    let diseq_atom = store.mk_eq(five, f1);
    let mut lia = LiaSolver::new(&store);
    lia.set_combined_theory_mode(true);
    for atom in [lower, upper, diseq_atom] {
        lia.register_atom(atom);
    }
    lia.assert_literal(lower, true);
    lia.assert_literal(upper, true);
    lia.assert_shared_disequality(f1, five, &[TheoryLit::new(diseq_atom, false)]);
    assert!(matches!(
        lia.try_finite_domain_search(),
        crate::DirectEnumResult::SatWitness
    ));
}

/// AY-SMT-2 (2026-11-19), the UFLIA rescue lane: with `x = y` shared,
/// `0 <= x, y <= 0` and `0 <= f(x) <= 1` asserted, and `f(x) != 0` forwarded
/// by EUF as a SHARED disequality, the rescue must install a witness that
/// keeps the disequality (`f(x) = 1`). Before the change the rescue saw only
/// the asserted literals and the shared equalities and could install
/// `f(x) = 0`; the first fix attempt threw that witness away instead. Shared
/// disequalities are now search constraints, so the witness found keeps them.
#[test]
fn uflia_rescue_witness_keeps_shared_disequality() {
    use ay_core::term::Symbol;
    use ay_core::TheoryLit;
    let mut store = TermStore::new();
    let x = store.mk_var("x", Sort::Int);
    let y = store.mk_var("y", Sort::Int);
    let zero = store.mk_int(BigInt::from(0));
    let one = store.mk_int(BigInt::from(1));
    let fx = store.mk_app(Symbol::named("f"), [x], Sort::Int);
    let x_lo = store.mk_le(zero, x);
    let x_hi = store.mk_le(x, zero);
    let y_lo = store.mk_le(zero, y);
    let y_hi = store.mk_le(y, zero);
    let fx_lo = store.mk_le(zero, fx);
    let fx_hi = store.mk_le(fx, one);
    let xy = store.mk_eq(x, y);
    let fx_zero = store.mk_eq(fx, zero);
    let mut lia = LiaSolver::new(&store);
    lia.set_combined_theory_mode(true);
    let bounds = [x_lo, x_hi, y_lo, y_hi, fx_lo, fx_hi];
    for atom in bounds.iter().copied().chain([xy, fx_zero]) {
        lia.register_atom(atom);
    }
    for atom in bounds {
        lia.assert_literal(atom, true);
    }
    lia.assert_shared_equality(x, y, &[TheoryLit::new(xy, true)]);
    lia.assert_shared_disequality(fx, zero, &[TheoryLit::new(fx_zero, false)]);
    assert!(
        lia.try_finite_domain_uflia(),
        "f(x) = 1 satisfies every constraint, so the rescue must find it"
    );
    let witness = lia
        .direct_enum_witness
        .as_ref()
        .expect("an installed rescue witness");
    assert_eq!(
        witness.values.get(&fx),
        Some(&BigInt::from(1)),
        "the installed witness must keep the shared disequality f(x) != 0"
    );
}
