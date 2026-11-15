// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #nia-split-probe: `try_split_probe` is a short clausal local search over
//! the ORIGINAL assertions, run at most once per solve (one flag shared by
//! every theory instance of the split loop). SAT-only: it claims a model only
//! when every root assertion evaluates true under it, and it leaves the full
//! local-search lane available.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use super::*;

/// `x*y = 12 ∧ x >= 3 ∧ y >= 3`, both factors unbounded above.
fn product_root(terms: &mut TermStore) -> (TermId, TermId, TermId, [TermId; 3]) {
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let twelve = terms.mk_int(BigInt::from(12));
    let three = terms.mk_int(BigInt::from(3));
    let product = terms.mk_eq(xy, twelve);
    let x_big = terms.mk_ge(x, three);
    let y_big = terms.mk_ge(y, three);
    let root = terms.mk_and(vec![product, x_big, y_big]);
    (x, y, root, [product, x_big, y_big])
}

fn solver_with<'a>(terms: &'a TermStore, root: TermId, atoms: &[TermId]) -> NiaSolver<'a> {
    let mut solver = NiaSolver::new(terms);
    solver.set_deadline(ay_core::time::Instant::now() + std::time::Duration::from_secs(10));
    solver.set_root_assertions(vec![root]);
    for &atom in atoms {
        solver.assert_literal(atom, true);
    }
    solver
}

/// The probe finds the 3 x 4 witness, `extract_model` serves it, the flag is
/// spent (a second instance sharing it does not probe again), and the full
/// lane of the probing instance is still available.
#[test]
fn split_probe_claims_a_verified_model_once_per_solve() {
    let mut terms = TermStore::new();
    let (x, y, root, atoms) = product_root(&mut terms);
    let flag = Arc::new(AtomicBool::new(false));

    let mut first = solver_with(&terms, root, &atoms);
    first.set_split_probe_flag(flag.clone());
    assert!(matches!(first.try_split_probe(), Some(TheoryResult::Sat)));
    let model = first
        .extract_model()
        .expect("a claimed probe serves its model");
    let value = |t: TermId| {
        model
            .values
            .get(&t)
            .cloned()
            .expect("every root leaf is valued")
    };
    let (vx, vy) = (value(x), value(y));
    assert_eq!(&vx * &vy, BigInt::from(12));
    assert!(
        vx >= BigInt::from(3) && vy >= BigInt::from(3),
        "x = {vx}, y = {vy}"
    );
    assert!(
        flag.load(Ordering::Relaxed),
        "the probe spends the solve's flag"
    );
    assert!(
        !first.local_search_done,
        "the probe must leave the full lane available"
    );

    let mut second = solver_with(&terms, root, &atoms);
    second.set_split_probe_flag(flag);
    assert!(second.try_split_probe().is_none(), "one probe per solve");
}

/// `x*y = 1 ∧ x >= 1`: the canonical point "every Int leaf 1" satisfies every
/// root, so the probe claims it without a search, and serves it.
#[test]
fn split_probe_claims_the_all_ones_point_when_every_root_holds_there() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let one = terms.mk_int(BigInt::from(1));
    let product = terms.mk_eq(xy, one);
    let x_pos = terms.mk_ge(x, one);
    let mut solver = solver_with(&terms, product, &[product, x_pos]);
    solver.set_root_assertions(vec![product, x_pos]);
    solver.set_split_probe_flag(Arc::new(AtomicBool::new(false)));
    assert!(matches!(solver.try_split_probe(), Some(TheoryResult::Sat)));
    let model = solver
        .extract_model()
        .expect("a claimed probe serves its model");
    assert_eq!(model.values.get(&x), Some(&BigInt::from(1)));
    assert_eq!(model.values.get(&y), Some(&BigInt::from(1)));
}

/// `x*y = 1 ∧ x + y = 3`: the all-ones point satisfies the first root and not
/// the second, the all-zeros point neither, and the problem has no integer
/// model at all — the probe must not claim anything.
#[test]
fn split_probe_never_claims_a_point_one_root_rejects() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let xy = terms.mk_mul(vec![x, y]);
    let one = terms.mk_int(BigInt::from(1));
    let three = terms.mk_int(BigInt::from(3));
    let product = terms.mk_eq(xy, one);
    let sum_t = terms.mk_add(vec![x, y]);
    let sum = terms.mk_eq(sum_t, three);
    let mut solver = solver_with(&terms, product, &[product, sum]);
    solver.set_root_assertions(vec![product, sum]);
    solver.set_deadline(ay_core::time::Instant::now() + std::time::Duration::from_millis(500));
    solver.set_split_probe_flag(Arc::new(AtomicBool::new(false)));
    assert!(solver.try_split_probe().is_none());
}

/// An unsatisfiable root (`x*x = 2`): the probe never claims.
#[test]
fn split_probe_never_claims_an_unsatisfiable_root() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let xx = terms.mk_mul(vec![x, x]);
    let two = terms.mk_int(BigInt::from(2));
    let root = terms.mk_eq(xx, two);
    let mut solver = solver_with(&terms, root, &[root]);
    solver.set_split_probe_flag(Arc::new(AtomicBool::new(false)));
    assert!(solver.try_split_probe().is_none());
}

/// No flag (every caller but the QF_NIA split loop) or no roots: inert, and a
/// root-less instance does not spend the solve's flag.
#[test]
fn split_probe_is_inert_without_a_flag_or_roots() {
    let mut terms = TermStore::new();
    let (_, _, root, atoms) = product_root(&mut terms);
    let mut no_flag = solver_with(&terms, root, &atoms);
    assert!(no_flag.try_split_probe().is_none());

    let flag = Arc::new(AtomicBool::new(false));
    let mut no_roots = NiaSolver::new(&terms);
    no_roots.set_deadline(ay_core::time::Instant::now() + std::time::Duration::from_secs(10));
    for &atom in &atoms {
        no_roots.assert_literal(atom, true);
    }
    no_roots.set_split_probe_flag(flag.clone());
    assert!(no_roots.try_split_probe().is_none());
    assert!(
        !flag.load(Ordering::Relaxed),
        "a root-less instance must not spend the flag"
    );
}
