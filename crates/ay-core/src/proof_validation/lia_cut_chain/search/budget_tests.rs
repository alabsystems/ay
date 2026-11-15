// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The equality elimination is charged against the search's [`MAX_WORK`].

use super::{eliminate, find_chain, Eliminated, MAX_WORK};
use crate::proof_validation::ChainRow;
use crate::{Sort, TermStore};
use num_bigint::BigInt;
use std::collections::BTreeMap;

/// `n` chained unit-pivot equalities `x_i − x_{i+1} + S = 0` sharing the
/// `fillers`-atom sum `S`, and their contradicting sum
/// `x_0 − x_n + n·S = 1`. The rows are refuted by exact elimination alone —
/// no bound, no rounding — so the only thing that can decline them is the
/// elimination's own budget.
fn chained_equalities(n: usize, fillers: usize) -> Vec<ChainRow> {
    let mut terms = TermStore::new();
    let x: Vec<_> = (0..=n)
        .map(|i| terms.mk_var(format!("x{i}"), Sort::Int))
        .collect();
    let y: Vec<_> = (0..fillers)
        .map(|j| terms.mk_var(format!("y{j}"), Sort::Int))
        .collect();
    let row = |form: BTreeMap<_, BigInt>, bound: i64| ChainRow {
        equality: true,
        form,
        bound: BigInt::from(bound),
    };
    let mut rows = Vec::with_capacity(n + 1);
    for i in 0..n {
        let mut form: BTreeMap<_, BigInt> = y.iter().map(|&yj| (yj, BigInt::from(1))).collect();
        form.insert(x[i], BigInt::from(1));
        form.insert(x[i + 1], BigInt::from(-1));
        rows.push(row(form, 0));
    }
    let mut total: BTreeMap<_, BigInt> = y.iter().map(|&yj| (yj, BigInt::from(n))).collect();
    total.insert(x[0], BigInt::from(1));
    total.insert(x[n], BigInt::from(-1));
    rows.push(row(total, 1));
    rows
}

/// 48 chained equalities over `632` fillers cost `48·632 + 2404 = 32740`
/// atom visits to eliminate, inside [`MAX_WORK`] (`32768`), and are refuted
/// with no cut; one more filler costs `32788` and declines, although the rows
/// are exactly as refutable. Before the elimination was charged, `find_chain`
/// certified both and the search's budget was consulted only after the whole
/// elimination had run: 48 dense unit-pivot equalities took 40-44 ms to
/// decline.
#[test]
fn the_elimination_is_charged_against_the_search_budget() {
    let within = chained_equalities(48, 632);
    let mut work = 0;
    assert!(matches!(
        eliminate(&within, &mut work),
        Some(Eliminated::Refuted(_))
    ));
    assert!(work <= MAX_WORK, "work {work}");
    let chain = find_chain(&within).expect("refuted by elimination alone");
    assert!(chain.cuts.is_empty());

    let over = chained_equalities(48, 633);
    let mut work = 0;
    assert!(eliminate(&over, &mut work).is_none());
    assert!(work > MAX_WORK, "work {work}");
    assert!(find_chain(&over).is_none());
}

/// One pivot equality `x + y_0 + … + y_999 = 0` and 94 bounds `x ≥ i`, each
/// holding the pivot: substituting it into all of them is ONE pivot iteration
/// costing `1 + 94·(1000 + 3)` atom visits, almost three times [`MAX_WORK`].
/// The charge is checked before every substitution, so the elimination
/// declines at most one substitution and one row visit past the budget
/// instead of finishing the whole iteration first (checked only once per
/// pivot, it spent all `94283` visits here before declining).
#[test]
fn the_budget_is_checked_before_every_substitution() {
    let (fillers, bounds) = (1000usize, 94i64);
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let mut pivot: BTreeMap<_, BigInt> = (0..fillers)
        .map(|j| (terms.mk_var(format!("y{j}"), Sort::Int), BigInt::from(1)))
        .collect();
    pivot.insert(x, BigInt::from(1));
    let mut rows = vec![ChainRow {
        equality: true,
        form: pivot,
        bound: BigInt::from(0),
    }];
    rows.extend((0..bounds).map(|i| ChainRow {
        equality: false,
        form: BTreeMap::from([(x, BigInt::from(1))]),
        bound: BigInt::from(i),
    }));
    let substitution = fillers + 2;
    let mut work = 0;
    assert!(eliminate(&rows, &mut work).is_none());
    assert!(work > MAX_WORK, "work {work}");
    assert!(work <= MAX_WORK + substitution + 1, "work {work}");
}
