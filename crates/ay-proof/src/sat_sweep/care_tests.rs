// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sweeping under the roots' hypotheses, on a circuit small enough to read.

use super::*;

/// `c ∧ a` and `c ∧ b` agree exactly where the hypothesis `a ∧ b` holds.
/// The root asserts the hypothesis and their disagreement.
///
/// Variables: inputs `a b c` (0..3), `h = a ∧ b` (3), `g1 = c ∧ a` (4),
/// `g2 = c ∧ b` (5), `m = g1 ⊕ g2` (6), `root = h ∧ m` (7).
fn guarded_miter() -> (Vec<Gate>, Vec<Vec<Literal>>, usize) {
    let pos = |var: usize| literal(var, false);
    let neg = |var: usize| literal(var, true);
    let and = |out: usize, x: usize, y: usize| {
        vec![
            vec![neg(out), pos(x)],
            vec![neg(out), pos(y)],
            vec![pos(out), neg(x), neg(y)],
        ]
    };
    let mut cnf = Vec::new();
    cnf.extend(and(3, 0, 1));
    cnf.extend(and(4, 2, 0));
    cnf.extend(and(5, 2, 1));
    cnf.extend([
        vec![neg(6), pos(4), pos(5)],
        vec![neg(6), neg(4), neg(5)],
        vec![pos(6), neg(4), pos(5)],
        vec![pos(6), pos(4), neg(5)],
    ]);
    cnf.extend(and(7, 3, 6));
    cnf.push(vec![pos(7)]);
    let root = cnf.len() - 1;
    let gates = vec![
        Gate::Input,
        Gate::Input,
        Gate::Input,
        Gate::And(vec![pos(0), pos(1)]),
        Gate::And(vec![pos(2), pos(0)]),
        Gate::And(vec![pos(2), pos(1)]),
        Gate::Xor(vec![pos(4), pos(5)]),
        Gate::And(vec![pos(3), pos(6)]),
    ];
    (gates, cnf, root)
}

fn limits() -> SweepLimits {
    SweepLimits {
        lemma_conflicts: 100,
        total_conflicts: 10_000,
        total_work: u64::MAX,
        deadline: Instant::now() + Duration::from_secs(60),
    }
}

/// The hypothesis is taken (the disagreement, which no pattern satisfying it
/// shows, is not), both gates merge with `c` under it, and the refutation
/// replays. Swept without it, neither merges: they differ where `a != b`.
#[test]
fn gates_equal_only_under_the_hypothesis_are_merged_under_it() {
    let (gates, cnf, root) = guarded_miter();
    let mut keep_going = || true;
    let mut sweep = Sweep::new(gates, &cnf, &[root], false, limits(), &mut keep_going).unwrap();
    let care = sweep
        .care
        .as_ref()
        .expect("the sweep is under the hypothesis");
    assert_eq!(
        care.units.iter().map(|(unit, _)| *unit).collect::<Vec<_>>(),
        vec![literal(3, false)]
    );
    sweep.sweep();
    assert!(matches!(sweep.merged[4], Some(Merge::Equiv(..))));
    assert!(matches!(sweep.merged[5], Some(Merge::Equiv(..))));
    let Direct::Refuted(dag) = sweep.close_direct() else {
        panic!("a refutation");
    };
    dag.validate().expect("the refutation replays");
}
