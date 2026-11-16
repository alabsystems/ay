// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::fallback::is_valid_interpolant;
use super::super::proof_backed::interpolating_sat_constraints_with_proof_provenance;
use super::super::InterpolatingSatResult;
use super::*;
use crate::ChcVar;
use std::time::Duration;

fn rvar(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Real))
}

fn real(n: i64) -> ChcExpr {
    ChcExpr::Real(n, 1)
}

fn shared(names: &[&str]) -> FxHashSet<String> {
    names.iter().map(|s| (*s).to_string()).collect()
}

/// `round' = round + 1` guarded transition, unrolled from `round = 0`:
/// `A = init@0 ∧ T@0`, `B = T@1 ∧ T@2 ∧ bad@3` with `bad = round ≥ 3 ∧ y ≠ 0`.
/// `y` is only ever copied, so every unrolling is refuted once the round
/// counter is propagated through the cut.
fn round_system() -> (Vec<ChcExpr>, Vec<ChcExpr>, FxHashSet<String>) {
    let step = |i: usize| {
        let (r, r1, y, y1) = (
            rvar(&format!("r{i}")),
            rvar(&format!("r{}", i + 1)),
            rvar(&format!("y{i}")),
            rvar(&format!("y{}", i + 1)),
        );
        ChcExpr::or_all((0..3).map(|c| {
            ChcExpr::and_all([
                ChcExpr::eq(r.clone(), real(c)),
                ChcExpr::eq(r1.clone(), real(c + 1)),
                ChcExpr::eq(y1.clone(), y.clone()),
            ])
        }))
    };
    let a = vec![
        ChcExpr::eq(rvar("r0"), real(0)),
        ChcExpr::eq(rvar("y0"), real(0)),
        step(0),
    ];
    let b = vec![
        step(1),
        step(2),
        ChcExpr::ge(rvar("r3"), real(3)),
        ChcExpr::not(ChcExpr::eq(rvar("y3"), real(0))),
    ];
    (a, b, shared(&["r1", "y1"]))
}

#[test]
fn deterministic_prefix_refutes_b_by_units_alone() {
    let (a, b, s) = round_system();
    match simplify_partition(&a, &b, &s, false) {
        Some(Transfer::Units(units)) => {
            let itp = conjoin(&units);
            assert!(is_valid_interpolant(&a, &b, &itp, &s), "{itp}");
        }
        other => panic!("expected a units-only refutation, got {other:?}"),
    }
}

#[test]
fn split_keeps_a_general_part_and_moves_the_units() {
    // A: x0 = 0 ∧ x1 = x0 + 1 ∧ y1 ≥ x0        (shared x1, y1)
    // B: y1 < x1 - 5
    let a = vec![
        ChcExpr::eq(rvar("x0"), real(0)),
        ChcExpr::eq(rvar("x1"), ChcExpr::add(rvar("x0"), real(1))),
        ChcExpr::ge(rvar("y1"), rvar("x0")),
    ];
    let b = vec![ChcExpr::lt(rvar("y1"), ChcExpr::sub(rvar("x1"), real(5)))];
    let s = shared(&["x1", "y1"]);
    match simplify_partition(&a, &b, &s, false) {
        Some(Transfer::Split {
            a: a2,
            b: b2,
            units,
        }) => {
            assert_ne!(units, [] as [ChcExpr; 0]);
            for part in a2.iter().chain(b2.iter()) {
                assert!(
                    part.vars().iter().all(|v| s.contains(&v.name)),
                    "locals must be eliminated: {part}"
                );
            }
        }
        other => panic!("expected a split, got {other:?}"),
    }
}

#[test]
fn proof_path_serves_a_valid_interpolant_through_the_transfer() {
    // A fixes the round but only bounds y (y0 ≥ 5); B needs y3 < 3. The
    // units decide B's disjunctions; the arithmetic is left to the proof.
    let (mut a, mut b, s) = round_system();
    a[1] = ChcExpr::ge(rvar("y0"), real(5));
    b[3] = ChcExpr::lt(rvar("y3"), real(3));
    match simplify_partition(&a, &b, &s, false) {
        Some(Transfer::Split { .. }) => {}
        other => panic!("expected a split, got {other:?}"),
    }
    match interpolating_sat_constraints_with_proof_provenance(
        &a,
        &b,
        &s,
        Some(Duration::from_secs(10)),
        Some(Duration::from_secs(10)),
    ) {
        (InterpolatingSatResult::Unsat(itp), _) => {
            assert!(is_valid_interpolant(&a, &b, &itp, &s), "{itp}");
        }
        (InterpolatingSatResult::Unknown, _) => panic!("must interpolate"),
    }
}

#[test]
fn nothing_to_transfer_is_none() {
    let a = vec![ChcExpr::le(rvar("x"), real(1))];
    let b = vec![ChcExpr::ge(rvar("x"), real(2))];
    assert!(simplify_partition(&a, &b, &shared(&["x"]), false).is_none());
}

#[test]
fn facts_mode_moves_shared_relations() {
    // A local-free relation between shared variables is moved, not only
    // equalities: z0 = 1 ∧ x1 <= y1 + z0 (shared x1, y1) gives x1 <= y1 + 1,
    // which the units-only mode leaves behind.
    let a = vec![
        ChcExpr::eq(rvar("z0"), real(1)),
        ChcExpr::le(rvar("x1"), ChcExpr::add(rvar("y1"), rvar("z0"))),
    ];
    let b = vec![ChcExpr::gt(rvar("x1"), ChcExpr::add(rvar("y1"), real(3)))];
    let s = shared(&["x1", "y1"]);
    match simplify_partition(&a, &b, &s, true) {
        Some(Transfer::Units(units)) | Some(Transfer::Split { units, .. }) => {
            assert!(!units.is_empty(), "the shared relation must be moved");
        }
        None => panic!("expected a transfer"),
    }
    match simplify_partition(&a, &b, &s, false) {
        Some(Transfer::Split { units, .. }) => assert!(units.is_empty(), "{units:?}"),
        other => panic!("expected a split without units, got {other:?}"),
    }
}
