// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `CegarEngine::resolve_equalities` keeps every constraint it cannot turn
//! into an acyclic definition, and substitutes every definition it takes.

use super::*;
use crate::smt::SmtContext;
use ay_core::kani_compat::DetHashSet as FxHashSet;
use std::sync::Arc;

fn bv64(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::BitVec(64))
}

fn lit(value: u128) -> ChcExpr {
    ChcExpr::BitVec(value, 64)
}

fn depth(expr: &ChcExpr) -> usize {
    match expr {
        ChcExpr::Op(_, args) => 1 + args.iter().map(|a| depth(a)).max().unwrap_or(0),
        _ => 0,
    }
}

/// `left` and `right` agree on every assignment (an SMT check of their XOR).
fn equivalent(left: &ChcExpr, right: &ChcExpr) -> bool {
    let differ = ChcExpr::not(ChcExpr::eq(left.clone(), right.clone()));
    SmtContext::new().check_sat(&differ).is_unsat()
}

/// The guard of model-checker-consumer `safe_symbolic_from_elem`'s pointer `add`:
/// `(v * 4) / 4 = v` is a constraint on `v`, not a definition of it. Taking
/// it as `v := (v * 4) / 4` unfolded the definition into itself until a
/// substitution budget gave out (a 250-deep chain) and dropped the guard.
#[test]
fn a_self_referential_equality_stays_a_constraint() {
    let v = bv64("v");
    let guard = ChcExpr::eq(
        ChcExpr::Op(
            ChcOp::BvSDiv,
            vec![
                Arc::new(ChcExpr::Op(
                    ChcOp::BvMul,
                    vec![Arc::new(ChcExpr::var(v.clone())), Arc::new(lit(4))],
                )),
                Arc::new(lit(4)),
            ],
        ),
        ChcExpr::var(v.clone()),
    );
    // Below 2^62 the guard still excludes v in [2^61, 2^62), where v * 4
    // overflows the signed range.
    let bound = ChcExpr::Op(
        ChcOp::BvULt,
        vec![Arc::new(ChcExpr::var(v)), Arc::new(lit(1 << 62))],
    );
    let resolved =
        CegarEngine::resolve_equalities(&[guard.clone(), bound.clone()], &FxHashSet::default());
    assert!(
        resolved.iter().all(|part| depth(part) <= depth(&guard)),
        "no part grows past the guard it came from: {resolved:?}"
    );
    assert!(
        equivalent(
            &ChcExpr::and_all(resolved.clone()),
            &ChcExpr::and(guard, bound)
        ),
        "the resolved parts are the original constraints: {resolved:?}"
    );
}

/// A cycle through several definitions (`v := w + 1`, `w := x + 1`,
/// `x := v - 2`) is caught on the edge that would close it; the one-step
/// occurs check of a single map application cannot see it.
#[test]
fn a_definition_that_closes_a_cycle_stays_a_constraint() {
    let (v, w, x) = (bv64("v"), bv64("w"), bv64("x"));
    let add = |var: &ChcVar, k: u128| {
        ChcExpr::Op(
            ChcOp::BvAdd,
            vec![Arc::new(ChcExpr::var(var.clone())), Arc::new(lit(k))],
        )
    };
    let parts = vec![
        ChcExpr::eq(ChcExpr::var(v.clone()), add(&w, 1)),
        ChcExpr::eq(ChcExpr::var(w.clone()), add(&x, 1)),
        ChcExpr::eq(ChcExpr::var(x.clone()), add(&v, u128::from(u64::MAX) - 1)),
    ];
    let resolved = CegarEngine::resolve_equalities(&parts, &FxHashSet::default());
    assert!(
        resolved.iter().all(|part| depth(part) <= 8),
        "no unfolded cycle: {resolved:?}"
    );
    assert_ne!(
        resolved,
        vec![ChcExpr::Bool(true)],
        "the cycle's last equality is kept, not dropped"
    );
}

/// A BitVec definition with a composite value is substituted into the parts
/// that remain. Its substitution pair was keyed on `Int`, so the remaining
/// `v` (a BitVec variable) was never replaced while `v = w + 1` itself had
/// been consumed: the parts below came back as `v <u 2` alone, satisfiable,
/// where the input is unsatisfiable.
#[test]
fn a_bitvec_definition_is_substituted_into_the_remaining_parts() {
    let (v, w) = (bv64("v"), bv64("w"));
    let shared: FxHashSet<String> = ["w".to_string()].into_iter().collect();
    let parts = vec![
        ChcExpr::eq(
            ChcExpr::var(v.clone()),
            ChcExpr::Op(
                ChcOp::BvAdd,
                vec![Arc::new(ChcExpr::var(w.clone())), Arc::new(lit(1))],
            ),
        ),
        ChcExpr::Op(
            ChcOp::BvULt,
            vec![Arc::new(ChcExpr::var(v)), Arc::new(lit(2))],
        ),
        ChcExpr::eq(ChcExpr::var(w), lit(7)),
    ];
    let resolved = CegarEngine::resolve_equalities(&parts, &shared);
    assert!(
        SmtContext::new()
            .check_sat(&ChcExpr::and_all(resolved.clone()))
            .is_unsat(),
        "w = 7 makes v = 8, so v <u 2 is false: {resolved:?}"
    );
}
