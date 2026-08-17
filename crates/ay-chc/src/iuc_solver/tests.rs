// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]
use super::*;
use crate::{ChcSort, ChcVar};
use serial_test::parallel;
#[test]
fn test_iuc_solver_sat() {
    let mut solver = IucSolver::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let background = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))];
    let assumptions = vec![ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10))];

    let result = solver.check_sat_with_partitions(&background, &assumptions);

    assert!(result.is_sat(), "expected SAT, got {result:?}");
}

#[test]
fn test_iuc_solver_unsat() {
    let mut solver = IucSolver::new();

    let x = ChcVar::new("x", ChcSort::Int);
    // x >= 10 AND x <= 5 is UNSAT
    let background = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(10))];
    let assumptions = vec![ChcExpr::le(ChcExpr::var(x), ChcExpr::int(5))];

    let result = solver.check_sat_with_partitions(&background, &assumptions);

    assert!(result.is_unsat(), "expected UNSAT, got {result:?}");
}

#[test]
fn test_iuc_solver_proxy_expansion() {
    let mut solver = IucSolver::new();

    let x = ChcVar::new("x", ChcSort::Int);
    // x <= 0 AND x >= 1 is UNSAT
    let background = vec![ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(0))];
    let assumptions = vec![ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(1))];

    let result = solver.check_sat_with_partitions(&background, &assumptions);

    match result {
        IucResult::Unsat {
            core,
            farkas_conflicts,
            ..
        } => {
            // The core should contain the expanded assumption with B partition
            for (expr, partition) in &core {
                safe_eprintln!("Core element: {} (partition: {:?})", expr, partition);
            }

            // Note: Core may be empty if SMT returns UNSAT propositionally
            // (before theory conflicts). In that case, farkas_conflicts
            // should still be populated from the arithmetic theory.
            if core.is_empty() {
                safe_eprintln!("Core is empty - UNSAT detected propositionally");
                safe_eprintln!("Farkas conflicts: {}", farkas_conflicts.len());
                // This is acceptable - proxy expansion worked, just no
                // assumption-level core was returned by the solver.
            } else {
                // If we have a core, at least one element must have B partition
                let has_b = core.iter().any(|(_, p)| *p == Partition::B);
                assert!(
                    has_b,
                    "non-empty core must have B partition elements, got: {core:?}"
                );
            }
        }
        _ => panic!("expected UNSAT, got {result:?}"),
    }
}

#[test]
#[parallel(global_term_memory)]
fn test_iuc_solver_multiple_assumptions() {
    let mut solver = IucSolver::new();

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Background: x >= 0, y >= 0
    let background = vec![
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::ge(ChcExpr::var(y), ChcExpr::int(0)),
    ];

    // Assumptions: x <= -1 (contradicts background)
    let assumptions = vec![ChcExpr::le(ChcExpr::var(x), ChcExpr::int(-1))];

    let result = solver.check_sat_with_partitions(&background, &assumptions);

    assert!(result.is_unsat(), "expected UNSAT, got {result:?}");
}

#[test]
fn test_iuc_solver_empty_background() {
    let mut solver = IucSolver::new();

    let x = ChcVar::new("x", ChcSort::Int);

    // Empty background - only assumptions
    let background: Vec<ChcExpr> = vec![];

    // Contradictory assumptions: x >= 1 AND x <= 0 is UNSAT
    let assumptions = vec![
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ChcExpr::le(ChcExpr::var(x), ChcExpr::int(0)),
    ];

    let result = solver.check_sat_with_partitions(&background, &assumptions);

    // Should be UNSAT with B-partition core elements
    match result {
        IucResult::Unsat { core, .. } => {
            // With empty background, the core (if non-empty) should be all B
            for (_, partition) in &core {
                assert_eq!(
                    *partition,
                    Partition::B,
                    "with empty background, all core elements should be B"
                );
            }
        }
        _ => panic!("expected UNSAT, got {result:?}"),
    }
}

/// Test expand_core correctly skips negated proxy variables.
///
/// Per Z3 semantics (spacer_iuc_solver.cpp:175-186), negated proxies (¬p_i)
/// indicate unused assumptions and should be skipped, not expanded.
/// Fix for #1029.
#[test]
fn test_expand_core_negated_proxy() {
    let mut solver = IucSolver::new();

    // Manually register a proxy
    let original = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(5),
    );
    solver
        .proxies
        .insert("__iuc_proxy_1".to_string(), (original, Partition::B));

    // Create a negated proxy: ¬__iuc_proxy_1
    let negated_proxy = ChcExpr::not(ChcExpr::var(ChcVar::new("__iuc_proxy_1", ChcSort::Bool)));

    // Expand the core containing the negated proxy
    let core = vec![negated_proxy];
    let expanded = solver.expand_core(&core);

    // Per Z3 semantics (spacer_iuc_solver.cpp:175-186): negated proxies indicate
    // unused assumptions and are skipped. Fix for #1029.
    assert_eq!(
        expanded.len(),
        0,
        "negated proxy should be skipped (unused assumption per Z3 semantics)"
    );
}

/// Test expand_core handles both positive and negated proxies in the same core.
///
/// Per Z3 semantics (spacer_iuc_solver.cpp:175-186): negated proxies indicate
/// unused assumptions and are skipped. Fix for #1029.
#[test]
fn test_expand_core_mixed_proxies() {
    let mut solver = IucSolver::new();

    // Register two proxies
    let original1 = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(0),
    );
    let original2 = ChcExpr::le(
        ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
        ChcExpr::int(10),
    );
    solver.proxies.insert(
        "__iuc_proxy_1".to_string(),
        (original1.clone(), Partition::B),
    );
    solver
        .proxies
        .insert("__iuc_proxy_2".to_string(), (original2, Partition::B));

    // Create a core with: positive proxy 1, negated proxy 2, and a non-proxy
    let non_proxy = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("z", ChcSort::Int)),
        ChcExpr::int(0),
    );
    let core = vec![
        ChcExpr::var(ChcVar::new("__iuc_proxy_1", ChcSort::Bool)), // positive
        ChcExpr::not(ChcExpr::var(ChcVar::new("__iuc_proxy_2", ChcSort::Bool))), // negated - skipped
        non_proxy.clone(),                                                       // not a proxy
    ];

    let expanded = solver.expand_core(&core);

    // Negated proxy 2 is skipped (unused assumption), so we get 2 elements:
    // 1. Expanded proxy 1
    // 2. Non-proxy (as-is)
    assert_eq!(
        expanded.len(),
        2,
        "expected 2 expanded elements (negated proxy skipped per Z3 semantics)"
    );

    // First: positive proxy expands to original with B partition
    assert_eq!(expanded[0].0, original1);
    assert_eq!(expanded[0].1, Partition::B);

    // Second: non-proxy stays as-is with AB partition
    assert_eq!(expanded[1].0, non_proxy);
    assert_eq!(expanded[1].1, Partition::AB);
}

mod farkas_retag;

/// Regression test for #2913: var=var equality through IUC proxy path.
///
/// The IUC solver creates proxy variables and implications (proxy → assumption),
/// so the var=var equality `E = C` is nested inside a disjunction:
///   ¬proxy ∨ (E = C)
/// Before the fix (commit 1259af49), `propagate_var_equalities()` substituted
/// one variable for another within individual expressions, causing the theory
/// solver to miss the equality constraint. The model then had E != C.
#[test]
fn test_iuc_solver_preserves_var_var_equality_in_model() {
    let mut solver = IucSolver::new();

    let e = ChcVar::new("E", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);
    let a = ChcVar::new("A", ChcSort::Int);

    // Background: A >= 0
    let background = vec![ChcExpr::ge(ChcExpr::var(a.clone()), ChcExpr::int(0))];

    // Assumptions (become proxy → assumption in IUC):
    //   E = C, A >= 1
    let assumptions = vec![
        ChcExpr::eq(ChcExpr::var(e), ChcExpr::var(c)),
        ChcExpr::ge(ChcExpr::var(a), ChcExpr::int(1)),
    ];

    let result = solver.check_sat_with_partitions(&background, &assumptions);

    match result {
        IucResult::Sat(model) => {
            let e_val = model.get("E");
            let c_val = model.get("C");
            assert!(e_val.is_some(), "IUC model must contain E. Got: {model:?}");
            assert!(c_val.is_some(), "IUC model must contain C. Got: {model:?}");
            assert_eq!(
                e_val, c_val,
                "IUC model violates E = C: E={e_val:?}, C={c_val:?}. Full model: {model:?}"
            );
        }
        other => panic!("Expected Sat (E=C with A>=1 is satisfiable), got {other:?}"),
    }
}
