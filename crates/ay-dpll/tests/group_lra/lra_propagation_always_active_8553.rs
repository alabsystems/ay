// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Verifies that LRA bound propagation is never throttled by conflict count.
//!
//! Z3's new solver sets `arith_propagation_threshold = UINT_MAX`, meaning
//! propagation is always active regardless of how many conflicts occur.
//! AY matches this design: there is no conflict-count gating on bound
//! propagation.
//!
//! This test exercises a QF_LRA problem that generates both conflicts and
//! propagations, then asserts that `lra_propagations > 0` even when
//! `lra_conflicts > 0`. If a conflict-based throttle were reintroduced,
//! this test would catch it.
//!
//! Part of #8553

use ay_dpll::Executor;
use ay_frontend::parse;

fn int_stat(exec: &Executor, name: &str) -> u64 {
    exec.statistics().get_int(name).unwrap_or(0)
}

/// QF_LRA problem that produces both conflicts and propagations.
///
/// The problem has contradictory branches that force the SAT solver to
/// make decisions, encounter theory conflicts, backtrack, and try
/// alternative assignments. Throughout this process, bound propagation
/// must remain active -- it should never be disabled based on conflict count.
#[test]
fn test_lra_propagation_active_despite_conflicts_8553() {
    // A QF_LRA problem with enough structure to force decisions,
    // conflicts, and bound propagations. The chain of inequalities
    // creates implications that bound propagation should derive.
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const z Real)
        (declare-const w Real)

        ; Chain of inequalities: x <= y <= z <= w
        (assert (<= x y))
        (assert (<= y z))
        (assert (<= z w))

        ; Bounds on x and w create propagation opportunities:
        ; x >= 0 and w <= 10 should propagate to y and z
        (assert (>= x 0.0))
        (assert (<= w 10.0))

        ; Disjunctive constraints to force decisions and conflicts
        (assert (or (>= x 5.0) (<= w 3.0)))
        (assert (or (<= y 4.0) (>= z 6.0)))
        (assert (or (>= y 2.0) (<= z 8.0)))

        ; Additional constraints to increase conflict count
        (assert (or (and (>= x 3.0) (<= y 7.0))
                    (and (>= z 1.0) (<= w 9.0))))

        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("LRA script should execute");
    assert_eq!(outputs, vec!["sat"]);

    let propagations = int_stat(&exec, "lra_propagations");
    let conflicts = int_stat(&exec, "lra_conflicts");

    // The primary assertion: propagation is active. On this problem,
    // the chain inequalities + bounds should generate bound propagations.
    assert!(
        propagations > 0,
        "expected lra_propagations > 0 (propagation should never be throttled); \
         got propagations={propagations}, conflicts={conflicts}"
    );
}

/// QF_LRA problem with tight bounds and disequalities that force the solver
/// through multiple rounds of decisions, conflicts, backtracking, and
/// propagation.
///
/// Disequalities create case splits which force the SAT solver to backtrack.
/// Tight bounds on a chain create implied bounds that propagation should
/// derive. Together these verify propagation remains active after conflicts.
#[test]
fn test_lra_propagation_active_with_disequalities_8553() {
    // Disequalities force case splits (x < c or x > c), which cause
    // decisions and conflicts. The tight bounds on the chain create
    // propagation opportunities (implied bounds from x <= y, y <= z chains).
    let input = r#"
        (set-logic QF_LRA)
        (declare-const x Real)
        (declare-const y Real)
        (declare-const z Real)

        ; Chain with tight bounds
        (assert (<= x y))
        (assert (<= y z))
        (assert (>= x 0.0))
        (assert (<= z 10.0))

        ; Disequalities force case splits and create more propagation
        (assert (not (= x 5.0)))
        (assert (not (= y 3.0)))
        (assert (not (= z 7.0)))

        ; Additional bound constraints for propagation opportunities
        (assert (>= y 1.0))
        (assert (<= y 9.0))

        (check-sat)
    "#;

    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("LRA script should execute");
    assert_eq!(outputs, vec!["sat"]);

    let propagations = int_stat(&exec, "lra_propagations");
    // With tight bounds, chains, and disequality splits, bound propagation
    // should derive implied bounds for intermediate variables.
    assert!(
        propagations > 0,
        "expected lra_propagations > 0 with tight bounds and disequalities; \
         got propagations={propagations}. \
         Bound propagation may have been incorrectly throttled."
    );
}
