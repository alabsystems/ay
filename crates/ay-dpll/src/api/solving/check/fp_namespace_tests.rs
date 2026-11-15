// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::api::{Logic, Solver, Term};
use crate::{UnknownOrigin, UnknownReason};

fn pending_after_pop(named: bool) -> (Solver, Term) {
    let mut solver = Solver::new(Logic::All);
    let assertion = if named {
        "(set-option :produce-unsat-cores true) (assert (! b :named named_b))"
    } else {
        "(assert b)"
    };
    let roots = solver
        .parse_smtlib2(&format!("(declare-const b Bool) {assertion}"))
        .unwrap();
    assert_eq!(roots.len(), 1);
    let root = roots[0];
    assert!(solver.check_sat().is_sat());
    assert!(solver.model().is_some());
    solver.push();
    solver
        .parse_smtlib2("(declare-const x (_ FloatingPoint 5 11)) (assert (fp.isZero x))")
        .unwrap();
    // Exercise the real push handler while keeping this boundary test small.
    solver
        .executor
        .incr_fp_state
        .as_mut()
        .unwrap()
        .fp_cache
        .next_var = u32::MAX;
    solver.push();
    solver.pop();
    solver.pop();
    assert_eq!(solver.num_scopes(), 0);
    assert_eq!(solver.assertions(), [root]);
    assert!(solver
        .executor
        .incr_fp_state
        .as_ref()
        .unwrap()
        .persistent_sat
        .is_none());
    (solver, root)
}

fn revoked(solver: &mut Solver) {
    assert_eq!(solver.unknown_reason(), Some(UnknownReason::ResourceLimit));
    assert_eq!(
        solver.executor.unknown_origin(),
        Some(UnknownOrigin::DeterministicResourceBudget)
    );
    assert!(solver.executor.last_result_is_unknown());
    assert!(solver.model().is_none());
    assert!(!solver.executor.was_model_validated());
    assert!(solver.executor.last_proof().is_none());
    assert!(solver.executor.take_sat_certificate().is_none());
    assert!(solver.executor.take_unsat_certificate().is_none());
}

#[test]
fn native_plain_and_interruptible_checks_consume_pending_namespace_failure_before_routing() {
    for interruptible in [false, true] {
        let (mut solver, root) = pending_after_pop(false);
        // A semantic opt-out is distinct from the already recorded resource
        // failure; neither it nor the now Boolean-only query may hide failure.
        solver
            .executor
            .incr_fp_state
            .as_mut()
            .unwrap()
            .disable_and_teardown();
        let rejected = if interruptible {
            solver.check_sat_interruptible(|| false)
        } else {
            solver.check_sat()
        };
        assert!(rejected.is_unknown());
        revoked(&mut solver);
        assert_eq!(solver.assertions(), [root]);
        let fresh = if interruptible {
            solver.check_sat_interruptible(|| false)
        } else {
            solver.check_sat()
        };
        assert!(fresh.is_sat());
        assert!(solver.model().is_some());
        assert!(solver.unknown_reason().is_none());
        assert_eq!(solver.assertions(), [root]);
    }
}

#[test]
fn native_named_assumption_check_preserves_resource_origin_and_fresh_authority() {
    let (mut solver, root) = pending_after_pop(true);
    assert_eq!(solver.executor.ctx.named_terms_iter().count(), 1);
    assert!(solver.check_sat_assuming(&[root]).is_unknown());
    revoked(&mut solver);
    assert_eq!(solver.assertions(), [root]);
    assert!(solver.check_sat_assuming(&[root]).is_sat());
    assert!(solver.model().is_some());
    assert_eq!(solver.assertions(), [root]);
    assert!(solver.unknown_reason().is_none());
}
