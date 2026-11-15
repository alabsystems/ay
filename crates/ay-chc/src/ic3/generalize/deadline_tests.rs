// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::ic3::transition_system::BitLevelTransitionSystem;
use ay_core::time::Instant;
use ay_sat::Variable;
use std::time::Duration;

fn fixture() -> Ic3Solver {
    let x = Variable::new(0);
    let next = Variable::new(1);
    Ic3Solver::new(
        BitLevelTransitionSystem::new(
            1,
            0,
            vec![x],
            vec![next],
            vec![],
            vec![vec![Literal::negative(x)]],
            vec![vec![Literal::negative(next)]],
            vec![Literal::positive(x)],
            2,
        ),
        false,
    )
}

#[test]
fn independent_checker_keeps_real_consecution_and_countermodel_controls() {
    let solver = fixture().with_deadline(Some(Instant::now() + Duration::from_secs(60)));
    let blocked = Cube::new(vec![Literal::positive(Variable::new(0))]);
    let reachable = Cube::new(vec![Literal::negative(Variable::new(0))]);
    assert!(solver.verify_consecution_independent(&blocked, 0));
    assert!(!solver.verify_consecution_independent(&reachable, 0));
    assert!(!solver.resource_exhausted());
}

#[test]
fn expired_independent_check_cannot_confirm_consecution_or_retry() {
    let solver = fixture().with_deadline(Some(Instant::now()));
    let blocked = Cube::new(vec![Literal::positive(Variable::new(0))]);
    assert!(!solver.verify_consecution_independent(&blocked, 0));
    assert!(solver.resource_exhausted());
    // Changing the original deadline does not revive a failed IC3 attempt.
    let solver = solver.with_deadline(Some(Instant::now() + Duration::from_secs(60)));
    assert!(!solver.verify_consecution_independent(&blocked, 0));
    assert!(fixture().verify_consecution_independent(&blocked, 0));
}
