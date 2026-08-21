// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by ic3::tests to preserve the test FQN.

/// Regression test: PriorityObligation ordering (lower level = higher priority).
#[test]
fn test_obligation_ordering() {
    use super::cube::{Cube, Ic3Obligation, PriorityObligation};
    use std::collections::BinaryHeap;

    let v0 = Variable::new(0);
    let cube = Cube::new(vec![Literal::positive(v0)]);

    let mut heap = BinaryHeap::new();
    heap.push(PriorityObligation(Ic3Obligation::new(
        cube.clone(),
        3,
        0,
        0,
        None,
    )));
    heap.push(PriorityObligation(Ic3Obligation::new(
        cube.clone(),
        1,
        0,
        1,
        None,
    )));
    heap.push(PriorityObligation(Ic3Obligation::new(cube, 2, 0, 2, None)));

    // Should pop in order: level 1, 2, 3.
    assert_eq!(heap.pop().expect("non-empty").0.level, 1);
    assert_eq!(heap.pop().expect("non-empty").0.level, 2);
    assert_eq!(heap.pop().expect("non-empty").0.level, 3);
}
