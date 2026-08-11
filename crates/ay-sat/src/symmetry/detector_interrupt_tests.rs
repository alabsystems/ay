// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{Literal, Variable};
use std::cell::Cell;

/// Regression for the FmlaEquivChain timeout hang: the candidate scan must
/// poll at the documented bounded cadence, not only before entering it.
#[test]
fn swap_verification_polls_mid_scan_at_64_clauses() {
    let x0 = Variable(0);
    let x1 = Variable(1);
    let mut clauses = Vec::new();
    for index in 0..65 {
        let z = Variable(index + 2);
        clauses.push(vec![Literal::positive(x0), Literal::positive(z)]);
        clauses.push(vec![Literal::positive(x1), Literal::positive(z)]);
    }
    assert_eq!(clauses.len(), 130);
    let formula_counts = build_formula_counts(&clauses);
    let polls = Cell::new(0usize);

    let result =
        swap_preserves_formula_interruptible(&formula_counts, BinarySwap::ordered(x0, x1), &|| {
            let next = polls.get() + 1;
            polls.set(next);
            next >= 2
        });

    assert_eq!(result, None, "the second in-scan poll must abort");
    assert_eq!(polls.get(), 2, "polls must occur at indices 0 and 64");
}

#[test]
fn detector_discards_verified_swaps_when_later_scan_stops() {
    let z = Variable(3);
    let clauses = (0..3)
        .map(|index| vec![Literal::positive(Variable(index)), Literal::positive(z)])
        .collect::<Vec<_>>();
    let polls = Cell::new(0usize);
    let detector = SymmetryDetector::new(128, 64);

    let result = detector.detect_and_encode_interruptible(&clauses, || {
        let next = polls.get() + 1;
        polls.set(next);
        // Three read-only phase polls, then one complete verified swap; stop
        // as the second candidate's scan begins.
        next >= 5
    });

    assert!(
        result.is_none(),
        "partial detector output must be discarded"
    );
    assert_eq!(polls.get(), 5);
}
