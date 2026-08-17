// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// The fast-vs-`BigRational` differential contract, at a scale `cargo test`
/// can afford. Every equality that matters is asserted inside
/// [`characterize`]; this pins the shape it actually exercised so a
/// degenerate model (no multipliers, nothing promoted to `BigRational`)
/// cannot make the oracle pass vacuously.
#[test]
fn small_scale_rational_weak_row_matches_big_reference() {
    let shape = SealedScaleShape::SMOKE;
    let report = characterize(shape);

    assert_eq!(
        report.multipliers,
        shape.rows + shape.cols,
        "every row and every structural column should price into the proof"
    );
    assert!(
        report.final_big_slots >= 1,
        "the forced side-store inputs must leave at least one promoted slot"
    );
    // The routine is deterministic in its shape alone, so a second run
    // must reproduce both fingerprints bit for bit.
    let repeat = characterize(shape);
    assert_eq!(report.row_hash, repeat.row_hash);
    assert_eq!(report.combination_hash, repeat.combination_hash);
}

/// The sealed shape is the one the example reports on; a typo that made it
/// unsynthesizable would otherwise only surface on a manual run.
#[test]
fn sealed_shape_is_synthesizable() {
    SealedScaleShape::SEALED.validate();
}
