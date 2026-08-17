// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// SCOUT GUARD: when nothing output-visible can move, the sweeps are
/// skipped and the output box is BYTE-IDENTICAL to the input — which is
/// also exactly what the full lane would have shipped (its continuous
/// refinements are discarded, its integral candidates are immaterial).
#[test]
fn scout_skip_ships_the_input_box_when_nothing_visible_moves() {
    let mut m = Model::new();
    let z = m.add_int_col(0.0, 1.0);
    let x = m.add_col(0.0, 10.0);
    // x <= 8: a real workspace tightening, invisible at output.
    m.add_row(f64::NEG_INFINITY, 8.0, &[(x, 1.0)]);
    // z + x <= 50: slack — z's derived cap (50 - 0 = 50, floor 42-ish
    // territory) never beats its existing ub 1.
    m.add_row(f64::NEG_INFINITY, 50.0, &[(z, 1.0), (x, 1.0)]);
    m.set_objective(&[(z, 1.0)], Sense::Maximize);
    let Presolved::Tightened(out) = tighten_bounds(&m, None) else {
        panic!("the model is feasible");
    };
    assert_eq!(out.col_bounds(z), (0.0, 1.0));
    assert_eq!(out.col_bounds(x), (0.0, 10.0));
}
