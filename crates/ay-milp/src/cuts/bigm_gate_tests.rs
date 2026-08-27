// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by `cuts::bigm_gate_tests`; keeping the module in `cuts.rs` preserves test FQNs.

use super::*;

/// Build one indicator neuron: pre-activation x in [l, u] (free column), output
/// y in [0, u], switch z binary, rows `y − u·z <= 0` and `−x + y + |l|·z <= |l|`.
fn add_neuron(m: &mut Model, l: f64, u: f64) -> (Col, Col, Col) {
    let x = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    let y = m.add_col(0.0, u);
    let z = m.add_binary_col();
    m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (z, -u)]);
    m.add_row(f64::NEG_INFINITY, -l, &[(x, -1.0), (y, 1.0), (z, -l)]);
    (x, y, z)
}

#[test]
fn bigm_gate_fires_on_the_indicator_shape_and_not_on_fixed_charge() {
    // The safenlp shape in miniature: BIGM_MIN_PAIRS paired ReLU neurons.
    let mut m = Model::new();
    for _ in 0..BIGM_MIN_PAIRS {
        add_neuron(&mut m, -0.5, 0.75);
    }
    assert!(
        is_bigm_indicator(&m),
        "paired big-M indicator rows must fire the gate"
    );

    // Fixed-charge shape (rout/khb05250): VUB rows exist, but no wider row ever
    // names the switch binary — the capacity row is over the flows alone.
    let mut fc = Model::new();
    let mut flows = Vec::new();
    for _ in 0..BIGM_MIN_PAIRS {
        let x = fc.add_col(0.0, f64::INFINITY);
        let z = fc.add_binary_col();
        fc.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0), (z, -40.0)]);
        flows.push(x);
    }
    let cap: Vec<(Col, f64)> = flows.iter().map(|&x| (x, 1.0)).collect();
    fc.add_row(f64::NEG_INFINITY, 100.0, &cap);
    assert!(
        !is_bigm_indicator(&fc),
        "a fixed-charge network (no row naming both y and z) must NOT fire"
    );

    // Below the pair floor: never fires, however clean the pairs.
    let mut tiny = Model::new();
    for _ in 0..(BIGM_MIN_PAIRS - 1) {
        add_neuron(&mut tiny, -0.5, 0.75);
    }
    assert!(!is_bigm_indicator(&tiny), "under the pair floor: inert");
}

/// A dense aggregate is not every indicator's big-M row (`gen`/`rout` regression).
/// The old pair confirmation accepted one 582-term row for all 432 `gen` pairs,
/// adding 30% wall time on an identical tree. Restoring that loop fails this
/// test while the positive/ordinary fixed-charge test above still passes.
#[test]
fn a_dense_aggregate_row_confirms_no_bigm_pair() {
    let mut m = Model::new();
    let mut wide: Vec<(Col, f64)> = Vec::new();
    for _ in 0..(BIGM_MIN_PAIRS + 4) {
        let y = m.add_col(0.0, 10.0);
        let z = m.add_binary_col();
        m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (z, -10.0)]);
        wide.push((y, 1.0));
        wide.push((z, 3.0));
    }
    // The aggregate: one row over every pair, exactly `gen`'s wide row in miniature.
    m.add_row(f64::NEG_INFINITY, 50.0, &wide);
    assert!(
        !is_bigm_indicator(&m),
        "one row naming every pair is an aggregate, not each indicator's big-M row"
    );

    // A genuine per-indicator model remains admitted even with an extra aggregate.
    let mut paired = Model::new();
    for _ in 0..BIGM_MIN_PAIRS {
        add_neuron(&mut paired, -0.5, 0.75);
    }
    let all: Vec<(Col, f64)> = (0..paired.num_cols())
        .map(|j| (Col(j as u32), 1.0))
        .collect();
    paired.add_row(f64::NEG_INFINITY, 1000.0, &all);
    assert!(
        is_bigm_indicator(&paired),
        "an extra aggregate row must not DISQUALIFY genuine per-indicator big-M rows"
    );
}
