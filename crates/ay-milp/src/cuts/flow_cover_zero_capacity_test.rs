// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Included by `cuts::flow_cover_tests`; keeping the module in `cuts.rs` preserves the test FQN.

/// A shift may not manufacture capacity on a conservation row (the blend2 pin).
/// With zero RHS, every switch payment vanishes. The prior widening instead
/// derived capacity from a column offset: five blend2 cuts grew its tree from
/// 3,882 to 9,070 nodes. This fixture pins zero- and real-capacity directions.
#[test]
fn a_shift_may_not_manufacture_capacity_on_a_conservation_row() {
    // Three VUB'd in-arcs and blend2's far-from-origin carrier, scaled down.
    const CAP: f64 = 60.0;
    const OFF: f64 = 100.0;
    let build = |rhs: f64| {
        let mut m = Model::new();
        let flow: Vec<Col> = (0..3).map(|_| m.add_col(0.0, CAP)).collect();
        let sw: Vec<Col> = (0..3).map(|_| m.add_binary_col()).collect();
        for k in 0..3 {
            m.add_row(f64::NEG_INFINITY, 0.0, &[(flow[k], 1.0), (sw[k], -CAP)]);
        }
        let far = m.add_col(OFF, OFF + 10.0);
        let mut row: Vec<(Col, f64)> = flow.iter().map(|&c| (c, 1.0)).collect();
        row.push((far, -1.0));
        m.add_row(f64::NEG_INFINITY, rhs, &row);
        m.set_objective(&[(flow[0], 1.0)], Sense::Minimize);
        // Every arc is a third open and the far column rests at its lower bound,
        // so `Σ flow − far = 0` satisfies either row before separation.
        let each = OFF / 3.0;
        let mut x = vec![0.0; m.num_cols()];
        for k in 0..3 {
            x[flow[k].index()] = each;
            x[sw[k].index()] = each / CAP;
        }
        x[far.index()] = OFF;
        (m, x)
    };

    let (m0, x0) = build(0.0);
    let cuts0 = separate_flow_cover(&m0, &x0, m0.num_rows());
    assert!(
        cuts0.is_empty(),
        "a shift manufactured capacity on a conservation row: {} cut(s), \
         the blend2 carrier (3,882 -> 9,070 nodes)",
        cuts0.len()
    );

    let (m5, x5) = build(5.0);
    let cuts5 = separate_flow_cover(&m5, &x5, m5.num_rows());
    assert!(
        !cuts5.is_empty(),
        "the zero-capacity guard also killed widening on a row with a real RHS"
    );
}
