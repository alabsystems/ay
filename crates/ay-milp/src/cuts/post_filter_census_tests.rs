// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Post-filter efficacy-floor census regressions.

use super::*;

/// One `<=` cut over columns `0..n` at the point `x = (1, 1, ..., 1)`, with a chosen
/// violation. Activity is `Σ a_j`, so `ub = Σ a_j − v` makes the violation exactly `v`.
fn cut_with(coeffs: &[f64], v: f64) -> (Cut, Vec<f64>) {
    let act: f64 = coeffs.iter().sum();
    let cut = Cut {
        coeffs: coeffs
            .iter()
            .enumerate()
            .map(|(j, &a)| (Col(j as u32), a))
            .collect(),
        lb: f64::NEG_INFINITY,
        ub: act - v,
    };
    (cut, vec![1.0; coeffs.len()])
}

/// THE CENSUS MUST SEPARATE SCALE FROM DEPTH, because that separation is the whole
/// finding it reports.
///
/// [`MIN_VIOLATION`] tests raw [`violation`], which is scale-DEPENDENT — multiply a cut
/// through by ten and it multiplies by ten while the inequality says the same thing.
/// The root pool never spends that currency: it ranks and floors on scale-free
/// [`cut_depth`]. So a count of refusals is a fire rate and orders nothing
/// (`1c1ce672c`: four families at fire rate zero, four different verdicts), and the
/// number the census exists to produce is how many refused cuts would ALSO have
/// cleared the pool's own floor. Two cuts with the SAME violation and different
/// coefficient scales must therefore be charged differently — if this test ever passes
/// with the depth term removed, the census is back to reporting a fire rate and the
/// 163-refusals/3-deep measurement in [`MIN_VIOLATION`]'s comment is void.
///
/// # The instrument is THIS THREAD's charges, not the process's
///
/// This test used to read [`crate::sepstat::gate_read`] — the process-global
/// counters — before and after each call. That is not a measurement of what
/// this test charged; it is a measurement of what the whole binary charged in
/// that interval, and libtest is running ~1142 other tests on other threads
/// while it runs. Twelve separation call sites reach
/// [`clears_min_violation`], so any sibling test that solves a model charges
/// the same gate.
///
/// MEASURED on a clean `main`, with no other change in the tree: 15 runs of
/// this test alongside `bab::tests::`/`cuts::`/`session::tests::` produced one
/// failure —
///
/// ```text
/// assertion `left == right` failed: a refused cut whose DEPTH clears the
/// pool's floor is the forgone capability
///   left: (2, 1)
///  right: (1, 1)
/// ```
///
/// — a hits delta of 2 for one call, i.e. a sibling's refusal landing inside
/// the window. The `crate::sepstat::adoption_test_guard` this test used to take
/// never covered that: it serialises only the tests that TAKE it, and the other
/// six are all about `ADOPTION_EXCLUDED`, a different counter. With the
/// instrument now per-thread the guard has nothing left to do, so it is gone
/// rather than left standing as a defence that never was one.
///
/// The failure direction that got noticed is the false FAIL. The dangerous one
/// is the other: a sibling charge is indistinguishable from this test's own, so
/// it can also SUPPLY a delta this test is checking for — which would let a
/// mutation that stopped charging pass. Reading
/// [`crate::sepstat::gate_read_local`] removes both: it is the same number with
/// the other threads' charges excluded, and every assertion below is unchanged.
#[test]
fn the_efficacy_floor_census_charges_depth_not_violation() {
    let site = crate::sepstat::GATE_CUT_MIN_VIOLATION;

    // Same violation (5e-5, an order under the floor) in both, differing only by the
    // scale of the coefficients — so `violation` cannot tell them apart and `depth` can.
    let (deep, x_deep) = cut_with(&[0.01], 5e-5); // depth 5e-3, above the pool's 1e-3
    let (flat, x_flat) = cut_with(&[1.0], 5e-5); // depth 5e-5, below it

    let before = crate::sepstat::gate_read_local(site);
    assert!(
        !clears_min_violation(&deep, &x_deep),
        "5e-5 is under the floor"
    );
    let after_deep = crate::sepstat::gate_read_local(site);
    assert_eq!(
        (after_deep.0 - before.0, after_deep.1 - before.1),
        (1, 1),
        "a refused cut whose DEPTH clears the pool's floor is the forgone capability"
    );

    assert!(
        !clears_min_violation(&flat, &x_flat),
        "5e-5 is under the floor"
    );
    let after_flat = crate::sepstat::gate_read_local(site);
    assert_eq!(
        (after_flat.0 - after_deep.0, after_flat.1 - after_deep.1),
        (1, 0),
        "the same violation at a hundred times the scale is shallow, and cost NOTHING"
    );

    // A SATISFIED cut is not a refusal at all: there was no capability to forgo, so it
    // must not even register as a hit. Without this the denominator is wrong and the
    // "3 of 163" ratio is meaningless.
    let (sat, x_sat) = cut_with(&[1.0], -1.0);
    assert!(!clears_min_violation(&sat, &x_sat));
    let after_sat = crate::sepstat::gate_read_local(site);
    assert_eq!(
        after_sat, after_flat,
        "a satisfied cut cost the search nothing and must not be charged"
    );
}

/// Charging must not have MOVED the filter. Every measurement in this crate taken
/// through the old bare `violation(&cut, x) > MIN_VIOLATION` spelling keeps its meaning
/// only while the helper decides exactly what that expression decided — including at the
/// boundary, where `>` and `>=` differ and a cut violated by precisely `1e-4` is REFUSED.
#[test]
fn the_census_helper_decides_exactly_what_the_bare_comparison_did() {
    let mut seed = 0x00C6_F117_u64;
    let rnd = |s: &mut u64| {
        *s = s.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        ((*s >> 33) as f64 / (1u64 << 31) as f64) - 0.5
    };
    let mut refused = 0usize;
    for _ in 0..2_000 {
        let n = 1 + (seed as usize % 4);
        let coeffs: Vec<f64> = (0..n).map(|_| rnd(&mut seed) * 10.0).collect();
        // Violations straddling the floor by orders of magnitude in both directions.
        let v = rnd(&mut seed) * 4.0 * MIN_VIOLATION;
        let (cut, x) = cut_with(&coeffs, v);
        let bare = violation(&cut, &x) > MIN_VIOLATION;
        assert_eq!(clears_min_violation(&cut, &x), bare);
        refused += usize::from(!bare);
    }
    // THE EXACT BOUNDARY, and it has to be built rather than asked for. `cut_with(&[1.0],
    // MIN_VIOLATION)` does NOT produce a cut violated by 1e-4: `1.0 - 1e-4` is not exact in
    // f64 and the difference comes back 9.999999999998899e-5, a hair UNDER the floor, so the
    // assertion would pass under `>` and `>=` alike and prove nothing. (Measured: it did —
    // the first version of this test failed to catch a deliberate `>` -> `>=` sabotage.)
    // Putting the floor in the COEFFICIENT and zero in the right-hand side makes the
    // subtraction exact, so this is the one input on which the two operators disagree.
    let edge = Cut {
        coeffs: vec![(Col(0), MIN_VIOLATION)],
        lb: f64::NEG_INFINITY,
        ub: 0.0,
    };
    let x_edge = vec![1.0];
    assert_eq!(
        violation(&edge, &x_edge),
        MIN_VIOLATION,
        "the boundary case must be EXACT or it tests nothing"
    );
    assert!(
        !clears_min_violation(&edge, &x_edge),
        "the floor is strict: a cut violated by exactly MIN_VIOLATION is refused"
    );
    assert!(
        refused > 200,
        "anti-vacuity: the sample must actually exercise the refusal branch, got {refused}"
    );
}
