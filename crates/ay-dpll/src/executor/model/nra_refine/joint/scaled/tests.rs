// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::tests::{ratio, rational_of, run_script, sqrt_value};
use super::*;
use ay_core::Sort;
use ay_nra::RealAlgebraicValue;
use num_traits::One;

// ---------------- pure scaled-coordinate helpers ----------------

#[test]
fn unscale_puts_the_scale_factor_on_the_named_member() {
    let (z, w) = (ratio(17, 13), ratio(7, 13));
    assert_eq!(
        Scale::Alpha.unscale(&z, &w),
        (ratio(119, 169), ratio(7, 13))
    );
    assert_eq!(
        Scale::Partner.unscale(&z, &w),
        (ratio(7, 13), ratio(119, 169))
    );
}

#[test]
fn partner_scaling_needs_a_sign_constant_interval_and_a_nonzero_partner() {
    let b = ratio(4, 5);
    // Straddles 0, or touches it: `b/α` is not enclosed.
    assert!(model_enclosure(Scale::Partner, &ratio(-1, 2), &ratio(1, 2), &b).is_none());
    assert!(model_enclosure(Scale::Partner, &rat(0), &ratio(1, 2), &b).is_none());
    // Positive interval (1/2, 1): z = b/α lies in (4/5, 8/5), w = α.
    let (z, w) = model_enclosure(Scale::Partner, &ratio(1, 2), &rat(1), &b).expect("enclosed");
    assert_eq!(z, (ratio(4, 5), ratio(8, 5)));
    assert_eq!(w, (ratio(1, 2), rat(1)));
    // A negative partner flips the order of the `Alpha` enclosure.
    let (z, w) =
        model_enclosure(Scale::Alpha, &ratio(1, 2), &rat(1), &ratio(-1, 2)).expect("enclosed");
    assert_eq!(z, (rat(-2), rat(-1)));
    assert_eq!(w, (ratio(-1, 2), ratio(-1, 2)));
    // `b = 0` declines by design: `Alpha` would need `w = 0`, `Partner` is skipped.
    for scale in [Scale::Alpha, Scale::Partner] {
        assert!(model_enclosure(scale, &ratio(1, 2), &rat(1), &rat(0)).is_none());
    }
}

#[test]
fn slope_enclosure_waits_until_the_seed_is_separated() {
    let b = ratio(1, 2);
    let (z0, w0) = (rat(1), rat(1));
    // z in (1/2 / 1/2, 1 / 1/2) = (1, 2) touches the seed's z = 1: not yet.
    assert!(slope_enclosure(Scale::Alpha, &ratio(1, 2), &rat(1), &b, (&z0, &w0)).is_none());
    // z in (5/4, 2): the slope (1/2 - 1)/(z - 1) lies in (-2, -1/2).
    let enclosure = slope_enclosure(Scale::Alpha, &ratio(5, 8), &rat(1), &b, (&z0, &w0));
    assert_eq!(enclosure, Some((rat(-2), ratio(-1, 2))));
}

// ---------------- end-to-end scaled refinement ----------------

/// `sqrt-problem-13-sqrt1-chunk-0032`, verbatim assertion.
const CHUNK_0032: &str = r#"
(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSM () Real)
(declare-fun skoSS () Real)
(assert (and (<= (- 2) skoX) (and (= (* skoX skoX) (+ 1 (* skoSS (* skoSS (- 1))))) (and (= skoX (+ 1 (* skoSM (* skoSM (- 1))))) (and (<= 0 skoSS) (and (<= 0 skoSM) (and (not (<= skoX 0)) (not (<= 1 skoX)))))))))
(check-sat)
"#;

/// Force the witness state: the listed rational values in the LRA model, the
/// ONLY algebraic value in the algebraic model, and a fresh one-shot guard.
/// Whatever the solver's own model left there is dropped first, so the joint
/// pass sees exactly one witness whether or not `check-sat` already refined.
fn force_state(
    exec: &mut Executor,
    rationals: &[(TermId, BigRational)],
    algebraic: TermId,
    value: RealAlgebraicValue,
) {
    if let Some(model) = exec.last_model.as_mut() {
        let lra = model.lra_model.as_mut().expect("LRA model");
        for (term, value) in rationals {
            lra.values.insert(*term, value.clone());
        }
        lra.values.remove(&algebraic);
    }
    exec.nra_algebraic_model.clear();
    exec.nra_algebraic_model.insert(algebraic, value);
    exec.nra_algebraic_model.reset_print_refinement_attempted();
}

/// The three chunk-0032 variables, in declaration order.
fn chunk_vars(exec: &mut Executor) -> (TermId, TermId, TermId) {
    (
        exec.ctx.terms.mk_var("skoX", Sort::Real),
        exec.ctx.terms.mk_var("skoSM", Sort::Real),
        exec.ctx.terms.mk_var("skoSS", Sort::Real),
    )
}

/// Independent exact re-verification of chunk 0032's pins and side
/// conditions — what the external validator computes.
fn assert_chunk_0032_model(exec: &Executor, x: TermId, sm: TermId, ss: TermId) {
    let (xv, smv, ssv) = (
        rational_of(exec, x),
        rational_of(exec, sm),
        rational_of(exec, ss),
    );
    assert_eq!(
        &xv * &xv,
        BigRational::one() - &ssv * &ssv,
        "skoX^2 = 1 - skoSS^2 must hold EXACTLY: {xv}, {ssv}"
    );
    assert_eq!(
        xv,
        BigRational::one() - &smv * &smv,
        "skoX = 1 - skoSM^2 must hold EXACTLY: {xv}, {smv}"
    );
    assert!(xv > BigRational::zero(), "skoX > 0: {xv}");
    assert!(xv < BigRational::one(), "skoX < 1: {xv}");
    assert!(ssv >= BigRational::zero(), "skoSS >= 0: {ssv}");
    assert!(smv >= BigRational::zero(), "skoSM >= 0: {smv}");
    let printed = exec.model();
    assert!(
        !printed.contains("root-obj"),
        "must print plain SMT-LIB: {printed}"
    );
}

/// Chunk 0032 with `skoSS = √7/4` algebraic and `skoSM = 1/2` rational.
/// Eliminating `skoX` leaves the QUARTIC `skoSS² − 2·skoSM² + skoSM⁴ = 0`,
/// which the plain chord sweep cannot parametrize; `skoSS = z·skoSM` turns it
/// into the circle `z² + skoSM² = 2` (the `Alpha` orientation).
#[test]
fn chunk_0032_quartic_refines_through_the_scaled_conic() {
    let (mut exec, out) = run_script(CHUNK_0032);
    assert_eq!(out[0], "sat");
    let (x, sm, ss) = chunk_vars(&mut exec);
    let rationals = [(sm, ratio(1, 2)), (x, ratio(3, 4))];
    force_state(&mut exec, &rationals, ss, sqrt_value(ratio(7, 16), 1));

    exec.refine_nra_algebraic_model_for_print();

    assert!(
        exec.nra_algebraic_model.is_empty(),
        "the quartic pin is refinable through z = skoSS/skoSM; the witness must go"
    );
    assert_chunk_0032_model(&exec, x, sm, ss);
}

/// The other orientation: `skoSM = √(2/5)` algebraic with the rational
/// partner `skoSS = 4/5` (and `skoX = 3/5`). Scaling the algebraic value by
/// the partner leaves a quartic again; scaling the PARTNER by the algebraic
/// value (`skoSS = z·skoSM`) gives the circle.
#[test]
fn chunk_0032_quartic_refines_with_the_partner_scaled() {
    let (mut exec, out) = run_script(CHUNK_0032);
    assert_eq!(out[0], "sat");
    let (x, sm, ss) = chunk_vars(&mut exec);
    let rationals = [(ss, ratio(4, 5)), (x, ratio(3, 5))];
    force_state(&mut exec, &rationals, sm, sqrt_value(ratio(2, 5), 1));

    exec.refine_nra_algebraic_model_for_print();

    assert!(
        exec.nra_algebraic_model.is_empty(),
        "the quartic pin is refinable through z = skoSS/skoSM; the witness must go"
    );
    assert_chunk_0032_model(&exec, x, sm, ss);
}

/// A zero partner declines by design (`Alpha` would need `w = 0`; `Partner`
/// is skipped conservatively): the algebraic model stays byte-identical.
#[test]
fn zero_partner_declines_and_preserves_the_algebraic_model() {
    let (mut exec, out) = run_script(CHUNK_0032);
    assert_eq!(out[0], "sat");
    let (x, sm, ss) = chunk_vars(&mut exec);
    let rationals = [(sm, rat(0)), (x, ratio(3, 4))];
    force_state(&mut exec, &rationals, ss, sqrt_value(ratio(7, 16), 1));
    let before = exec.model();

    exec.refine_nra_algebraic_model_for_print();

    assert!(
        !exec.nra_algebraic_model.is_empty(),
        "zero partner: must decline"
    );
    assert_eq!(exec.model(), before, "declined => model byte-identical");
    assert!(before.contains("root-obj"));
}

/// An ABSOLUTE pin in scaled form: with `skoSM > 0`, `skoX = 3/2 − skoSM²` and
/// `skoX² + skoSS² = 9/4` force `skoSS = skoSM·√(3 − skoSM²)`, and the circle
/// `z² + skoSM² = 3` has no rational point, so no rational model exists. Both
/// orientations must decline, never publish a rational triple that misses it.
#[test]
fn scaled_conic_without_a_rational_point_declines() {
    let (mut exec, out) = run_script(
        r#"
(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSM () Real)
(declare-fun skoSS () Real)
(assert (= (* skoX skoX) (+ (/ 9 4) (* skoSS (* skoSS (- 1))))))
(assert (= skoX (+ (/ 3 2) (* skoSM (* skoSM (- 1))))))
(assert (<= 0 skoSS))
(assert (< 0 skoSM))
(assert (not (<= skoX 0)))
(check-sat)
"#,
    );
    assert_eq!(out[0], "sat");
    let (x, sm, ss) = chunk_vars(&mut exec);
    let rationals = [(sm, ratio(1, 2)), (x, ratio(5, 4))];
    force_state(&mut exec, &rationals, ss, sqrt_value(ratio(11, 16), 1));
    let before = exec.model();

    exec.refine_nra_algebraic_model_for_print();

    assert!(
        !exec.nra_algebraic_model.is_empty(),
        "z^2 + w^2 = 3 has no rational point: refinement must decline"
    );
    assert_eq!(exec.model(), before, "declined => model byte-identical");
    assert!(before.contains("root-obj"));
}
