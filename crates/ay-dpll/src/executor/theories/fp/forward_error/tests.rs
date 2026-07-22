// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the FP forward-error tactic: exact rounding-bound
//! arithmetic and the end-to-end refutation decision on a hand-built
//! signed-distance dag (the geometry_consumer GUARD-claim shape).

#![allow(clippy::panic)]

use super::*;
use ay_core::Symbol;

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

#[test]
fn ceil_log2_exact_and_between() {
    assert_eq!(ceil_log2(&rat(1, 1)), 0);
    assert_eq!(ceil_log2(&rat(2, 1)), 1);
    assert_eq!(ceil_log2(&rat(3, 1)), 2);
    assert_eq!(ceil_log2(&pow2(48)), 48);
    assert_eq!(ceil_log2(&(pow2(48) * rat(3, 1))), 50);
    assert_eq!(ceil_log2(&rat(3, 10)), -1); // 1/4 < 0.3 <= 1/2
    assert_eq!(ceil_log2(&rat(1, 4)), -2);
    assert_eq!(ceil_log2(&pow2(-1075)), -1075);
}

#[test]
fn round_err_bound_f64_binades() {
    let f64_format = FpFormat::from_sort(&Sort::FloatingPoint(11, 53)).expect("f64 format");
    // |v| <= 2^48: worst half-spacing is in binade [2^47, 2^48) -> 2^-6.
    assert_eq!(f64_format.round_err_bound(&pow2(48)), pow2(-6));
    assert_eq!(f64_format.round_err_bound(&pow2(49)), pow2(-5));
    // 3*2^48 reaches binade [2^49, 2^50) -> 2^-4.
    assert_eq!(
        f64_format.round_err_bound(&(pow2(48) * rat(3, 1))),
        pow2(-4)
    );
    // Subnormal floor: tiny magnitudes still cost half a subnormal step.
    assert_eq!(f64_format.round_err_bound(&pow2(-1080)), pow2(-1075));
    assert_eq!(
        f64_format.round_err_bound(&BigRational::zero()),
        BigRational::zero()
    );
}

#[test]
fn representability_f64() {
    let f64_format = FpFormat::from_sort(&Sort::FloatingPoint(11, 53)).expect("f64 format");
    assert!(f64_format.is_representable(&BigRational::zero()));
    assert!(f64_format.is_representable(&pow2(48)));
    assert!(f64_format.is_representable(&(pow2(48) * rat(3, 1))));
    assert!(f64_format.is_representable(&(pow2(48) * rat(-3, 1))));
    assert!(f64_format.is_representable(&rat(1, 4)));
    // 0.3 is famously not a binary float.
    assert!(!f64_format.is_representable(&rat(3, 10)));
    // 2^-1074 is the smallest subnormal; half of it is not representable.
    assert!(f64_format.is_representable(&pow2(-1074)));
    assert!(!f64_format.is_representable(&pow2(-1075)));
    // 2^53 + 1 needs 54 significand bits.
    assert!(!f64_format.is_representable(&(pow2(53) + BigRational::one())));
    assert!(f64_format.is_representable(&(pow2(53) + rat(2, 1))));
    // Beyond the exponent range.
    assert!(!f64_format.is_representable(&pow2(2000)));
}

/// Build the geometry_consumer GUARD-claim signed-distance dag and its input-bound
/// assertions; returns (assertions-without-goal, to_real(rf), mirror-expr).
fn build_guard_dag(terms: &mut TermStore) -> (Vec<TermId>, TermId, TermId) {
    let f64_sort = Sort::FloatingPoint(11, 53);
    let rne = terms.mk_app(Symbol::named("RNE"), [], Sort::Bool);
    let mk_bounded_var = |terms: &mut TermStore, name: &str, mag: BigRational| {
        let v = terms.mk_var(name, f64_sort.clone());
        let is_normal = terms.mk_app(Symbol::named("fp.isNormal"), [v], Sort::Bool);
        let abs = terms.mk_app(Symbol::named("fp.abs"), [v], f64_sort.clone());
        let abs_real = terms.mk_app(Symbol::named("fp.to_real"), [abs], Sort::Real);
        let mag_const = terms.mk_rational(mag);
        let le = terms.mk_app(Symbol::named("<="), [abs_real, mag_const], Sort::Bool);
        let both = terms.mk_app(Symbol::named("and"), [is_normal, le], Sort::Bool);
        (v, both)
    };
    let one = BigRational::one();
    let b48 = pow2(48);
    let (nx, a1) = mk_bounded_var(terms, "nx", one.clone());
    let (ny, a2) = mk_bounded_var(terms, "ny", one.clone());
    let (nz, a3) = mk_bounded_var(terms, "nz", one);
    let (px, a4) = mk_bounded_var(terms, "px", b48.clone());
    let (py, a5) = mk_bounded_var(terms, "py", b48.clone());
    let (pz, a6) = mk_bounded_var(terms, "pz", b48.clone());
    let (d, a7) = mk_bounded_var(terms, "d", b48);

    let fp_mul = |terms: &mut TermStore, a: TermId, b: TermId| {
        terms.mk_app(Symbol::named("fp.mul"), [rne, a, b], f64_sort.clone())
    };
    let fp_add = |terms: &mut TermStore, a: TermId, b: TermId| {
        terms.mk_app(Symbol::named("fp.add"), [rne, a, b], f64_sort.clone())
    };
    let t1 = fp_mul(terms, nx, px);
    let t2 = fp_mul(terms, ny, py);
    let t3 = fp_mul(terms, nz, pz);
    let s1 = fp_add(terms, t1, t2);
    let s2 = fp_add(terms, s1, t3);
    let rf = fp_add(terms, s2, d);
    let rf_real = terms.mk_app(Symbol::named("fp.to_real"), [rf], Sort::Real);

    let to_real = |terms: &mut TermStore, v: TermId| {
        terms.mk_app(Symbol::named("fp.to_real"), [v], Sort::Real)
    };
    let nx_r = to_real(terms, nx);
    let px_r = to_real(terms, px);
    let ny_r = to_real(terms, ny);
    let py_r = to_real(terms, py);
    let nz_r = to_real(terms, nz);
    let pz_r = to_real(terms, pz);
    let d_r = to_real(terms, d);
    let m1 = terms.mk_app(Symbol::named("*"), [nx_r, px_r], Sort::Real);
    let m2 = terms.mk_app(Symbol::named("*"), [ny_r, py_r], Sort::Real);
    let m3 = terms.mk_app(Symbol::named("*"), [nz_r, pz_r], Sort::Real);
    let mirror = terms.mk_app(Symbol::named("+"), [m1, m2, m3, d_r], Sort::Real);

    (vec![a1, a2, a3, a4, a5, a6, a7], rf_real, mirror)
}

/// The certified bound for the GUARD dag is exactly 13/64 = 0.203125:
/// 3 products at 2^-6, then adds at 2^-5, 2^-4, 2^-4 with representable
/// interval endpoints clamping every stage.
#[test]
fn guard_dag_certified_bound_is_13_64ths() {
    let mut terms = TermStore::new();
    let (mut assertions, rf_real, mirror) = build_guard_dag(&mut terms);
    let claim = terms.mk_rational(rat(3, 10));
    let diff = terms.mk_app(Symbol::named("-"), [rf_real, mirror], Sort::Real);
    let goal = terms.mk_app(Symbol::named(">="), [diff, claim], Sort::Bool);
    assertions.push(goal);

    let refutation = try_refute_forward_error_goal(&terms, &assertions)
        .expect("0.3 claim must be refuted (bound 13/64 < 3/10)");
    assert_eq!(refutation.goal, goal);
    assert_eq!(refutation.bound, rat(13, 64));
}

#[test]
fn guard_dag_tight_claim_is_not_refuted() {
    let mut terms = TermStore::new();
    let (mut assertions, rf_real, mirror) = build_guard_dag(&mut terms);
    // 1e-7 is far below the certified bound 13/64: the tactic must abstain
    // (real rounding errors genuinely exceed 1e-7 at these magnitudes).
    let claim = terms.mk_rational(rat(1, 10_000_000));
    let diff = terms.mk_app(Symbol::named("-"), [rf_real, mirror], Sort::Real);
    let goal = terms.mk_app(Symbol::named(">="), [diff, claim], Sort::Bool);
    assertions.push(goal);

    assert!(try_refute_forward_error_goal(&terms, &assertions).is_none());
}

#[test]
fn guard_dag_boundary_claim_exactly_at_bound() {
    let mut terms = TermStore::new();
    let (mut assertions, rf_real, mirror) = build_guard_dag(&mut terms);
    // `diff >= 13/64` cannot be refuted (needs strict excess over the bound)…
    let claim = terms.mk_rational(rat(13, 64));
    let diff = terms.mk_app(Symbol::named("-"), [rf_real, mirror], Sort::Real);
    let goal = terms.mk_app(Symbol::named(">="), [diff, claim], Sort::Bool);
    let mut with_ge = assertions.clone();
    with_ge.push(goal);
    assert!(try_refute_forward_error_goal(&terms, &with_ge).is_none());

    // …but the strict `diff > 13/64` is refuted.
    let goal_gt = terms.mk_app(Symbol::named(">"), [diff, claim], Sort::Bool);
    assertions.push(goal_gt);
    assert!(try_refute_forward_error_goal(&terms, &assertions).is_some());
}

#[test]
fn guard_dag_reversed_orientation_refuted() {
    let mut terms = TermStore::new();
    let (mut assertions, rf_real, mirror) = build_guard_dag(&mut terms);
    // mirror - to_real(rf) <= -0.3 is the same claim with flipped sign.
    let claim = terms.mk_rational(rat(-3, 10));
    let diff = terms.mk_app(Symbol::named("-"), [mirror, rf_real], Sort::Real);
    let goal = terms.mk_app(Symbol::named("<="), [diff, claim], Sort::Bool);
    assertions.push(goal);

    assert!(try_refute_forward_error_goal(&terms, &assertions).is_some());
}

#[test]
fn missing_normality_aborts() {
    let mut terms = TermStore::new();
    let (mut assertions, rf_real, mirror) = build_guard_dag(&mut terms);
    // Drop the first input's (and isNormal bound) conjunction entirely.
    let _ = assertions.remove(0);
    let claim = terms.mk_rational(rat(3, 10));
    let diff = terms.mk_app(Symbol::named("-"), [rf_real, mirror], Sort::Real);
    let goal = terms.mk_app(Symbol::named(">="), [diff, claim], Sort::Bool);
    assertions.push(goal);

    assert!(try_refute_forward_error_goal(&terms, &assertions).is_none());
}

#[test]
fn mirror_mismatch_aborts() {
    let mut terms = TermStore::new();
    let (mut assertions, rf_real, _mirror) = build_guard_dag(&mut terms);
    // A mirror that swaps operands across products is a DIFFERENT polynomial;
    // the claim is not a pure rounding-error claim and must be left alone.
    let to_real = |terms: &mut TermStore, name: &str| {
        // mk_var is idempotent by name: this resolves the existing variable.
        let v = terms.mk_var(name, Sort::FloatingPoint(11, 53));
        terms.mk_app(Symbol::named("fp.to_real"), [v], Sort::Real)
    };
    let nx_r = to_real(&mut terms, "nx");
    let py_r = to_real(&mut terms, "py");
    let ny_r = to_real(&mut terms, "ny");
    let px_r = to_real(&mut terms, "px");
    let nz_r = to_real(&mut terms, "nz");
    let pz_r = to_real(&mut terms, "pz");
    let d_r = to_real(&mut terms, "d");
    let m1 = terms.mk_app(Symbol::named("*"), [nx_r, py_r], Sort::Real);
    let m2 = terms.mk_app(Symbol::named("*"), [ny_r, px_r], Sort::Real);
    let m3 = terms.mk_app(Symbol::named("*"), [nz_r, pz_r], Sort::Real);
    let wrong_mirror = terms.mk_app(Symbol::named("+"), [m1, m2, m3, d_r], Sort::Real);

    let claim = terms.mk_rational(rat(3, 10));
    let diff = terms.mk_app(Symbol::named("-"), [rf_real, wrong_mirror], Sort::Real);
    let goal = terms.mk_app(Symbol::named(">="), [diff, claim], Sort::Bool);
    assertions.push(goal);

    assert!(try_refute_forward_error_goal(&terms, &assertions).is_none());
}

#[test]
fn non_rne_rounding_mode_aborts() {
    let mut terms = TermStore::new();
    let f64_sort = Sort::FloatingPoint(11, 53);
    let rtz = terms.mk_app(Symbol::named("RTZ"), [], Sort::Bool);
    let v = terms.mk_var("x", f64_sort.clone());
    let is_normal = terms.mk_app(Symbol::named("fp.isNormal"), [v], Sort::Bool);
    let abs = terms.mk_app(Symbol::named("fp.abs"), [v], f64_sort.clone());
    let abs_real = terms.mk_app(Symbol::named("fp.to_real"), [abs], Sort::Real);
    let one = terms.mk_rational(BigRational::one());
    let le = terms.mk_app(Symbol::named("<="), [abs_real, one], Sort::Bool);

    let sum = terms.mk_app(Symbol::named("fp.add"), [rtz, v, v], f64_sort);
    let sum_real = terms.mk_app(Symbol::named("fp.to_real"), [sum], Sort::Real);
    let v_real = terms.mk_app(Symbol::named("fp.to_real"), [v], Sort::Real);
    let two = terms.mk_rational(rat(2, 1));
    let mirror = terms.mk_app(Symbol::named("*"), [two, v_real], Sort::Real);
    let diff = terms.mk_app(Symbol::named("-"), [sum_real, mirror], Sort::Real);
    let claim = terms.mk_rational(BigRational::one());
    let goal = terms.mk_app(Symbol::named(">="), [diff, claim], Sort::Bool);

    // The half-ulp model is RNE-specific: an RTZ dag must abort even though
    // the claim (error >= 1) would otherwise be comfortably refutable.
    let assertions = vec![is_normal, le, goal];
    assert!(try_refute_forward_error_goal(&terms, &assertions).is_none());
}

#[test]
fn overflow_risk_aborts() {
    let mut terms = TermStore::new();
    let f64_sort = Sort::FloatingPoint(11, 53);
    let rne = terms.mk_app(Symbol::named("RNE"), [], Sort::Bool);
    let v = terms.mk_var("x", f64_sort.clone());
    let is_normal = terms.mk_app(Symbol::named("fp.isNormal"), [v], Sort::Bool);
    let abs = terms.mk_app(Symbol::named("fp.abs"), [v], f64_sort.clone());
    let abs_real = terms.mk_app(Symbol::named("fp.to_real"), [abs], Sort::Real);
    // |x| <= 2^1023: x + x may overflow to +oo, where fp.to_real is
    // unconstrained — the tactic must abstain.
    let big = terms.mk_rational(pow2(1023));
    let le = terms.mk_app(Symbol::named("<="), [abs_real, big], Sort::Bool);

    let sum = terms.mk_app(Symbol::named("fp.add"), [rne, v, v], f64_sort);
    let sum_real = terms.mk_app(Symbol::named("fp.to_real"), [sum], Sort::Real);
    let v_real = terms.mk_app(Symbol::named("fp.to_real"), [v], Sort::Real);
    let two = terms.mk_rational(rat(2, 1));
    let mirror = terms.mk_app(Symbol::named("*"), [two, v_real], Sort::Real);
    let diff = terms.mk_app(Symbol::named("-"), [sum_real, mirror], Sort::Real);
    let claim = terms.mk_rational(pow2(900));
    let goal = terms.mk_app(Symbol::named(">="), [diff, claim], Sort::Bool);

    let assertions = vec![is_normal, le, goal];
    assert!(try_refute_forward_error_goal(&terms, &assertions).is_none());
}
