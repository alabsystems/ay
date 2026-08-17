// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Sort;
use ay_frontend::parse;

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

// ---------------- simplest_rational_in_open ----------------

#[test]
fn simplest_rational_basics() {
    // Straddles zero.
    assert_eq!(
        simplest_rational_in_open(&rat(-1, 3), &rat(1, 7), MAX_SIMPLEST_STEPS),
        Some(rat(0, 1))
    );
    // Contains an integer.
    assert_eq!(
        simplest_rational_in_open(&rat(9, 10), &rat(11, 10), MAX_SIMPLEST_STEPS),
        Some(rat(1, 1))
    );
    // (1, 2) open: no integer inside, simplest is 3/2.
    assert_eq!(
        simplest_rational_in_open(&rat(1, 1), &rat(2, 1), MAX_SIMPLEST_STEPS),
        Some(rat(3, 2))
    );
    // (1.3, 1.5) open: 3/2 is excluded (open end), 4/3 wins.
    assert_eq!(
        simplest_rational_in_open(&rat(13, 10), &rat(3, 2), MAX_SIMPLEST_STEPS),
        Some(rat(4, 3))
    );
    // (0.5, 0.6) open: both ends excluded, smallest denominator inside is 4/7.
    assert_eq!(
        simplest_rational_in_open(&rat(1, 2), &rat(3, 5), MAX_SIMPLEST_STEPS),
        Some(rat(4, 7))
    );
    // Negative mirror of the (1.3, 1.5) case.
    assert_eq!(
        simplest_rational_in_open(&rat(-3, 2), &rat(-13, 10), MAX_SIMPLEST_STEPS),
        Some(rat(-4, 3))
    );
    // Degenerate interval: fail closed.
    assert_eq!(
        simplest_rational_in_open(&rat(1, 2), &rat(1, 2), MAX_SIMPLEST_STEPS),
        None
    );
    assert_eq!(
        simplest_rational_in_open(&rat(2, 3), &rat(1, 2), MAX_SIMPLEST_STEPS),
        None
    );
}

#[test]
fn simplest_rational_depth_cap_fails_closed() {
    // (1/3, 1/2) needs at least one recursion level; a zero budget at
    // that level must return None, never loop or approximate.
    assert_eq!(simplest_rational_in_open(&rat(1, 3), &rat(1, 2), 1), None);
    assert_eq!(simplest_rational_in_open(&rat(1, 3), &rat(1, 2), 0), None);
    // With budget it succeeds.
    assert_eq!(
        simplest_rational_in_open(&rat(1, 3), &rat(1, 2), MAX_SIMPLEST_STEPS),
        Some(rat(2, 5))
    );
}

#[test]
fn candidate_size_cap_declines() {
    // An interval between consecutive dyadics of denominator 2^600: every
    // rational inside has more than MAX_CANDIDATE_BITS bits (numerator +
    // denominator), so candidate generation must decline — either through
    // the size guard or the walk depth cap, but never by producing an
    // oversized candidate.
    let denom = BigInt::one() << 600u32;
    let k = BigInt::from(3) * (BigInt::one() << 598u32); // ~ 3/4 * 2^600
    let lo = BigRational::new(k.clone(), denom.clone());
    let hi = BigRational::new(k + BigInt::one(), denom);
    let sqrt2 = sqrt2_value();
    let state = vec![RefineVar {
        term: TermId(0),
        alpha: sqrt2.alpha().clone(),
        lo,
        hi,
        exact: None,
    }];
    assert!(
        candidates(&state).is_none(),
        "an interval admitting only oversized rationals must decline"
    );
}

#[test]
fn candidate_exact_value_wins_over_interval() {
    let sqrt2 = sqrt2_value();
    let state = vec![RefineVar {
        term: TermId(0),
        alpha: sqrt2.alpha().clone(),
        lo: rat(1, 1),
        hi: rat(2, 1),
        exact: Some(rat(7, 5)),
    }];
    assert_eq!(candidates(&state), Some(vec![(TermId(0), rat(7, 5))]));
}

// ---------------- end-to-end refinement ----------------

/// The positive root of `x^2 - 2` as an exact algebraic value.
fn sqrt2_value() -> RealAlgebraicValue {
    ay_nra::rcf_api::real_roots(&[
        BigRational::from_integer(BigInt::from(-2)),
        BigRational::zero(),
        BigRational::one(),
    ])
    .expect("x^2 - 2 root isolation")
    .into_iter()
    .filter_map(|root| match root {
        RealScalar::Algebraic(value) => Some(value),
        RealScalar::Rational(_) => None,
    })
    .find(|v| v.sign() == Some(1))
    .expect("x^2 - 2 has a positive irrational root")
}

fn run_script(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("script parses");
    let mut exec = Executor::new();
    let out = exec.execute_all(&commands).expect("script executes");
    (exec, out)
}

/// OPEN constraints admit rationals near the algebraic witness: an
/// installed sqrt(2) witness for `1 < x  /\  x*x < 3` must be replaced by
/// a nearby rational whose full assignment re-verifies exactly, and the
/// printed model must be plain SMT-LIB (no root-obj).
#[test]
fn model_refinement_replaces_sqrt2_witness_on_open_constraints() {
    let (mut exec, out) = run_script(
        r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (> x 1.0))
(assert (< (* x x) 3.0))
(check-sat)
"#,
    );
    assert_eq!(out[0], "sat");
    let x = exec.ctx.terms.mk_var("x", Sort::Real);

    // Force the algebraic-witness state the NRA certificate lane
    // produces: x = sqrt(2), no rational LRA entry for x.
    exec.nra_algebraic_model.insert(x, sqrt2_value());
    if let Some(model) = exec.last_model.as_mut() {
        if let Some(lra) = model.lra_model.as_mut() {
            lra.values.remove(&x);
        }
    }
    exec.nra_algebraic_model.reset_print_refinement_attempted();

    exec.refine_nra_algebraic_model_for_print();

    assert!(
        exec.nra_algebraic_model.is_empty(),
        "the sqrt(2) witness must be refined away into a rational"
    );
    let refined = exec
        .last_model
        .as_ref()
        .and_then(|m| m.lra_model.as_ref())
        .and_then(|l| l.values.get(&x))
        .expect("refined rational value for x")
        .clone();
    assert!(
        refined > rat(1, 1) && &refined * &refined < rat(3, 1),
        "refined value must satisfy the assertions exactly, got {refined}"
    );
    let printed = exec.model();
    assert!(
        !printed.contains("root-obj"),
        "refined model must print plain SMT-LIB rationals: {printed}"
    );
    assert!(
        printed.contains("(define-fun x () Real"),
        "x must still be defined in the printed model: {printed}"
    );
}

/// EQUALITY-PINNED at an irrational: `x*x = 2  /\  x > 0` has NO rational
/// model, so refinement must decline and the exact root-obj output must
/// be preserved byte-for-byte (never a wrong rational model). Runs
/// through the real `(get-model)` command path, which is where the
/// refinement hook lives.
#[test]
fn model_refinement_declines_on_equality_pinned_irrational() {
    let (exec, out) = run_script(
        r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= (* x x) 2.0))
(assert (> x 0.0))
(check-sat)
(get-model)
"#,
    );
    assert_eq!(out[0], "sat");
    assert!(
        out[1].contains("(define-fun x () Real (root-obj (+ (^ x 2) (- 2)) 2))"),
        "refinement must decline and preserve the exact algebraic model: {}",
        out[1]
    );
    assert!(
        !exec.nra_algebraic_model.is_empty(),
        "declined refinement must leave the algebraic witness in place"
    );
    assert!(
        exec.nra_algebraic_model.print_refinement_attempted(),
        "the bounded search must run at most once per verdict"
    );
}

/// The one-shot guard: a second print does not re-run the search, and the
/// declined model still prints identically.
#[test]
fn model_refinement_attempt_is_one_shot_per_verdict() {
    let (mut exec, out) = run_script(
        r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= (* x x) 2.0))
(assert (> x 0.0))
(check-sat)
"#,
    );
    assert_eq!(out[0], "sat");
    exec.refine_nra_algebraic_model_for_print();
    assert!(exec.nra_algebraic_model.print_refinement_attempted());
    let first = exec.model();
    // Second call is a no-op (flag short-circuits) and printing is stable.
    exec.refine_nra_algebraic_model_for_print();
    let second = exec.model();
    assert_eq!(first, second);
    assert!(first.contains("root-obj"));
}

/// The positive root of `x^2 - c` for rational `c > 0`, as an exact
/// algebraic value. `None` when the root is rational.
fn sqrt_value(c: BigRational) -> RealAlgebraicValue {
    ay_nra::rcf_api::real_roots(&[-c, BigRational::zero(), BigRational::one()])
        .expect("x^2 - c root isolation")
        .into_iter()
        .filter_map(|root| match root {
            RealScalar::Algebraic(value) => Some(value),
            RealScalar::Rational(_) => None,
        })
        .find(|v| v.sign() == Some(1))
        .expect("x^2 - c has a positive irrational root")
}

/// ADVERSARIAL (joint coupling): two refined variables whose individual
/// constraints (`1 < v`, `v*v < 2`) admit nearly every nearby rational,
/// coupled by a THIRD assertion `x*x + y*y in (3.9399, 3.9401)` that
/// almost every individually-plausible candidate pair violates (true
/// point: x = sqrt(1.99), y = sqrt(1.95), sum exactly 3.94). A
/// per-assertion-in-isolation or per-variable acceptance would install a
/// pair that satisfies the boxes and breaks the coupling — the WRONG
/// model handed to the external validator. Acceptance is only correct if
/// the re-check is joint over the WHOLE assertion set; this test
/// re-verifies the accepted pair with independent exact BigRational
/// arithmetic, so any non-joint acceptance fails here.
#[test]
fn joint_coupling_is_verified_across_refined_variables() {
    let (mut exec, out) = run_script(
        r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (> x 1.0))
(assert (< (* x x) 2.0))
(assert (> y 1.0))
(assert (< (* y y) 2.0))
(assert (> (+ (* x x) (* y y)) 3.9399))
(assert (< (+ (* x x) (* y y)) 3.9401))
(check-sat)
"#,
    );
    assert_eq!(out[0], "sat");
    let x = exec.ctx.terms.mk_var("x", Sort::Real);
    let y = exec.ctx.terms.mk_var("y", Sort::Real);

    // Force the algebraic-witness state: x = sqrt(1.99), y = sqrt(1.95),
    // no rational LRA entries for either.
    exec.nra_algebraic_model
        .insert(x, sqrt_value(rat(199, 100)));
    exec.nra_algebraic_model
        .insert(y, sqrt_value(rat(195, 100)));
    if let Some(model) = exec.last_model.as_mut() {
        if let Some(lra) = model.lra_model.as_mut() {
            lra.values.remove(&x);
            lra.values.remove(&y);
        }
    }
    exec.nra_algebraic_model.reset_print_refinement_attempted();

    exec.refine_nra_algebraic_model_for_print();

    assert!(
        exec.nra_algebraic_model.is_empty(),
        "open joint constraints admit a rational pair; the bounded search \
             must find one"
    );
    let lra = exec
        .last_model
        .as_ref()
        .and_then(|m| m.lra_model.as_ref())
        .expect("refined LRA model");
    let a = lra.values.get(&x).expect("refined rational for x").clone();
    let b = lra.values.get(&y).expect("refined rational for y").clone();
    // Independent exact re-verification of EVERY assertion, including the
    // coupling window: this is what the external validator will compute.
    let one = rat(1, 1);
    let two = rat(2, 1);
    let sum = &a * &a + &b * &b;
    assert!(a > one && b > one, "boxes: {a}, {b}");
    assert!(&a * &a < two && &b * &b < two, "boxes: {a}, {b}");
    assert!(
        sum > rat(39399, 10000) && sum < rat(39401, 10000),
        "the COUPLING must hold for the pair jointly, got {sum}"
    );
    let printed = exec.model();
    assert!(
        !printed.contains("root-obj"),
        "accepted refinement must print plain rationals: {printed}"
    );
}

/// Refinement leaves get-value consistent with get-model after success:
/// the refined rational is what evaluation reads.
#[test]
fn refined_value_is_read_by_evaluation() {
    let (mut exec, out) = run_script(
        r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (> x 1.0))
(assert (< (* x x) 3.0))
(check-sat)
"#,
    );
    assert_eq!(out[0], "sat");
    let x = exec.ctx.terms.mk_var("x", Sort::Real);
    exec.nra_algebraic_model.insert(x, sqrt2_value());
    if let Some(model) = exec.last_model.as_mut() {
        if let Some(lra) = model.lra_model.as_mut() {
            lra.values.remove(&x);
        }
    }
    exec.nra_algebraic_model.reset_print_refinement_attempted();
    exec.refine_nra_algebraic_model_for_print();
    assert!(exec.nra_algebraic_model.is_empty());

    let model = exec.last_model.clone().expect("model");
    let refined = model
        .lra_model
        .as_ref()
        .and_then(|l| l.values.get(&x))
        .expect("refined rational")
        .clone();
    assert_eq!(
        exec.evaluate_term(&model, x),
        EvalValue::Rational(refined),
        "evaluation must read the refined rational, keeping get-value \
             consistent with the printed model"
    );
}
