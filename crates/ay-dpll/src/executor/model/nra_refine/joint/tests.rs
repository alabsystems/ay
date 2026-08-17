// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::Sort;
use ay_frontend::parse;
use ay_nra::{RealAlgebraicValue, RealScalar};
use num_bigint::BigInt;
use num_traits::One;

fn ratio(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

// ---------------- pure candidate-generation helpers ----------------

#[test]
fn quadratic_fit_confirms_at_a_fourth_point() {
    // f(x) = 2x^2 - 3x + 5 sampled at 0, 1, -1, 2.
    let f = |x: i64| rat(2 * x * x - 3 * x + 5);
    assert_eq!(
        quadratic_fit(&f(0), &f(1), &f(-1), &f(2)),
        Some((rat(5), rat(-3), rat(2)))
    );
    // A CUBIC must not be mistaken for a conic — the fourth sample is what
    // catches it (the Fermat-cubic pins land here and must decline).
    let g = |x: i64| rat(x * x * x + 1);
    assert_eq!(quadratic_fit(&g(0), &g(1), &g(-1), &g(2)), None);
    // This quartic (a shape a squared substitution leaves behind) too.
    let h = |x: i64| rat(x * x * x * x - 2 * x * x);
    assert_eq!(quadratic_fit(&h(0), &h(1), &h(-1), &h(2)), None);
}

/// The exact reach of the fourth-sample check: every cubic is rejected, but
/// the quartic family `a3 = -2*a4` reproduces its own quadratic fit at λ = 2.
#[test]
fn quadratic_fit_rejects_every_cubic_but_not_every_quartic() {
    let sample =
        |f: &dyn Fn(i64) -> i64| quadratic_fit(&rat(f(0)), &rat(f(1)), &rat(f(-1)), &rat(f(2)));
    for a3 in [1i64, -1, 2, -5, 7] {
        for a2 in [0i64, 3, -4] {
            for a1 in [0i64, 1, -6] {
                assert_eq!(
                    sample(&|x| a3 * x * x * x + a2 * x * x + a1 * x + 9),
                    None,
                    "a cubic with a3={a3} must be rejected"
                );
            }
        }
    }

    let slipped = sample(&|x| x * x * x * x - 2 * x * x * x);
    assert_eq!(slipped, Some((rat(0), rat(-2), rat(1))));
    let (c0, c1, c2) = slipped.expect("fitted");
    let at3 = &c2 * rat(9) + &c1 * rat(3) + &c0;
    assert_eq!(at3, rat(3));
    assert_eq!(rat(3 * 3 * 3 * 3 - 2 * 3 * 3 * 3), rat(27));
    assert_ne!(at3, rat(27));
    assert_eq!(sample(&|x| x * x * x * x), None);
}

#[test]
fn rational_roots_are_exact_or_empty() {
    // x^2 - 1: roots 1 and -1.
    let mut roots = rational_roots(&rat(-1), &rat(0), &rat(1));
    roots.sort();
    assert_eq!(roots, vec![rat(-1), rat(1)]);
    // x^2 - 2 has NO rational root: the discriminant 8 is not a square.
    assert!(rational_roots(&rat(-2), &rat(0), &rat(1)).is_empty());
    // Double root: reported once.
    assert_eq!(
        rational_roots(&rat(1), &rat(-2), &rat(1)),
        vec![BigRational::one()]
    );
    // Linear fallback: 3x - 1.
    assert_eq!(
        rational_roots(&rat(-1), &rat(3), &rat(0)),
        vec![ratio(1, 3)]
    );
    // Degenerate: no equation at all.
    assert!(rational_roots(&rat(5), &rat(0), &rat(0)).is_empty());
}

#[test]
fn seed_values_include_the_models_own_rationals() {
    let values = vec![ratio(3, 2)];
    let seeds = seed_values(&values);
    assert!(seeds.contains(&ratio(3, 2)), "{seeds:?}");
    assert!(seeds.contains(&ratio(-3, 2)), "{seeds:?}");
    assert!(seeds.contains(&BigRational::zero()));
    // No duplicates: the walk is bounded and deterministic.
    let mut sorted = seeds.clone();
    sorted.sort();
    sorted.dedup();
    assert_eq!(sorted.len(), seeds.len());
}

// ---------------- end-to-end joint refinement ----------------

/// The positive or negative root of `x^2 - c` as an exact algebraic value.
fn sqrt_value(c: BigRational, sign: i32) -> RealAlgebraicValue {
    ay_nra::rcf_api::real_roots(&[-c, BigRational::zero(), BigRational::one()])
        .expect("x^2 - c root isolation")
        .into_iter()
        .filter_map(|root| match root {
            RealScalar::Algebraic(value) => Some(value),
            RealScalar::Rational(_) => None,
        })
        .find(|v| v.sign() == Some(sign))
        .expect("x^2 - c has an irrational root of that sign")
}

fn run_script(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("script parses");
    let mut exec = Executor::new();
    let out = exec.execute_all(&commands).expect("script executes");
    (exec, out)
}

fn rational_of(exec: &Executor, var: TermId) -> BigRational {
    exec.last_model
        .as_ref()
        .and_then(|m| m.lra_model.as_ref())
        .and_then(|l| l.values.get(&var))
        .unwrap_or_else(|| panic!("refined rational value for {var:?}"))
        .clone()
}

/// CONVOI2 shape (`meti-tarski/CONVOI2/CONVOI2-chunk-0019`): `skoS² + skoC² =
/// 1` pins the algebraic `skoC = −√3/2` to the RATIONAL partner `skoS = 1/2`,
/// with everything else strict. Moving `skoC` alone can never satisfy the
/// equality; the joint pass must move the PAIR to an exact rational point of
/// the unit circle, re-verify every assertion exactly, and print plain
/// SMT-LIB.
#[test]
fn convoi2_shape_refines_the_pinned_pair_jointly() {
    let (mut exec, out) = run_script(
        r#"
(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun skoT () Real)
(assert (= (* skoS skoS) (+ 1 (* skoC (* skoC (- 1))))))
(assert (not (<= skoS 0)))
(assert (not (<= skoC (- 1))))
(assert (not (<= 0 skoC)))
(assert (not (<= skoT 0)))
(assert (not (<= 1 skoT)))
(check-sat)
"#,
    );
    assert_eq!(out[0], "sat");
    let s = exec.ctx.terms.mk_var("skoS", Sort::Real);
    let c = exec.ctx.terms.mk_var("skoC", Sort::Real);

    // Force the algebraic-witness state the NRA lane produces on the real
    // instance: skoS = 1/2 rational, skoC = -sqrt(3)/2 algebraic.
    if let Some(model) = exec.last_model.as_mut() {
        let lra = model.lra_model.as_mut().expect("LRA model");
        lra.values.insert(s, ratio(1, 2));
        lra.values.remove(&c);
    }
    exec.nra_algebraic_model
        .insert(c, sqrt_value(ratio(3, 4), -1));
    exec.nra_algebraic_model.reset_print_refinement_attempted();

    exec.refine_nra_algebraic_model_for_print();

    assert!(
        exec.nra_algebraic_model.is_empty(),
        "the pinned pair is jointly refinable; the algebraic witness must go"
    );
    let (sv, cv) = (rational_of(&exec, s), rational_of(&exec, c));
    // Independent exact re-verification of the PIN and of every side
    // condition — this is what the external validator computes.
    assert_eq!(
        &sv * &sv + &cv * &cv,
        BigRational::one(),
        "the refined pair must be EXACTLY on the unit circle: {sv}, {cv}"
    );
    assert!(sv > BigRational::zero(), "skoS > 0, got {sv}");
    assert!(cv < BigRational::zero(), "skoC < 0, got {cv}");
    assert!(cv > -BigRational::one(), "skoC > -1, got {cv}");
    let printed = exec.model();
    assert!(
        !printed.contains("root-obj"),
        "a jointly refined model must print plain SMT-LIB rationals: {printed}"
    );
}

/// The sqrt-family shape (`sqrt-problem-12vars3-chunk-0013`): TWO equalities,
/// `skoX = 1 − skoSMX²` and `skoSX² − 1 = skoX`. `skoX` is eliminated
/// affinely; what remains is the circle `skoSX² + skoSMX² = 2`, whose rational
/// point (1,1) seeds the chord. All three variables must move together, and
/// the tight non-strict bound `skoX ≤ 1` must still hold exactly.
#[test]
fn sqrt_shape_refines_through_an_eliminated_partner() {
    let (mut exec, out) = run_script(
        r#"
(set-logic QF_NRA)
(declare-fun skoX () Real)
(declare-fun skoSMX () Real)
(declare-fun skoSX () Real)
(assert (= skoX (+ 1 (* skoSMX (* skoSMX (- 1))))))
(assert (= (+ (- 1) (* skoSX skoSX)) skoX))
(assert (<= skoX 1))
(assert (<= 0 skoSX))
(assert (<= 0 skoSMX))
(assert (not (<= skoX 0)))
(check-sat)
"#,
    );
    assert_eq!(out[0], "sat");
    let x = exec.ctx.terms.mk_var("skoX", Sort::Real);
    let smx = exec.ctx.terms.mk_var("skoSMX", Sort::Real);
    let sx = exec.ctx.terms.mk_var("skoSX", Sort::Real);

    if let Some(model) = exec.last_model.as_mut() {
        let lra = model.lra_model.as_mut().expect("LRA model");
        lra.values.insert(x, BigRational::one());
        lra.values.insert(smx, BigRational::zero());
        lra.values.remove(&sx);
    }
    exec.nra_algebraic_model.insert(sx, sqrt_value(rat(2), 1));
    exec.nra_algebraic_model.reset_print_refinement_attempted();

    exec.refine_nra_algebraic_model_for_print();

    assert!(
        exec.nra_algebraic_model.is_empty(),
        "the sqrt pin is jointly refinable; the algebraic witness must go"
    );
    let (xv, smxv, sxv) = (
        rational_of(&exec, x),
        rational_of(&exec, smx),
        rational_of(&exec, sx),
    );
    assert_eq!(
        xv,
        BigRational::one() - &smxv * &smxv,
        "eliminated partner must satisfy its equality EXACTLY"
    );
    assert_eq!(
        &sxv * &sxv - BigRational::one(),
        xv,
        "the residual pin must hold EXACTLY"
    );
    assert!(xv <= BigRational::one(), "tight bound skoX <= 1: {xv}");
    assert!(xv > BigRational::zero(), "skoX > 0: {xv}");
    assert!(smxv >= BigRational::zero(), "skoSMX >= 0: {smxv}");
    assert!(sxv >= BigRational::zero(), "skoSX >= 0: {sxv}");
    assert!(!exec.model().contains("root-obj"));
}

/// ABSOLUTE (no rational point anywhere on the pinning variety): `x² = 2`
/// with a movable partner is still unrefinable — `x² + y² = 3` has no
/// rational point at all (3 is not a sum of two rational squares). The joint
/// pass must decline and leave the exact algebraic model byte-identical,
/// never publish a rational pair that misses the circle.
#[test]
fn absolute_pin_declines_and_preserves_the_algebraic_model() {
    let (mut exec, out) = run_script(
        r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (+ (* x x) (* y y)) 3.0))
(assert (not (<= x 0)))
(assert (not (<= y 0)))
(check-sat)
"#,
    );
    assert_eq!(out[0], "sat");
    let x = exec.ctx.terms.mk_var("x", Sort::Real);
    let y = exec.ctx.terms.mk_var("y", Sort::Real);
    if let Some(model) = exec.last_model.as_mut() {
        let lra = model.lra_model.as_mut().expect("LRA model");
        lra.values.insert(y, BigRational::one());
        lra.values.remove(&x);
    }
    exec.nra_algebraic_model.insert(x, sqrt_value(rat(2), 1));
    exec.nra_algebraic_model.reset_print_refinement_attempted();
    let before = exec.model();

    exec.refine_nra_algebraic_model_for_print();

    assert!(
        !exec.nra_algebraic_model.is_empty(),
        "x^2 + y^2 = 3 has no rational point: refinement must decline"
    );
    assert_eq!(
        exec.model(),
        before,
        "a declined joint refinement must leave the model byte-identical"
    );
    assert!(before.contains("root-obj"));
}

/// The single-variable ABSOLUTE pin (`x² = 2`, no partner at all): the chord
/// mode has no second coordinate and must fail closed rather than invent one.
#[test]
fn pin_without_a_partner_declines() {
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
        "exact algebraic model must be preserved: {}",
        out[1]
    );
    assert!(!exec.nra_algebraic_model.is_empty());
}

/// Bounds fail closed: a proposal whose bit-width blows past
/// [`MAX_JOINT_CANDIDATE_BITS`] is rejected BEFORE installation, so the
/// algebraic model survives untouched instead of being replaced by a bloated
/// one. Driven through the real acceptance path, not by asserting on the
/// constant.
#[test]
fn oversized_candidates_are_rejected_before_installation() {
    let (mut exec, out) = run_script(
        r#"
(set-logic QF_NRA)
(declare-fun x () Real)
(declare-fun y () Real)
(assert (= (* x x) (+ 1 (* y y))))
(assert (not (<= x 0)))
(check-sat)
"#,
    );
    assert_eq!(out[0], "sat");
    let x = exec.ctx.terms.mk_var("x", Sort::Real);
    let y = exec.ctx.terms.mk_var("y", Sort::Real);
    if let Some(model) = exec.last_model.as_mut() {
        let lra = model.lra_model.as_mut().expect("LRA model");
        lra.values.insert(y, BigRational::zero());
        lra.values.remove(&x);
    }
    exec.nra_algebraic_model.insert(x, sqrt_value(rat(2), 1));
    let before = exec.model();

    let mut values: DetHashMap<TermId, BigRational> = DetHashMap::default();
    values.insert(y, BigRational::zero());
    let plan = Plan {
        alpha: x,
        eqs: Vec::new(),
        solves: Vec::new(),
        free: vec![y],
        values,
        residual: None,
    };
    let huge = BigRational::new(BigInt::one() << 600u32, BigInt::from(3));
    assert!(rational_bits(&huge) > MAX_JOINT_CANDIDATE_BITS);
    assert!(
        !exec.try_joint_assignment(&plan, None, &huge, None),
        "an oversized proposal must be declined"
    );
    assert!(
        !exec.nra_algebraic_model.is_empty(),
        "a declined proposal must not have been installed"
    );
    assert_eq!(exec.model(), before, "declined => model byte-identical");
    // A chord-sized rational (the classification's worked CONVOI2 point) is
    // well inside the cap.
    assert!(rational_bits(&ratio(260, 521)) < MAX_JOINT_CANDIDATE_BITS);
}

/// An Int-sorted cluster partner must never be handed a non-integer value.
/// The whole-model assertion gate evaluates over `BigRational`, so `(> n 0)`
/// alone cannot distinguish `n = 3/2` from a legal positive integer.
#[test]
fn int_sorted_partner_is_rejected_unless_the_value_is_an_integer() {
    let (mut exec, out) = run_script(
        r#"
(set-logic QF_NRA)
(declare-fun skoS () Real)
(declare-fun skoC () Real)
(declare-fun n () Int)
(assert (= (* skoS skoS) (+ 1 (* skoC (* skoC (- 1))))))
(assert (not (<= skoS 0)))
(assert (not (<= skoC (- 1))))
(assert (not (<= 0 skoC)))
(assert (> n 0))
(check-sat)
"#,
    );
    assert_eq!(out[0], "sat");
    let s = exec.ctx.terms.mk_var("skoS", Sort::Real);
    let c = exec.ctx.terms.mk_var("skoC", Sort::Real);
    let n = exec.ctx.terms.mk_var("n", Sort::Int);

    if let Some(model) = exec.last_model.as_mut() {
        model.lia_model = None;
        let lra = model.lra_model.get_or_insert_with(|| ay_lra::LraModel {
            values: Default::default(),
        });
        lra.values.insert(c, ratio(-1, 2));
        lra.values.insert(n, BigRational::one());
        lra.values.remove(&s);
    }
    exec.nra_algebraic_model
        .insert(s, sqrt_value(ratio(3, 4), 1));
    exec.nra_algebraic_model.reset_print_refinement_attempted();
    let before = exec.model();

    let mut values: DetHashMap<TermId, BigRational> = DetHashMap::default();
    values.insert(c, ratio(-120, 241));
    values.insert(n, BigRational::one());
    let plan = Plan {
        alpha: s,
        eqs: Vec::new(),
        solves: Vec::new(),
        free: vec![c, n],
        values,
        residual: None,
    };

    // This exact point satisfies the Real constraints. The only invalid part
    // of the first proposal is the non-integral value for `n`.
    assert!(
        !exec.try_joint_assignment(&plan, Some(n), &ratio(209, 241), Some(&ratio(3, 2))),
        "a non-integer value for an Int-sorted partner must be declined"
    );
    assert!(!exec.nra_algebraic_model.is_empty());
    let printed = exec.model();
    assert_eq!(printed, before, "declined => model byte-identical");
    assert!(!printed.contains("(define-fun n () Int (/ 3 2))"));

    // The same rational point with an integral Int coordinate remains valid.
    assert!(
        exec.try_joint_assignment(&plan, Some(n), &ratio(209, 241), Some(&BigRational::one())),
        "an integral value for the Int-sorted partner must remain accepted"
    );
    assert!(exec.nra_algebraic_model.is_empty());
    let sv = rational_of(&exec, s);
    let cv = rational_of(&exec, c);
    assert_eq!(&sv * &sv + &cv * &cv, BigRational::one());
    assert!(exec.model().contains("(define-fun n () Int 1)"));
}
