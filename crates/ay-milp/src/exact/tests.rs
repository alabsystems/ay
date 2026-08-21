// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::construction::upper_crash_mask;
use super::*;
use crate::model::Sense;

fn budget() -> Budget {
    Budget {
        deadline: None,
        max_iters: 10_000,
    }
}

/// No logical starts outside its bounds ⇔ `make_feasible` returns without
/// pivoting once.
fn phase_one_is_empty(lp: &ExactLp) -> bool {
    lp.rows
        .iter()
        .all(|row| !lp.below_lower(row.basic as usize) && !lp.above_upper(row.basic as usize))
}

fn unit_objective(n: u32) -> Vec<(u32, Rational)> {
    (0..n).map(|j| (j, Rational::new(1, 1))).collect()
}

/// COVERING — the class the crash exists for: every column tips to its
/// upper bound, which leaves Phase I with nothing to repair, and the
/// optimum is unchanged by the different starting point.
#[test]
fn covering_columns_crash_and_leave_phase_one_empty() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 1.0);
    let y = m.add_col(0.0, 1.0);
    let z = m.add_col(0.0, 1.0);
    m.add_row(1.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
    m.add_row(1.0, f64::INFINITY, &[(y, 1.0), (z, 1.0)]);
    assert_eq!(upper_crash_mask(&m, None).unwrap(), vec![true, true, true]);
    let mut lp = ExactLp::new(&m);
    assert!(phase_one_is_empty(&lp));
    // min x+y+z over that cover is 1 (y = 1), crash or no crash.
    let LpOptimum::Optimal { value, .. } = lp.minimize(&unit_objective(3), &budget()) else {
        panic!("covering LP must be optimal");
    };
    assert_eq!(value, BigRational::from_integer(1.into()));
}

/// PACKING — `gain` is 0 and `harm` is not, so nothing tips and the start
/// is the historical all-at-lower one.
#[test]
fn packing_columns_do_not_crash() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 1.0);
    let y = m.add_col(0.0, 1.0);
    m.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, 1.0)]);
    assert_eq!(upper_crash_mask(&m, None).unwrap(), vec![false, false]);
    let lp = ExactLp::new(&m);
    assert!(lp.values[..2].iter().all(Rational::is_zero));
}

/// SET PARTITIONING — a row with both bounds finite charges at least as
/// much harm as it credits gain, so an equality model can never tip a
/// column. This is what keeps `air03`/`nw04`-shaped models on their old
/// start.
#[test]
fn equality_rows_never_crash() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 1.0);
    let y = m.add_col(0.0, 1.0);
    let z = m.add_col(0.0, 1.0);
    m.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
    m.add_row(1.0, 1.0, &[(y, 1.0), (z, 1.0)]);
    assert_eq!(
        upper_crash_mask(&m, None).unwrap(),
        vec![false, false, false]
    );
}

/// A start that is already feasible is left alone: with nothing short,
/// nothing has anything to gain, so no column tips and the starting vertex
/// — which is what a degenerate LP's reported optimum hangs on — does not
/// move.
#[test]
fn a_feasible_start_is_not_disturbed() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 1.0);
    let y = m.add_col(0.0, 1.0);
    // Covering-shaped (no finite row upper bound) but satisfied at x=y=0.
    m.add_row(0.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
    assert_eq!(upper_crash_mask(&m, None).unwrap(), vec![false, false]);
    let lp = ExactLp::new(&m);
    assert!(lp.values[..2].iter().all(Rational::is_zero));
}

/// An unbounded column has no upper bound to crash to; a fixed column has
/// nowhere to move. Neither is a candidate.
#[test]
fn infinite_and_empty_spans_are_not_candidates() {
    let mut m = Model::new();
    let free = m.add_col(0.0, f64::INFINITY);
    let fixed = m.add_col(1.0, 1.0);
    let boxed = m.add_col(0.0, 1.0);
    m.add_row(
        5.0,
        f64::INFINITY,
        &[(free, 1.0), (fixed, 1.0), (boxed, 1.0)],
    );
    assert_eq!(
        upper_crash_mask(&m, None).unwrap(),
        vec![false, false, true]
    );
}

/// The crash is a STARTING POINT, not a verdict: an infeasible covering
/// model is still refuted, with the same exact answer either way.
#[test]
fn crash_does_not_change_an_infeasible_verdict() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 1.0);
    m.add_row(2.0, f64::INFINITY, &[(x, 1.0)]);
    assert_eq!(upper_crash_mask(&m, None).unwrap(), vec![true]);
    let mut lp = ExactLp::new(&m);
    assert!(matches!(
        lp.make_feasible(&budget()),
        LpFeasibility::Infeasible(_)
    ));
}

// ---- the representation switch ----------------------------------------

/// A deterministic LP that is wide enough for a basis with `|det B| > 1`
/// and awkward enough (fractional coefficients, mixed row senses) that
/// both representations have real work to do.
fn switch_model() -> Model {
    let mut m = Model::new();
    let cols: Vec<Col> = (0..9).map(|_| m.add_col(0.0, 7.0)).collect();
    // A deterministic LCG, so the instance is a fixed one.
    let mut s: u64 = 0x5eed;
    let mut next = || {
        s = s.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        (s >> 33) as u32
    };
    for r in 0..7 {
        let terms: Vec<(Col, f64)> = cols
            .iter()
            .map(|&c| (c, f64::from(next() % 17) / 4.0 - 2.0))
            .filter(|&(_, a)| a != 0.0)
            .collect();
        let b = f64::from(next() % 11) + 3.0;
        if r % 2 == 0 {
            m.add_row(f64::NEG_INFINITY, b, &terms);
        } else {
            m.add_row(-b, f64::INFINITY, &terms);
        }
    }
    let obj: Vec<(Col, f64)> = cols
        .iter()
        .map(|&c| (c, f64::from(next() % 9) - 4.0))
        .collect();
    m.set_objective(&obj, Sense::Minimize);
    m
}

fn objective_terms(model: &Model) -> Vec<(u32, Rational)> {
    (0..model.num_cols() as u32)
        .filter_map(|j| {
            let a = model.obj_coeff(Col(j));
            let e = model.obj_coeff_exact_at(j, a);
            (!e.is_zero()).then(|| (j, Rational::from_big(e)))
        })
        .collect()
}

/// Solve `model` with the policy pinned to `force` (0 auto, 1 never
/// switch, 2 switch at the first pivot that can) and return the verdict
/// with the form it ended in.
fn solve_forced(model: &Model, force: u8) -> (BigRational, Vec<Multiplier>, Form, u64) {
    probe::set_force(force);
    let mut lp = ExactLp::new(model);
    let out = lp.minimize(&objective_terms(model), &budget());
    probe::set_force(0);
    let LpOptimum::Optimal { value, multipliers } = out else {
        panic!("bounded LP must be optimal");
    };
    (value, multipliers, lp.form, lp.det.to_big().numer().bits())
}

/// THE PROPERTY THE SWITCH IS FOR: the two representations are two
/// spellings of the same tableau, so the optimum is BIT-IDENTICAL and the
/// dual evidence is identical multiplier for multiplier — not equal to
/// within a print, equal as exact rationals.
#[test]
fn every_arm_returns_the_same_exact_optimum_and_the_same_multipliers() {
    let m = switch_model();
    let (v_auto, mult_auto, _, _) = solve_forced(&m, 0);
    let (v_red, mult_red, form_red, _) = solve_forced(&m, 1);
    let (v_ff, mult_ff, form_ff, det_bits) = solve_forced(&m, 2);
    assert_eq!(form_red, Form::Reduced, "arm 1 must stay reduced");
    assert_eq!(
        form_ff,
        Form::FractionFree,
        "arm 2 must convert (|det B| is {det_bits} bits)"
    );
    assert_eq!(
        v_red, v_ff,
        "the two representations disagree on the optimum"
    );
    assert_eq!(v_auto, v_red, "the policy changed the optimum");
    assert_eq!(mult_red.len(), mult_ff.len());
    for (a, b) in mult_red.iter().zip(&mult_ff) {
        assert_eq!(a.fact, b.fact, "multiplier facts diverged");
        assert_eq!(a.coeff, b.coeff, "multiplier coefficients diverged");
    }
    assert_eq!(mult_auto.len(), mult_red.len());
}

/// The certificate the fraction-free arm hands out re-checks against the
/// MODEL, by the code a consumer would run — the switch does not get to be
/// believed on its own say-so.
#[test]
fn a_converted_solve_still_produces_a_checkable_optimality_certificate() {
    let m = switch_model();
    let (value, multipliers, form, _) = solve_forced(&m, 2);
    assert_eq!(form, Form::FractionFree);
    let cert = crate::cert::OptimalityCertificate {
        sense: Sense::Minimize,
        objective: (0..m.num_cols() as u32)
            .map(|j| (j, m.obj_coeff_exact_at(j, m.obj_coeff(Col(j)))))
            .filter(|(_, a)| !a.is_zero())
            .collect(),
        bound: value,
        multipliers,
    };
    cert.verify(&m).expect("optimality certificate re-checks");
}

/// An instance whose tableau never leaves the inline `i64` path never
/// converts — the policy's whole promise to the reduced class. `p0201`'s
/// shape in miniature: small integer coefficients, unit bounds.
#[test]
fn an_inline_tableau_is_never_converted() {
    let mut m = Model::new();
    let cols: Vec<Col> = (0..12).map(|_| m.add_col(0.0, 1.0)).collect();
    for r in 0..10 {
        let terms: Vec<(Col, f64)> = cols
            .iter()
            .enumerate()
            .filter(|(j, _)| (j + r) % 3 != 0)
            .map(|(j, &c)| (c, f64::from((j % 3) as i32) + 1.0))
            .collect();
        m.add_row(2.0, f64::INFINITY, &terms);
    }
    let obj: Vec<(Col, f64)> = cols.iter().map(|&c| (c, 1.0)).collect();
    m.set_objective(&obj, Sense::Minimize);
    let (_, _, form, _) = solve_forced(&m, 0);
    assert_eq!(form, Form::Reduced, "an all-inline solve must stay reduced");
}

/// A ROW THE TABLEAU HAS TO SCALE, refuted, with the certificate re-checked
/// by the independent public checker.
///
/// `1/3·x + 1/2·y >= 5` with `x, y ∈ [0, 1]` cannot hold. The row's
/// coefficients are not integers, so the tableau pivots on `λ_r·(a_r·x)`
/// and its logical variable's bound is `λ_r·5`, not `5` — and the
/// multiplier that reaches the certificate must be the one that refutes
/// the MODEL's row, not the scaled one. `verify` re-derives the
/// combination from the model alone, so it fails if the scale is not
/// undone. (`1.0/3.0` is a `f64`, so `λ_r` is the dyadic `2^54` that
/// literal really denotes, not 6 — which is the point: the rim scales the
/// row the model actually holds.)
#[test]
fn a_scaled_row_still_produces_a_checkable_refutation() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 1.0);
    let y = m.add_col(0.0, 1.0);
    m.add_row(5.0, f64::INFINITY, &[(x, 1.0 / 3.0), (y, 0.5)]);
    let mut lp = ExactLp::new(&m);
    assert_eq!(lp.row_scale.len(), 1);
    assert!(
        !is_unit(&lp.row_scale[0]),
        "a fractional row must be scaled"
    );
    let LpFeasibility::Infeasible(cert) = lp.make_feasible(&budget()) else {
        panic!("1/3 x + 1/2 y >= 5 is infeasible over the unit box");
    };
    cert.verify(&m).expect("Farkas certificate re-checks");
}

/// The same scaling, on the OPTIMALITY side: the dual multipliers have to
/// come back in the model's own units or the identity
/// `Σ coeff·oriented == objective − bound` does not close.
#[test]
fn a_scaled_row_still_produces_a_checkable_optimum() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 10.0);
    let y = m.add_col(0.0, 10.0);
    // min x + y subject to x/3 + y/2 >= 1  →  optimum 2 (y = 2).
    m.add_row(1.0, f64::INFINITY, &[(x, 1.0 / 3.0), (y, 0.5)]);
    let mut lp = ExactLp::new(&m);
    let LpOptimum::Optimal { value, multipliers } = lp.minimize(&unit_objective(2), &budget())
    else {
        panic!("bounded covering LP must be optimal");
    };
    assert_eq!(value, BigRational::from_integer(2.into()));
    let cert = crate::cert::OptimalityCertificate {
        sense: Sense::Minimize,
        objective: vec![
            (0, BigRational::from_integer(1.into())),
            (1, BigRational::from_integer(1.into())),
        ],
        bound: value,
        multipliers,
    };
    cert.verify(&m).expect("optimality certificate re-checks");
}

/// An integer-coefficient model is left at `λ = 1`, so nothing about its
/// certificates moves — the property that makes the scaling inert on the
/// corpus this was measured on (`dcmulti` and `p0201`: 0 non-integral rows
/// out of 290 and 133).
#[test]
fn an_integral_model_is_not_scaled() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 1.0);
    let y = m.add_col(0.0, 1.0);
    m.add_row(1.0, f64::INFINITY, &[(x, 2.0), (y, 3.0)]);
    m.add_row(f64::NEG_INFINITY, 4.0, &[(x, 1.0), (y, -7.0)]);
    let lp = ExactLp::new(&m);
    assert!(lp.row_scale.iter().all(is_unit));
    assert!(lp.rows.iter().all(|r| is_unit(&r.den)));
    assert!(lp.convertible);
}

/// A row the scaling cannot integralise on the inline path is left exactly
/// as the rim has always built it, and LOCKS the solve to the reduced
/// form — the switch's precondition (an integer matrix, so that `det` is a
/// determinant of one) is gone, so the switch is gone with it.
#[test]
fn a_row_the_scale_would_widen_locks_the_solve_to_the_reduced_form() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 1.0);
    let y = m.add_col(0.0, 1.0);
    // 1/(2^53) needs a 53-bit lambda, and 3^33 against it leaves i64.
    m.add_row(
        1.0,
        f64::INFINITY,
        &[(x, 2f64.powi(-53)), (y, 3f64.powi(33))],
    );
    let lp = ExactLp::new(&m);
    assert!(!lp.convertible, "the guard must decline this row");
    assert!(lp.row_scale.iter().all(is_unit), "and leave it unscaled");
}
