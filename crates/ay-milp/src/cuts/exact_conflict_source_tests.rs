// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{exact, separate_clique, separate_odd_cycle, violation, Col, Cut, Model};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};

fn rational(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(numerator.into(), denominator.into())
}

fn k56() -> (BigInt, f64) {
    (BigInt::from(1u8) << 56usize, 2.0f64.powi(56))
}

fn assert_cut_at(cut: &Cut, point: &[BigRational]) {
    let activity = cut
        .coeffs
        .iter()
        .fold(BigRational::zero(), |sum, &(column, value)| {
            sum + exact(value).unwrap() * &point[column.index()]
        });
    if let Some(lower) = exact(cut.lb) {
        assert!(
            activity >= lower,
            "cut deletes authoritative feasible point {point:?}: {activity} < {lower}"
        );
    }
    if let Some(upper) = exact(cut.ub) {
        assert!(
            activity <= upper,
            "cut deletes authoritative feasible point {point:?}: {activity} > {upper}"
        );
    }
}

fn audit_binary(model: &Model, cuts: &[Cut], witness: &[BigRational]) {
    model.check_point(witness).unwrap();
    let mut feasible = 0usize;
    for code in 0..(1usize << model.num_cols()) {
        let point = (0..model.num_cols())
            .map(|column| BigRational::from_integer(BigInt::from((code >> column) & 1)))
            .collect::<Vec<_>>();
        if model.check_point(&point).is_err() {
            continue;
        }
        feasible += 1;
        for cut in cuts {
            assert_cut_at(cut, &point);
        }
    }
    assert!(
        feasible > 0,
        "the authoritative feasible-point census is empty"
    );
}

fn subnormal_source(columns: usize, upper_eighths: i64) -> (Model, Vec<Col>) {
    let raw = f64::from_bits(1);
    let quantum = BigRational::new(BigInt::one(), BigInt::one() << 1074usize);
    assert_eq!(exact(raw).unwrap(), quantum);
    let coefficient = &quantum * rational(5, 8);
    let upper = &quantum * rational(upper_eighths, 8);
    // Conversion is exercised in native tests, including subnormal
    // nearest rounding; it is not assumed from the source spelling.
    assert_eq!(coefficient.to_f64(), Some(raw));
    assert_eq!(upper.to_f64(), Some(raw));
    let mut model = Model::new();
    let cols = (0..columns)
        .map(|_| model.add_binary_col())
        .collect::<Vec<_>>();
    let edges = if columns == 2 { 1 } else { columns };
    for i in 0..edges {
        let next = (i + 1) % columns;
        let row = model.add_row(f64::NEG_INFINITY, raw, &[(cols[i], raw), (cols[next], raw)]);
        model.record_inexact_row_coeff(row, cols[i].0, coefficient.clone());
        model.record_inexact_row_coeff(row, cols[next].0, coefficient.clone());
        model.record_inexact_row_bound(row, false, upper.clone());
    }
    (model, cols)
}

#[test]
fn clique_upper_coefficient_override_preserves_every_exact_binary_point() {
    let (k, raw) = k56();
    let truth = BigRational::from_integer(&k - BigInt::from(2u8));
    assert_eq!(truth.to_f64(), Some(raw));
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    let row = model.add_row(f64::NEG_INFINITY, raw, &[(x, raw), (y, 1.0)]);
    model.record_inexact_row_coeff(row, x.0, truth);
    let cuts = separate_clique(&model, &[0.75, 0.75], model.num_rows());
    audit_binary(&model, &cuts, &[BigRational::one(), BigRational::one()]);
}

#[test]
fn clique_lower_coefficient_override_preserves_every_exact_binary_point() {
    let (k, raw) = k56();
    let truth = BigRational::from_integer(-(&k - BigInt::from(2u8)));
    assert_eq!(truth.to_f64(), Some(-raw));
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    let row = model.add_row(-raw, f64::INFINITY, &[(x, -raw), (y, -1.0)]);
    model.record_inexact_row_coeff(row, x.0, truth);
    let cuts = separate_clique(&model, &[0.75, 0.75], model.num_rows());
    audit_binary(&model, &cuts, &[BigRational::one(), BigRational::one()]);
}

#[test]
fn clique_upper_bound_override_preserves_every_exact_binary_point() {
    let (k, raw) = k56();
    let truth = BigRational::from_integer(&k + BigInt::from(2u8));
    assert_eq!(truth.to_f64(), Some(raw));
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    let row = model.add_row(f64::NEG_INFINITY, raw, &[(x, raw), (y, 1.0)]);
    model.record_inexact_row_bound(row, false, truth);
    let cuts = separate_clique(&model, &[0.75, 0.75], model.num_rows());
    audit_binary(&model, &cuts, &[BigRational::one(), BigRational::one()]);
}

#[test]
fn clique_lower_bound_override_preserves_every_exact_binary_point() {
    let (k, raw) = k56();
    let truth = BigRational::from_integer(-(&k + BigInt::from(2u8)));
    assert_eq!(truth.to_f64(), Some(-raw));
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    let row = model.add_row(-raw, f64::INFINITY, &[(x, -raw), (y, -1.0)]);
    model.record_inexact_row_bound(row, true, truth);
    let cuts = separate_clique(&model, &[0.75, 0.75], model.num_rows());
    audit_binary(&model, &cuts, &[BigRational::one(), BigRational::one()]);
}

#[test]
fn clique_subnormal_packing_override_preserves_every_exact_binary_point() {
    let (model, _) = subnormal_source(2, 11);
    let cuts = separate_clique(&model, &[0.75, 0.75], model.num_rows());
    audit_binary(&model, &cuts, &[BigRational::one(), BigRational::one()]);
}

#[test]
fn odd_cycle_subnormal_override_preserves_every_exact_binary_point() {
    let (model, _) = subnormal_source(5, 11);
    let cuts = separate_odd_cycle(&model, &[0.5; 5], model.num_rows());
    audit_binary(&model, &cuts, &vec![BigRational::one(); 5]);
}

#[test]
fn clique_true_subnormal_packing_still_separates_with_exact_overrides() {
    let (model, _) = subnormal_source(2, 9);
    let cuts = separate_clique(&model, &[0.75, 0.75], model.num_rows());
    assert!(
        cuts.iter().any(|cut| {
            cut.coeffs.len() == 2
                && cut.ub == 1.0
                && cut.coeffs.iter().all(|&(_, value)| value == 1.0)
                && violation(cut, &[0.75, 0.75]) > 0.49
        }),
        "correctly rounded advice must not disable genuine exact packing"
    );
    audit_binary(&model, &cuts, &[BigRational::one(), BigRational::zero()]);
}

#[test]
fn odd_cycle_true_subnormal_packing_still_separates_with_exact_overrides() {
    let (model, _) = subnormal_source(5, 9);
    let cuts = separate_odd_cycle(&model, &[0.5; 5], model.num_rows());
    assert!(
        cuts.iter().any(|cut| {
            cut.coeffs.len() == 5
                && cut.ub == 2.0
                && cut.coeffs.iter().all(|&(_, value)| value == 1.0)
                && violation(cut, &[0.5; 5]) > 0.49
        }),
        "the genuine exact five-hole must remain nonempty"
    );
    audit_binary(&model, &cuts, &vec![BigRational::zero(); 5]);
}

#[test]
fn clique_negative_continuous_floor_override_preserves_exact_corner() {
    let (k, raw) = k56();
    let truth = BigRational::from_integer(-(&k + BigInt::from(2u8)));
    assert_eq!(truth.to_f64(), Some(-raw));
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    let z = model.add_col(0.0, 1.0);
    let row = model.add_row(f64::NEG_INFINITY, 0.0, &[(x, raw), (y, 1.0), (z, -raw)]);
    model.record_inexact_row_coeff(row, z.0, truth);
    let point = vec![BigRational::one(); 3];
    model.check_point(&point).unwrap();
    let cuts = separate_clique(&model, &[0.75, 0.75, 1.0], model.num_rows());

    // This is one exact continuous corner, not a complete enumeration
    // or an interval proof for all continuous points.
    for cut in &cuts {
        assert_cut_at(cut, &point);
    }
}

#[test]
fn normal_root_lp_clique_preserves_the_optimal_binary_witness() {
    let source = include_str!("../../tests/fixtures/exact_conflict_root.mps");
    let integer = crate::read_mps(source).unwrap().model;
    let relaxed = source
        .replace("BV BND X", "UP BND X 1")
        .replace("BV BND Y", "UP BND Y 1");
    let lp = crate::read_mps(&relaxed).unwrap().model;
    let opts = crate::SolveOpts::new().with_time_limit(std::time::Duration::from_secs(5));
    let mut session = crate::LpSession::new(&lp, &opts).unwrap();
    let crate::Outcome::Optimal { model_values, .. } = session.optimize_model_objective().unwrap()
    else {
        panic!("expected the bounded relaxation optimum");
    };
    // t <= x, t <= y and x+y+2t <= 3 imply 4t <= 3. Equality
    // forces all three coordinates to 3/4.
    assert_eq!(model_values, vec![rational(3, 4); 3]);
    lp.check_point(&model_values).unwrap();
    let point = model_values
        .iter()
        .map(|v| v.to_f64().unwrap())
        .collect::<Vec<_>>();
    let witness = [BigRational::one(), BigRational::one(), rational(1, 2)];
    integer.check_point(&witness).unwrap();
    for cut in separate_clique(&integer, &point, integer.num_rows()) {
        assert_cut_at(&cut, &witness);
    }
}
