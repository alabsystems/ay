// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Same-solve advice, legacy compatibility, and original-model rejection controls.
use super::*;

fn reset() {
    OBSERVATIONS.with(|o| o.set((0, 0)));
}

fn observations() -> (usize, usize) {
    OBSERVATIONS.with(std::cell::Cell::get)
}

fn fixture() -> (Model, [Col; 3]) {
    let mut model = Model::new();
    let x = model.add_col(-8., 8.);
    let y = model.add_col(-4., 4.);
    let z = model.add_col(2., 2.);
    model.add_row(4099., f64::INFINITY, &[(x, 4096.), (y, 1.)]);
    model.add_row(
        3. - 2. / 4096.,
        3. - 2. / 4096.,
        &[(y, 1.), (z, -1. / 4096.)],
    );
    (model, [x, y, z])
}

fn candidate(values: Vec<f64>, duals: Vec<f64>) -> Candidate {
    Candidate {
        basis: Vec::new(),
        at: Vec::new(),
        values,
        duals,
        farkas: Vec::new(),
        farkas_verified: false,
        status: SimplexStatus::Optimal,
    }
}

#[test]
fn float_advice_one_solve_returns_original_scaled_columns_and_same_candidate_duals() {
    let _scaling = crate::tune::activate_caller(
        crate::tune::Profile::EMPTY.with(crate::tune::Knob::Scale, crate::tune::Setting::Count(1)),
    );
    let (model, [x, _, _]) = fixture();
    let opts = SolveOpts::new();
    let mut session = LpSession::new(&model, &opts).expect("valid continuous model");
    assert!(session
        .float_lp(&[(x.0, 1.)], Sense::Minimize)
        .expect("lowering")
        .scaled());
    reset();
    let advice = session
        .float_advice_for_expr(&[(x, 1.)], Sense::Minimize)
        .expect("valid objective")
        .expect("small float optimum");
    assert_eq!(
        observations(),
        (1, 1),
        "one real solve and one original-prefix copy"
    );
    let primal = advice.primal.as_deref().expect("finite original columns");
    assert_eq!(
        primal.len(),
        3,
        "not the five structural-plus-logical columns"
    );
    for (&actual, expected) in primal.iter().zip([1., 3., 2.]) {
        assert!(
            (actual - expected).abs() < 1e-9,
            "original frame: {primal:?}"
        );
    }
    assert_eq!(advice.duals.len(), 2);
    assert!(advice.duals.iter().all(|v| v.is_finite()));
    assert!(
        session.lp.is_none(),
        "advice cannot materialize the exact fallback"
    );
    // Exact checking is a separate operation; it is not furnished by the API.
    model
        .check_point(&[1, 3, 2].map(|v| BigRational::from_integer(v.into())))
        .expect("independent exact original-model witness");
}

#[test]
fn float_advice_legacy_duals_match_both_senses_without_any_primal_copy() {
    let (model, [x, _, _]) = fixture();
    let opts = SolveOpts::new();
    for sense in [Sense::Minimize, Sense::Maximize] {
        let mut old = LpSession::new(&model, &opts).expect("old session");
        reset();
        let duals = old
            .float_dual_for_expr(&[(x, 1.)], sense)
            .expect("valid old objective")
            .expect("old float optimum");
        assert_eq!(
            observations(),
            (1, 0),
            "old path never copies primal columns"
        );
        let mut new = LpSession::new(&model, &opts).expect("advice session");
        reset();
        let advice = new
            .float_advice_for_expr(&[(x, 1.)], sense)
            .expect("valid new objective")
            .expect("new float optimum");
        assert_eq!(observations(), (1, 1));
        assert_eq!(
            duals.iter().map(|v| v.to_bits()).collect::<Vec<_>>(),
            advice.duals.iter().map(|v| v.to_bits()).collect::<Vec<_>>()
        );
        let expected = if sense == Sense::Minimize { 1. } else { 8. };
        assert!((advice.primal.expect("finite prefix")[x.index()] - expected).abs() < 1e-9);
        assert!(old.lp.is_none() && new.lp.is_none());
    }
}

#[test]
fn float_advice_narrowed_bounds_change_new_point_without_mutating_owned_old_advice() {
    let (model, [x, _, _]) = fixture();
    let mut session = LpSession::new(&model, &SolveOpts::new()).expect("session");
    reset();
    let first = session
        .float_advice_for_expr(&[(x, 1.)], Sense::Minimize)
        .expect("objective")
        .expect("first optimum");
    assert!(session.narrow_col_bounds(x, 1.5, 2.));
    let second = session
        .float_advice_for_expr(&[(x, 1.)], Sense::Minimize)
        .expect("objective")
        .expect("narrowed optimum");
    assert_eq!(
        observations(),
        (2, 2),
        "one solve for each explicit call, no hidden retry"
    );
    drop(session);
    assert!((first.primal.expect("owned first point")[x.index()] - 1.).abs() < 1e-9);
    assert!((second.primal.expect("owned second point")[x.index()] - 1.5).abs() < 1e-9);
}

#[test]
fn float_advice_invalid_empty_and_disabled_forms_keep_legacy_validation_order() {
    let (model, [x, _, _]) = fixture();
    let opts = SolveOpts::new().with_engine(crate::EngineEconomics::new().with_float_lane(false));
    let mut session = LpSession::new(&model, &opts).expect("disabled session");
    reset();
    for weight in [f64::NAN, f64::INFINITY, f64::NEG_INFINITY] {
        assert!(session
            .float_advice_for_expr(&[(x, weight)], Sense::Minimize)
            .is_err());
        assert!(session
            .float_dual_for_expr(&[(x, weight)], Sense::Minimize)
            .is_err());
    }
    for sense in [Sense::Minimize, Sense::Maximize] {
        assert!(session
            .float_advice_for_expr(&[(Col(99), 1.)], sense)
            .is_err());
        assert!(session
            .float_advice_for_expr(&[], sense)
            .expect("empty form")
            .is_none());
        assert!(session
            .float_advice_for_expr(&[(x, 1.)], sense)
            .expect("disabled lane")
            .is_none());
    }
    assert_eq!(observations(), (0, 0));
    assert!(session.lp.is_none());
}

#[test]
fn float_advice_actual_infeasible_and_unbounded_models_decline_without_exact_claim() {
    let mut infeasible = Model::new();
    let x = infeasible.add_col(0., 1.);
    infeasible.add_row(2., f64::INFINITY, &[(x, 1.)]);
    let mut unbounded = Model::new();
    let y = unbounded.add_col(0., f64::INFINITY);
    unbounded.add_row(0., f64::INFINITY, &[(y, 1.)]);
    for (model, col, weight) in [(&infeasible, x, 1.), (&unbounded, y, -1.)] {
        let mut session = LpSession::new(model, &SolveOpts::new()).expect("valid model");
        reset();
        assert!(session
            .float_advice_for_expr(&[(col, weight)], Sense::Minimize)
            .expect("valid objective")
            .is_none());
        assert_eq!(observations(), (1, 0));
        assert!(
            session.lp.is_none(),
            "None is a decline, not an exact infeasibility verdict"
        );
    }
}

#[test]
fn float_advice_expired_original_deadline_never_captures_or_restarts_the_exact_rim() {
    let (model, [x, _, _]) = fixture();
    let expired = Instant::now()
        .checked_sub(Duration::from_secs(1))
        .expect("test clock");
    let opts = SolveOpts::new().with_deadline(expired);
    let mut session = LpSession::new(&model, &opts).expect("session");
    reset();
    let advice = session
        .float_advice_for_expr(&[(x, 1.)], Sense::Minimize)
        .expect("valid objective");
    assert!(advice.is_none_or(|a| a.primal.is_none()));
    let (solves, copies) = observations();
    assert!(solves <= 1);
    assert_eq!(copies, 0);
    assert!(session.lp.is_none());
    assert!(original_prefix(&[1.], 1, Some(expired)).is_none());
    assert_eq!(observations().1, 0);
}

#[test]
fn float_advice_prefix_excludes_nonfinite_logicals_and_moves_raw_dual_capacity_unchanged() {
    let mut values = Vec::with_capacity(128);
    values.extend([-0., 1.25, f64::NAN, f64::INFINITY]);
    let mut duals = Vec::with_capacity(64);
    duals.extend([0.25, -0.5]);
    let pointer = duals.as_ptr();
    let capacity = duals.capacity();
    reset();
    let advice = FloatLpAdvice::from_candidate(candidate(values, duals), 2, None);
    assert_eq!(observations(), (0, 1));
    let primal = advice
        .primal
        .expect("only original finite prefix is scanned");
    assert_eq!(primal.len(), 2);
    assert_eq!(std::mem::size_of_val(primal.as_ref()), 16);
    assert_eq!(primal[0].to_bits(), (-0.0_f64).to_bits());
    assert_eq!(primal[1], 1.25);
    assert_eq!(advice.duals.as_ptr(), pointer, "move, not a dual clone");
    assert_eq!(advice.duals.capacity(), capacity);
}

#[test]
fn float_advice_malformed_original_prefix_retains_duals_without_repair_or_second_solve() {
    for values in [vec![1.], vec![1., f64::NAN], vec![f64::INFINITY, 2.]] {
        let duals = vec![f64::NAN, -0.0];
        reset();
        let advice = FloatLpAdvice::from_candidate(candidate(values, duals), 2, None);
        assert!(advice.primal.is_none());
        assert!(
            advice.duals[0].is_nan(),
            "raw dual semantics are not tightened by primal capture"
        );
        assert_eq!(advice.duals[1].to_bits(), (-0.0_f64).to_bits());
        assert_eq!(observations(), (0, 0));
    }
}

#[test]
fn float_advice_finite_hint_is_not_clamped_or_promoted_to_a_model_witness() {
    let mut model = Model::new();
    let _x = model.add_col(0., 1.);
    let outside = 1.0_f64.next_up();
    let advice = FloatLpAdvice::from_candidate(candidate(vec![outside], vec![]), 1, None);
    let value = advice
        .primal
        .expect("finite advice is copied without a feasibility claim")[0];
    assert_eq!(value.to_bits(), outside.to_bits());
    let rational = BigRational::from_float(value).expect("finite rational");
    assert!(
        model.check_point(&[rational]).is_err(),
        "independent checker rejects the raw hint"
    );
}

#[test]
fn float_advice_actual_rounded_proxy_point_requires_original_model_rechecking() {
    let mut model = Model::new();
    let x = model.add_col(0., 2.);
    let row = model.add_row(f64::NEG_INFINITY, 1., &[(x, 1.)]);
    // The float proxy says x <= 1; the original side-store says 2x <= 1.
    model.record_inexact_row_coeff(row, x.0, BigRational::from_integer(2.into()));
    let mut session = LpSession::new(&model, &SolveOpts::new()).expect("valid side-store model");
    reset();
    let advice = session
        .float_advice_for_expr(&[(x, -1.)], Sense::Minimize)
        .expect("valid objective")
        .expect("rounded float proxy settles");
    assert_eq!(observations(), (1, 1));
    let primal = advice.primal.expect("finite float hint");
    assert!((primal[0] - 1.).abs() < 1e-9);
    let exact_point = primal
        .iter()
        .map(|v| BigRational::from_float(*v).expect("finite"))
        .collect::<Vec<_>>();
    assert!(
        model.check_point(&exact_point).is_err(),
        "float status and finiteness prove no witness"
    );
    model
        .check_point(&[BigRational::new(1.into(), 2.into())])
        .expect("actual original feasible endpoint");
    assert!(
        session.lp.is_none(),
        "the raw advice path never adjudicates an exact verdict"
    );
}
