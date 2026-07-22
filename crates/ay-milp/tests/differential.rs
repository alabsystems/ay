// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential testing: the exact rim vs the ay-dpll smt lane on random
//! small LPs. The two lanes are independent implementations (a fresh
//! bounded-variable simplex vs the CDCL(T)+LRA stack), so agreement is a
//! strong check on both — the in-crate analog of the downstream optimization consumer's mip-diff gate.

#![cfg(feature = "smt")]

use ay_milp::{BabSession, LpSession, Model, Outcome, Sense, SolveOpts};
use num_rational::BigRational;
use proptest::prelude::*;
use proptest::test_runner::TestCaseResult;

/// A compact random LP description: small integer data keeps optima exact
/// and human-debuggable.
#[derive(Debug, Clone)]
struct RandomLp {
    /// (lb, ub) per column, from a small menu including one-sided boxes.
    cols: Vec<(f64, f64)>,
    /// (lb, ub, coeffs) per row.
    rows: Vec<(f64, f64, Vec<(usize, f64)>)>,
    /// Objective coefficients (same arity as cols).
    obj: Vec<f64>,
    maximize: bool,
}

fn bound_menu() -> impl Strategy<Value = (f64, f64)> {
    prop_oneof![
        Just((0.0, 1.0)),
        Just((-1.0, 1.0)),
        Just((0.0, 4.0)),
        Just((f64::NEG_INFINITY, 2.0)),
        Just((-3.0, f64::INFINITY)),
        Just((0.0, 0.0)),
    ]
}

fn row_bound_menu() -> impl Strategy<Value = (f64, f64)> {
    prop_oneof![
        Just((f64::NEG_INFINITY, 2.0)),
        Just((1.0, f64::INFINITY)),
        Just((0.0, 3.0)),
        Just((1.0, 1.0)),
        Just((-2.0, 2.0)),
    ]
}

fn random_lp() -> impl Strategy<Value = RandomLp> {
    (2usize..=5, 1usize..=4).prop_flat_map(|(ncols, nrows)| {
        let cols = prop::collection::vec(bound_menu(), ncols);
        let coeff = prop_oneof![Just(-2.0), Just(-1.0), Just(0.5), Just(1.0), Just(2.0)];
        let row = (
            row_bound_menu(),
            prop::collection::vec((0..ncols, coeff.clone()), 1..=ncols),
        )
            .prop_map(|((lb, ub), coeffs)| (lb, ub, coeffs));
        let rows = prop::collection::vec(row, nrows);
        let obj = prop::collection::vec(
            prop_oneof![Just(-1.0), Just(0.0), Just(1.0), Just(2.0)],
            ncols,
        );
        (cols, rows, obj, any::<bool>()).prop_map(|(cols, rows, obj, maximize)| RandomLp {
            cols,
            rows,
            obj,
            maximize,
        })
    })
}

/// Build the model; `with_dummy_binary` appends an unconstrained binary
/// column untouched by rows/objective, which routes BabSession through the
/// smt lane without changing the LP.
fn build(lp: &RandomLp, with_dummy_binary: bool) -> Model {
    let mut m = Model::new();
    let cols: Vec<_> = lp.cols.iter().map(|&(lb, ub)| m.add_col(lb, ub)).collect();
    if with_dummy_binary {
        let _ = m.add_binary_col();
    }
    for (lb, ub, coeffs) in &lp.rows {
        let terms: Vec<_> = coeffs.iter().map(|&(c, a)| (cols[c], a)).collect();
        m.add_row(*lb, *ub, &terms);
    }
    let obj: Vec<_> = lp
        .obj
        .iter()
        .enumerate()
        .map(|(i, &a)| (cols[i], a))
        .collect();
    let sense = if lp.maximize {
        Sense::Maximize
    } else {
        Sense::Minimize
    };
    m.set_objective(&obj, sense);
    m
}

/// Check every model-bearing outcome against the exact model it came from.
///
/// The SMT-routing model intentionally has one extra dummy binary column, so
/// lane equivalence is about status and objective value, not equal vector
/// arity or an identical (potentially non-unique) primal point. Each lane must
/// nevertheless return exactly one value per column in *its own* model, and
/// that point must be feasible and attain any claimed optimum.
fn check_outcome_model(model: &Model, outcome: &Outcome) -> TestCaseResult {
    let (values, claimed_value) = match outcome {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => (Some(model_values.as_slice()), Some(value)),
        Outcome::Feasible { model_values, .. } => (Some(model_values.as_slice()), None),
        _ => (None, None),
    };
    if let Some(values) = values {
        prop_assert_eq!(
            values.len(),
            model.num_cols(),
            "model vector must have exactly one value per column"
        );
        prop_assert!(
            model.check_point(values).is_ok(),
            "lane returned an infeasible model point: {values:?}"
        );
        if let Some(claimed_value) = claimed_value {
            prop_assert_eq!(
                model.objective_value_at(values),
                claimed_value.clone(),
                "optimal model must attain its claimed objective value"
            );
        }
    }
    Ok(())
}

/// An explicitly set zero-coefficient objective is still an optimization
/// problem. `Model::has_objective` records that API distinction, so every
/// optimization entry point must prove the constant optimum instead of
/// silently degrading the request to a feasibility check.
#[test]
fn explicit_zero_objective_preserves_optimization_semantics_and_model_arity() {
    let lp = RandomLp {
        cols: vec![(0.0, 1.0), (0.0, 1.0)],
        rows: vec![(f64::NEG_INFINITY, 2.0, vec![(0, -2.0)])],
        obj: vec![0.0, 0.0],
        maximize: false,
    };
    let exact_model = build(&lp, false);
    let smt_model = build(&lp, true);
    assert_eq!(exact_model.num_cols(), 2);
    assert_eq!(smt_model.num_cols(), 3, "SMT routing adds one dummy binary");

    let mut explicit_lp = LpSession::new(&exact_model, &SolveOpts::new()).unwrap();
    match explicit_lp.optimize_model_objective().unwrap() {
        Outcome::Optimal {
            value,
            model_values,
            cert: Some(cert),
        } => {
            assert_eq!(value, BigRational::from_integer(0.into()));
            assert_eq!(model_values.len(), exact_model.num_cols());
            exact_model.check_point(&model_values).unwrap();
            cert.verify(&exact_model).unwrap();
        }
        other => {
            panic!("explicit zero-objective optimization must prove Optimal(0), got {other:?}")
        }
    }

    let mut exact_session = BabSession::new(exact_model.clone(), &SolveOpts::new()).unwrap();
    let mut smt_session = BabSession::new(smt_model.clone(), &SolveOpts::new()).unwrap();
    for (model, outcome) in [
        (&exact_model, exact_session.check().unwrap()),
        (&smt_model, smt_session.check().unwrap()),
    ] {
        match outcome {
            Outcome::Optimal {
                value,
                model_values,
                cert,
            } => {
                assert_eq!(value, BigRational::from_integer(0.into()));
                assert_eq!(model_values.len(), model.num_cols());
                model.check_point(&model_values).unwrap();
                assert_eq!(model.objective_value_at(&model_values), value);
                if let Some(cert) = cert {
                    cert.verify(model).unwrap();
                }
            }
            other => panic!("explicit zero objective must be Optimal(0), got {other:?}"),
        }
    }
}

/// A Boolean 0/1 disjunction makes ay-dpll's standalone LRA simplex
/// inapplicable. The MILP adapter must still prove the optimum, rather than
/// falling into the bounded 128-round Real improvement crawl and returning
/// `unknown`.
#[test]
fn bounded_objective_with_dummy_binary_is_optimized_exactly() {
    let lp = RandomLp {
        cols: vec![(0.0, 1.0), (-1.0, 1.0), (0.0, 4.0)],
        rows: vec![
            (0.0, 3.0, vec![(0, -2.0)]),
            (f64::NEG_INFINITY, 2.0, vec![(1, -2.0), (2, -2.0)]),
            (0.0, 3.0, vec![(0, -2.0), (2, -2.0)]),
            (f64::NEG_INFINITY, 2.0, vec![(0, -2.0)]),
        ],
        obj: vec![-1.0, -1.0, 1.0],
        maximize: true,
    };
    let model = build(&lp, true);
    let mut session = BabSession::new(model.clone(), &SolveOpts::new()).unwrap();
    match session.check().unwrap() {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            assert_eq!(value, BigRational::from_integer(1.into()));
            assert_eq!(model_values.len(), model.num_cols());
            model.check_point(&model_values).unwrap();
            assert_eq!(model.objective_value_at(&model_values), value);
        }
        other => panic!("bounded mixed model must be Optimal, got {other:?}"),
    }
}

proptest! {
    #![proptest_config(ProptestConfig { cases: 48, ..ProptestConfig::default() })]

    /// Exact rim and smt lane agree on verdict and exact optimum.
    #[test]
    fn lanes_agree_on_random_lps(lp in random_lp()) {
        let exact_model = build(&lp, false);
        let smt_model = build(&lp, true);

        // Use the same public operation on both models. BabSession routes the
        // continuous model through ExactLp and the dummy-binary model through
        // the independent SMT lane.
        let mut exact_session = BabSession::new(exact_model.clone(),&SolveOpts::new()).unwrap();
        let exact_outcome = exact_session.check().unwrap();

        let mut smt_session = BabSession::new(smt_model.clone(),&SolveOpts::new()).unwrap();
        let smt_outcome = smt_session.check().unwrap();

        check_outcome_model(&exact_model, &exact_outcome)?;
        check_outcome_model(&smt_model, &smt_outcome)?;

        // `build` explicitly calls `set_objective`, even when every
        // coefficient is zero. Track non-triviality only for the unbounded
        // sanity check; it does not decide whether this is optimization.
        let has_nonzero_coefficient = lp.obj.iter().any(|&a| a != 0.0);

        match (&exact_outcome, &smt_outcome) {
            (Outcome::Optimal { value: v1, cert, .. }, Outcome::Optimal { value: v2, .. }) => {
                prop_assert_eq!(v1, v2, "optima must agree exactly");
                let cert = cert.as_ref().expect("exact lane certifies");
                prop_assert!(cert.verify(&exact_model).is_ok());
            }
            (Outcome::Feasible { .. }, Outcome::Feasible { .. }) => prop_assert!(
                false,
                "an explicitly set objective requires an optimization verdict"
            ),
            (Outcome::Infeasible { cert, .. }, Outcome::Infeasible { cert: smt_cert, .. }) => {
                let cert = cert.as_ref().expect("exact lane certifies");
                prop_assert!(cert.verify(&exact_model).is_ok());
                if let Some(cert) = smt_cert {
                    prop_assert!(cert.verify(&smt_model).is_ok());
                }
            }
            (Outcome::Unbounded, Outcome::Unbounded) => {
                prop_assert!(
                    has_nonzero_coefficient,
                    "a constant objective cannot be unbounded"
                );
            }
            // KNOWN INCOMPLETENESS of the native branch-and-bound, not a
            // disagreement. An unbounded LP relaxation makes the MILP unbounded
            // only if the MILP is FEASIBLE; if it is infeasible, reporting
            // `Unbounded` would be a wrong verdict. Most solvers conflate the two
            // (Gurobi's INF_OR_UNBD); this lane refuses to, and says so when its
            // integer-feasibility probe cannot settle the question. Sound, and
            // weaker than we would like. The smt fallback normally answers before
            // this is reached; the arm keeps the property honest if it ever is.
            (Outcome::Unbounded, Outcome::Unknown { .. }) => {}
            // Anything else is a real disagreement.
            (a, b) => prop_assert!(false, "lane disagreement: exact={a:?} smt={b:?}"),
        }
    }
}
