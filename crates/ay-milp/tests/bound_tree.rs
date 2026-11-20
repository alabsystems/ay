// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `derive_bound_tree_reported`: an exact, witness-free certificate that every
//! integer-feasible point has objective at least (Minimize) / at most
//! (Maximize) a value, the artifact an interrupted search's dual bound needs.

use ay_milp::{
    derive_bound_tree_reported, BabSession, Col, LpSession, MilpBoundCertificate, Model,
    OptimalityTreeBudget, Outcome, Sense, SolveOpts,
};
use num_rational::BigRational;

fn int(v: i64) -> BigRational {
    BigRational::from_integer(v.into())
}

/// min -(5a + 4b + 3c) s.t. 2a + 3b + 4c <= 4, binaries. No two items fit
/// together, so the integer optimum takes `a` alone (-5); the LP relaxation
/// takes `a` and 2/3 of `b` (-23/3), a strictly weaker bound.
fn knapsack() -> Model {
    let mut m = Model::new();
    let a = m.add_binary_col();
    let b = m.add_binary_col();
    let c = m.add_binary_col();
    m.add_row(f64::NEG_INFINITY, 4.0, &[(a, 2.0), (b, 3.0), (c, 4.0)]);
    m.set_objective(&[(a, -5.0), (b, -4.0), (c, -3.0)], Sense::Minimize);
    m
}

/// Exact integer optimum of `knapsack` by enumeration.
fn knapsack_optimum() -> BigRational {
    let mut best: Option<i64> = None;
    for a in 0..=1i64 {
        for b in 0..=1i64 {
            for c in 0..=1i64 {
                if 2 * a + 3 * b + 4 * c <= 4 {
                    let v = -(5 * a + 4 * b + 3 * c);
                    best = Some(best.map_or(v, |x: i64| x.min(v)));
                }
            }
        }
    }
    int(best.expect("feasible"))
}

fn relaxed(m: &Model) -> Model {
    let mut r = Model::new();
    let cols: Vec<Col> = (0..m.num_cols())
        .map(|j| {
            let (l, u) = m.col_bounds(m.col_at(j).unwrap());
            r.add_col(l, u)
        })
        .collect();
    for i in 0..m.num_rows() {
        let (coeffs, l, u) = m.row(m.row_at(i).unwrap());
        let row: Vec<(Col, f64)> = coeffs.iter().map(|&(c, a)| (cols[c as usize], a)).collect();
        r.add_row(l, u, &row);
    }
    r
}

#[test]
fn bound_tree_certifies_the_integer_optimum_beyond_the_lp_bound() {
    let m = knapsack();
    let opt = knapsack_optimum();
    assert_eq!(opt, int(-5));
    // The LP bound is strictly weaker than the integer optimum: a genuine
    // integer argument is needed, not one LP leaf.
    let r = relaxed(&m);
    let mut lp = LpSession::new(&r, &SolveOpts::new()).unwrap();
    let objective: Vec<(Col, f64)> = vec![
        (r.col_at(0).unwrap(), -5.0),
        (r.col_at(1).unwrap(), -4.0),
        (r.col_at(2).unwrap(), -3.0),
    ];
    let Outcome::Bound { dual_bound, .. } =
        lp.rigorous_bound_expr(&objective, Sense::Minimize).unwrap()
    else {
        panic!("bounded LP");
    };
    assert!(
        dual_bound < opt,
        "LP bound {dual_bound} must be below the integer optimum {opt}"
    );

    let (cert, report) = derive_bound_tree_reported(&m, &opt, &OptimalityTreeBudget::new(4096));
    let cert = cert.unwrap_or_else(|| panic!("certifies the optimum: {report:?}"));
    cert.verify(&m).expect("independent replay");
    // A weaker bound is cheaper and also certifiable.
    let (weaker, _) = derive_bound_tree_reported(&m, &int(-7), &OptimalityTreeBudget::new(4096));
    weaker.expect("a weaker bound").verify(&m).unwrap();
}

#[test]
fn bound_tree_refuses_a_bound_a_feasible_point_beats() {
    let m = knapsack();
    let opt = knapsack_optimum();
    // `opt + 1` is violated by the optimal point: no tree may exist.
    let (cert, report) =
        derive_bound_tree_reported(&m, &(&opt + int(1)), &OptimalityTreeBudget::new(4096));
    assert!(
        cert.is_none(),
        "no certificate above the optimum: {report:?}"
    );
    // Tampering with a genuine certificate's value is caught by replay.
    let (cert, _) = derive_bound_tree_reported(&m, &opt, &OptimalityTreeBudget::new(4096));
    let mut forged: MilpBoundCertificate = cert.unwrap();
    forged.value = &opt + BigRational::new(1.into(), 2.into());
    assert!(forged.verify(&m).is_err(), "a raised value must not replay");
    // A zero leaf budget is a refusal, never a certificate.
    assert!(
        derive_bound_tree_reported(&m, &opt, &OptimalityTreeBudget::new(0))
            .0
            .is_none()
    );
}

#[test]
fn bound_tree_handles_maximize_frame() {
    let mut m = knapsack();
    let cols: Vec<Col> = (0..3).map(|j| m.col_at(j).unwrap()).collect();
    m.set_objective(
        &[(cols[0], 5.0), (cols[1], 4.0), (cols[2], 3.0)],
        Sense::Maximize,
    );
    let opt = -knapsack_optimum(); // max = 5
    let (cert, report) = derive_bound_tree_reported(&m, &opt, &OptimalityTreeBudget::new(4096));
    cert.unwrap_or_else(|| panic!("max-frame bound: {report:?}"))
        .verify(&m)
        .unwrap();
    let (none, _) =
        derive_bound_tree_reported(&m, &(&opt - int(1)), &OptimalityTreeBudget::new(4096));
    assert!(
        none.is_none(),
        "an upper bound below the attained maximum cannot exist"
    );
}

/// The NY shape: a big-M ReLU network maximizing an output. The certified
/// bound on the integer optimum matches what branch-and-bound proves.
#[test]
fn bound_tree_certifies_a_big_m_relu_network_maximum() {
    let units: [([f64; 2], f64, f64); 3] = [
        ([1.0, -0.75], 0.25, 1.0),
        ([-0.5, 1.0], 0.125, -0.75),
        ([0.75, 0.5], -0.25, 0.5),
    ];
    let mut m = Model::new();
    let x = [m.add_col(-1.0, 1.0), m.add_col(-1.0, 1.0)];
    let mut objective = Vec::new();
    for (w, b, c) in units {
        let l = b - w[0].abs() - w[1].abs();
        let u = b + w[0].abs() + w[1].abs();
        let y = m.add_col(0.0, u);
        let z = m.add_binary_col();
        m.add_row(b, f64::INFINITY, &[(y, 1.0), (x[0], -w[0]), (x[1], -w[1])]);
        m.add_row(
            f64::NEG_INFINITY,
            b - l,
            &[(y, 1.0), (x[0], -w[0]), (x[1], -w[1]), (z, -l)],
        );
        m.add_row(f64::NEG_INFINITY, 0.0, &[(y, 1.0), (z, -u)]);
        objective.push((y, c));
    }
    m.set_objective(&objective, Sense::Maximize);
    let mut session = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    let Outcome::Optimal { value, .. } = session.check().unwrap() else {
        panic!("small network solves to optimality");
    };
    let (cert, report) = derive_bound_tree_reported(&m, &value, &OptimalityTreeBudget::new(4096));
    let cert = cert.unwrap_or_else(|| panic!("certified maximum: {report:?}"));
    cert.verify(&m).expect("independent replay");
    // And nothing strictly below the true maximum can be certified as an
    // upper bound.
    let below = &value - BigRational::new(1.into(), 64.into());
    let (none, _) = derive_bound_tree_reported(&m, &below, &OptimalityTreeBudget::new(4096));
    assert!(none.is_none());
}
