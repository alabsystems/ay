// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! P4 certified-cut harvesting: `LpSession::harvest_cut` and the
//! `OptimalityCertificate -> CertifiedRow` conversion. Each capability has a
//! positive (harvest + independently verify) and a false twin (unbounded /
//! infeasible / tampered -> refused). See `crates/ay-milp/design/P4-SPEC.md`.

use ay_milp::{
    BoundSide, CertifiedRow, Col, FactRef, LpSession, Model, Multiplier, Outcome, Sense, SolveOpts,
};
use num_rational::BigRational;
use num_traits::{ToPrimitive, Zero};

fn int(n: i64) -> BigRational {
    BigRational::from_integer(n.into())
}

/// A window-shaped LP: `x0, x1 in [0, 1]`, `y = x0 + x1` (free), plus a
/// coupling row `x0 - x1 >= -1/2`. Returns the model and `y`.
fn window_model() -> (Model, Col) {
    let mut m = Model::new();
    let x0 = m.add_col(0.0, 1.0);
    let x1 = m.add_col(0.0, 1.0);
    let y = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    m.add_row(0.0, 0.0, &[(y, 1.0), (x0, -1.0), (x1, -1.0)]); // y = x0 + x1
    m.add_row(-0.5, f64::INFINITY, &[(x0, 1.0), (x1, -1.0)]); // x0 - x1 >= -1/2
    (m, y)
}

#[test]
fn harvest_minimize_cut_verifies_and_is_tight() {
    let (m, y) = window_model();
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    let row = s
        .harvest_cut(&[(y, 1.0)], Sense::Minimize)
        .expect("bounded window objective harvests a cut");
    // Independently checkable against the model, no solver state.
    row.verify(&m).expect("harvested cut must verify");
    // min y = 0 (x0 = x1 = 0), so the proved inequality is y >= 0.
    assert!(
        row.lb.is_zero(),
        "expected y >= 0, got lb {}",
        row.lb.to_f64().unwrap()
    );
    // The cut is on y with coefficient 1.
    assert_eq!(
        row.coeffs,
        vec![(y.index() as u32, BigRational::from_integer(1.into()))]
    );
}

#[test]
fn harvest_maximize_cut_reorients_to_lower_bound_form() {
    let (m, y) = window_model();
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    let row = s
        .harvest_cut(&[(y, 1.0)], Sense::Maximize)
        .expect("bounded above too");
    row.verify(&m)
        .expect("harvested upper-bound cut must verify");
    // max y = 2, proved as (-y) >= -2  <=>  y <= 2.
    assert_eq!(
        row.coeffs,
        vec![(y.index() as u32, BigRational::from_integer((-1).into()))]
    );
    assert_eq!(row.lb, BigRational::from_integer((-2).into()));
}

#[test]
fn harvested_cut_holds_at_every_feasible_point() {
    // SOUNDNESS: the harvested inequality is model-implied — it must hold at
    // an actual feasible point of the model (here, the max-y witness).
    let (m, y) = window_model();
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    let row = s.harvest_cut(&[(y, 1.0)], Sense::Minimize).unwrap();
    // Grab a concrete feasible point and check coeffs·x >= lb on it.
    match s.optimize(y, Sense::Maximize).unwrap() {
        Outcome::Optimal { model_values, .. } => {
            let mut lhs = BigRational::zero();
            for &(c, ref a) in &row.coeffs {
                lhs += a * &model_values[c as usize];
            }
            assert!(lhs >= row.lb, "harvested cut violated at a feasible point");
        }
        other => panic!("expected Optimal witness, got {other:?}"),
    }
}

#[test]
fn harvest_none_on_unbounded_objective() {
    // TWIN: an objective unbounded below has no finite optimum -> no cut.
    let mut m = Model::new();
    let x = m.add_col(f64::NEG_INFINITY, f64::INFINITY); // free, unconstrained
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    assert!(s.harvest_cut(&[(x, 1.0)], Sense::Minimize).is_none());
}

#[test]
fn harvest_none_on_infeasible_model() {
    // TWIN: x >= 2 and x <= 1 has no feasible point -> no cut to harvest.
    let mut m = Model::new();
    let x = m.add_col(-10.0, 10.0);
    m.add_row(2.0, f64::INFINITY, &[(x, 1.0)]);
    m.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0)]);
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    assert!(s.harvest_cut(&[(x, 1.0)], Sense::Minimize).is_none());
}

#[test]
fn harvest_none_on_nonfinite_coeffs() {
    let (m, y) = window_model();
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    assert!(s.harvest_cut(&[(y, f64::NAN)], Sense::Minimize).is_none());
    assert!(s
        .harvest_cut(&[(y, f64::INFINITY)], Sense::Minimize)
        .is_none());
}

#[test]
fn harvested_cut_is_bound_to_its_model() {
    // A cut derived from one model's facts must NOT verify against a model
    // whose constraints differ (the derivation references THIS model's rows).
    let (m, y) = window_model();
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    let row = s.harvest_cut(&[(y, 1.0)], Sense::Minimize).unwrap();
    row.verify(&m).expect("verifies against its own model");

    // A model with the SAME columns but the coupling equality dropped: the
    // multipliers reference a row that no longer means what it did, so the
    // derivation can no longer reproduce coeffs·x - lb.
    let mut m2 = Model::new();
    let a0 = m2.add_col(0.0, 1.0);
    let a1 = m2.add_col(0.0, 1.0);
    let _y2 = m2.add_col(f64::NEG_INFINITY, f64::INFINITY);
    m2.add_row(5.0, 5.0, &[(a0, 1.0), (a1, 1.0)]); // an unrelated equality
    m2.add_row(-0.5, f64::INFINITY, &[(a0, 1.0), (a1, -1.0)]);
    assert!(
        row.verify(&m2).is_err(),
        "a model-bound cut must not verify against a different model"
    );
}

/// Regression (P4 audit): `verify` must interpret a row's coefficients by
/// their SUM over repeated columns, matching how the multiplier side
/// combines — so an internally-inconsistent duplicate-column row is rejected,
/// not silently checked against only its last entry.
#[test]
fn verify_rejects_inconsistent_duplicate_column_row() {
    // x0 in [3, 10]. The lower-bound fact proves x0 - 3 >= 0, i.e. x0 >= 3.
    let mut m = Model::new();
    let x0 = m.add_col(3.0, 10.0);
    let proof = vec![Multiplier {
        fact: FactRef::ColBound {
            col: x0,
            side: BoundSide::Lower,
        },
        coeff: int(1),
    }];
    // Canonical row `1·x0 >= 3` is genuinely proved: verifies.
    let good = CertifiedRow {
        coeffs: vec![(x0.index() as u32, int(1))],
        lb: int(3),
        multipliers: proof.clone(),
    };
    good.verify(&m)
        .expect("x0 >= 3 is proved by the lower-bound fact");
    // Duplicate columns summing to −3 (`−4·x0 + 1·x0 = −3·x0`) claim
    // `−3·x0 >= 3` (x0 <= −1, FALSE on [3,10]) but carry the SAME proof of
    // x0 >= 3. Assignment-based verify would have read coeffs[0] as the last
    // entry (1) and passed; accumulation reads −3 and rejects.
    let bad = CertifiedRow {
        coeffs: vec![(x0.index() as u32, int(-4)), (x0.index() as u32, int(1))],
        lb: int(3),
        multipliers: proof,
    };
    assert!(
        bad.verify(&m).is_err(),
        "an internally-inconsistent duplicate-column row must be rejected"
    );
}
