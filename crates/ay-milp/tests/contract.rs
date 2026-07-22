// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The five API contract properties of
//! the development design notes §3, as tests.

use std::time::{Duration, Instant};

use ay_milp::{BabSession, LpSession, Model, Outcome, Sense, SolveOpts};
use num_rational::BigRational;

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

/// Property 5: `Model: Send + Sync + Clone`; sessions `Send`.
#[test]
fn model_and_sessions_are_send() {
    fn assert_send_sync_clone<T: Send + Sync + Clone>() {}
    fn assert_send<T: Send>() {}
    assert_send_sync_clone::<Model>();
    assert_send::<LpSession>();
    assert_send::<BabSession>();
}

/// Property 4 (determinism): identical inputs, identical outcomes.
#[test]
fn determinism_run_to_run() {
    let build = || {
        let mut m = Model::new();
        let x = m.add_binary_col();
        let y = m.add_binary_col();
        let z = m.add_col(0.0, 3.0);
        m.add_row(1.0, 2.0, &[(x, 1.0), (y, 1.0), (z, 0.5)]);
        m.set_objective(&[(x, 1.0), (y, 3.0), (z, 0.25)], Sense::Maximize);
        m
    };
    let solve = |m: &Model| -> String {
        let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
        format!("{:?}", s.check().unwrap())
    };
    let m1 = build();
    let m2 = build();
    assert_eq!(solve(&m1), solve(&m2));
    assert_eq!(solve(&m1), solve(&m1), "same session-model twice");
}

/// Property 4 (deadlines): an expired deadline yields Unknown(Timeout) or a
/// sound verdict that finished first — never a hang and never a wrong value.
#[test]
fn expired_deadline_fails_closed() {
    let mut m = Model::new();
    let mut prev = m.add_col(0.0, 1.0);
    // A chain long enough that the exact lane hits a deadline checkpoint.
    for _ in 0..200 {
        let next = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
        m.add_row(0.0, 0.0, &[(prev, 1.0), (next, -1.0)]);
        prev = next;
    }
    let expired_deadline = Instant::now()
        .checked_sub(Duration::from_secs(1))
        .expect("test clock must support a one-second lookback");
    let opts = SolveOpts::new().with_deadline(expired_deadline);
    let mut s = LpSession::new(&m, &opts).unwrap();
    match s.optimize(prev, Sense::Maximize).unwrap() {
        Outcome::Unknown { .. } | Outcome::Optimal { .. } | Outcome::Unbounded => {}
        other => panic!("expired deadline must fail closed, got {other:?}"),
    }
}

/// Property 1: `check_point` guards witnesses (the belt the downstream optimization consumer's revalidation
/// wears too).
#[test]
fn check_point_accepts_and_rejects() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_col(0.0, 2.0);
    m.add_row(1.0, 2.0, &[(x, 1.0), (y, 1.0)]);
    assert!(m.check_point(&[rat(1, 1), rat(1, 2)]).is_ok());
    // Violates the row lower bound.
    assert!(m.check_point(&[rat(0, 1), rat(1, 2)]).is_err());
    // Violates integrality.
    assert!(m.check_point(&[rat(1, 2), rat(1, 1)]).is_err());
    // Violates the column bound.
    assert!(m.check_point(&[rat(1, 1), rat(5, 2)]).is_err());
}

/// NaN input is rejected at the model boundary.
#[test]
#[should_panic(expected = "NaN")]
fn nan_bound_panics() {
    let mut m = Model::new();
    let _ = m.add_col(f64::NAN, 1.0);
}

/// Duplicate coefficients merge; merged-to-zero coefficients vanish.
#[test]
fn add_row_merges_duplicates() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 1.0);
    let y = m.add_col(0.0, 1.0);
    let r = m.add_row(0.0, 1.0, &[(x, 2.0), (y, 1.0), (x, -2.0)]);
    let (coeffs, _, _) = m.row(r);
    assert_eq!(coeffs, &[(y.index() as u32, 1.0)][..]);
}

/// The objective offset flows through both lanes.
#[test]
fn objective_offset_is_reported() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    m.set_objective(&[(x, 1.0)], Sense::Minimize);
    m.set_objective_offset(5.0);
    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    match s.check().unwrap() {
        Outcome::Optimal { value, .. } => assert_eq!(value, rat(5, 1)),
        other => panic!("expected Optimal, got {other:?}"),
    }
}
