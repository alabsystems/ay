// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! OBBT driver tests (P3): productivity, soundness (the tightened box never
//! excludes a feasible point), determinism, and fail-closed behaviour. The
//! pure-exact-rim soundness twin lives in `tests/obbt_exact.rs` (it forces
//! the float advice lane off via `AY_MILP_NO_FLOAT`, a process-global switch
//! that must own its own test binary). See `crates/ay-milp/design/P3-SPEC.md`.

use ay_milp::{Col, LpSession, Model, ObbtOpts, Outcome, Sense, SolveOpts};
use num_traits::ToPrimitive;

/// The exact optimum of `col` over `model` in `sense`, as f64. On this engine
/// `optimize` adjudicates the float basis through the exact rim, so the
/// returned value is exact — the reference the OBBT box is checked against.
fn exact_opt(model: &Model, col: Col, sense: Sense) -> Option<f64> {
    let mut s = LpSession::new(model, &SolveOpts::new()).unwrap();
    match s.optimize(col, sense).unwrap() {
        Outcome::Optimal { value, .. } => value.to_f64(),
        _ => None,
    }
}

/// Every feasible point's `col` value lies in `[true_min, true_max]`; assert
/// the OBBT box still contains that whole interval, so it excluded nothing.
fn assert_box_contains_feasible_range(model: &Model, col: Col, lb: f64, ub: f64) {
    if let Some(mn) = exact_opt(model, col, Sense::Minimize) {
        assert!(
            lb <= mn + 1e-9,
            "OBBT lower bound {lb} cut the true minimum {mn} of col {}",
            col.index()
        );
    }
    if let Some(mx) = exact_opt(model, col, Sense::Maximize) {
        assert!(
            ub >= mx - 1e-9,
            "OBBT upper bound {ub} cut the true maximum {mx} of col {}",
            col.index()
        );
    }
}

/// A coupled box: `x = y` and `1 <= y <= 3`, both cols nominally `[-10, 10]`.
/// OBBT must pull `x` (and `y`) in to about `[1, 3]` through the coupling.
fn coupled_model() -> (Model, Col, Col) {
    let mut m = Model::new();
    let x = m.add_col(-10.0, 10.0);
    let y = m.add_col(-10.0, 10.0);
    m.add_row(0.0, 0.0, &[(x, 1.0), (y, -1.0)]); // x - y = 0
    m.add_row(1.0, 3.0, &[(y, 1.0)]); // 1 <= y <= 3
    (m, x, y)
}

#[test]
fn obbt_tightens_coupled_box() {
    let (m, x, y) = coupled_model();
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    let report = s.obbt(&[x, y], &ObbtOpts::default()).unwrap();
    assert!(!report.infeasible);
    assert_eq!(report.tightened, 2, "both coupled columns tighten");
    // x pulled from [-10, 10] to about [1, 3].
    let (xlb, xub) = report.bounds[0];
    assert!(
        xlb >= 1.0 - 1e-9 && xub <= 3.0 + 1e-9,
        "x box {xlb}..{xub} not ~[1,3]"
    );
    // Soundness: neither box cut the true feasible range.
    assert_box_contains_feasible_range(&m, x, xlb, xub);
    let (ylb, yub) = report.bounds[1];
    assert_box_contains_feasible_range(&m, y, ylb, yub);
}

#[test]
fn obbt_second_run_is_a_fixpoint() {
    // TWIN of productivity: re-running OBBT after it converged tightens
    // nothing more (idempotent at the fixpoint).
    let (m, x, y) = coupled_model();
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    let first = s.obbt(&[x, y], &ObbtOpts::default()).unwrap();
    let second = s.obbt(&[x, y], &ObbtOpts::default()).unwrap();
    assert_eq!(second.tightened, 0, "already at the fixpoint");
    assert_eq!(
        first.bounds, second.bounds,
        "bounds stable across a second run"
    );
}

#[test]
fn obbt_never_widens_and_stays_sound_on_a_bigger_lp() {
    // A three-variable coupled LP; check the box only ever shrinks and the
    // shrunk box still contains the exact feasible range of each column.
    let mut m = Model::new();
    let a = m.add_col(-5.0, 5.0);
    let b = m.add_col(-5.0, 5.0);
    let c = m.add_col(-5.0, 5.0);
    m.add_row(0.0, f64::INFINITY, &[(b, 1.0), (a, -1.0)]); // b >= a
    m.add_row(0.0, f64::INFINITY, &[(c, 1.0), (b, -1.0)]); // c >= b
    m.add_row(f64::NEG_INFINITY, 2.0, &[(c, 1.0)]); // c <= 2
    m.add_row(-1.0, f64::INFINITY, &[(a, 1.0)]); // a >= -1
    let orig = [(-5.0, 5.0); 3];
    let cols = [a, b, c];
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    let report = s.obbt(&cols, &ObbtOpts::default()).unwrap();
    assert!(!report.infeasible);
    for (i, &col) in cols.iter().enumerate() {
        let (lb, ub) = report.bounds[i];
        assert!(
            lb >= orig[i].0 - 1e-12 && ub <= orig[i].1 + 1e-12,
            "col {i} widened"
        );
        assert!(lb <= ub, "col {i} crossed");
        assert_box_contains_feasible_range(&m, col, lb, ub);
    }
    assert!(
        report.tightened >= 1,
        "the chain must tighten at least one box"
    );
}

#[test]
fn obbt_is_deterministic() {
    let run = || {
        let (m, x, y) = coupled_model();
        let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
        s.obbt(&[x, y], &ObbtOpts::default()).unwrap().bounds
    };
    assert_eq!(run(), run(), "OBBT bounds drift run-to-run");
}

#[test]
fn obbt_flags_an_infeasible_model() {
    // x >= 2 and x <= 1: the rigorous solve certifies infeasibility.
    let mut m = Model::new();
    let x = m.add_col(-10.0, 10.0);
    m.add_row(2.0, f64::INFINITY, &[(x, 1.0)]);
    m.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0)]);
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    let report = s.obbt(&[x], &ObbtOpts::default()).unwrap();
    assert!(report.infeasible, "OBBT must surface the infeasibility");
}

#[test]
fn narrow_col_bounds_only_ever_tightens() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 10.0);
    m.add_row(0.0, 10.0, &[(x, 1.0)]);
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    // A genuine tightening reports true and sticks.
    assert!(s.narrow_col_bounds(x, 2.0, 8.0));
    assert_eq!(s.col_bounds(x), (2.0, 8.0));
    // A widening request is refused (no-op, returns false).
    assert!(!s.narrow_col_bounds(x, -5.0, 20.0));
    assert_eq!(s.col_bounds(x), (2.0, 8.0));
    // NaN is ignored (no-op).
    assert!(!s.narrow_col_bounds(x, f64::NAN, 5.0));
    assert_eq!(s.col_bounds(x), (2.0, 8.0));
    // A crossed intersection (lower above current upper) is refused.
    assert!(!s.narrow_col_bounds(x, 9.0, 9.5));
    assert_eq!(s.col_bounds(x), (2.0, 8.0));
    // A tightening-side infinity would empty the box: refused, not committed.
    assert!(!s.narrow_col_bounds(x, f64::INFINITY, f64::INFINITY));
    assert!(!s.narrow_col_bounds(x, f64::NEG_INFINITY, f64::NEG_INFINITY));
    assert_eq!(s.col_bounds(x), (2.0, 8.0));
    // The no-op sides (-inf lower / +inf upper) are accepted as "don't
    // tighten here" and combine with a real tightening on the other side.
    assert!(s.narrow_col_bounds(x, f64::NEG_INFINITY, 7.0));
    assert_eq!(s.col_bounds(x), (2.0, 7.0));
}

#[test]
fn narrow_then_optimize_respects_the_tighter_box() {
    // After committing a tighter box, an exact optimize honours it — the
    // authority path is rebuilt from the narrowed model (P3-SPEC §rule 3).
    let mut m = Model::new();
    let x = m.add_col(0.0, 10.0);
    m.add_row(0.0, 10.0, &[(x, 1.0)]);
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    assert!(s.narrow_col_bounds(x, 0.0, 4.0));
    match s.optimize(x, Sense::Maximize).unwrap() {
        Outcome::Optimal { value, cert, .. } => {
            assert_eq!(
                value.to_f64(),
                Some(4.0),
                "max honours the narrowed upper bound"
            );
            // The certificate must verify against the narrowed model the
            // session is actually solving. `set_col_bounds` is crate-private,
            // so reconstruct that model with the narrowed column directly.
            if let Some(cert) = cert {
                let mut narrowed = Model::new();
                let nx = narrowed.add_col(0.0, 4.0);
                narrowed.add_row(0.0, 10.0, &[(nx, 1.0)]);
                cert.verify(&narrowed).unwrap();
            }
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}
