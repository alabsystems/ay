// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness of the MARGIN REFRAME (opt-in via `Model::mark_margin_row`).
//!
//! The reframe turns an objective-≡0 feasibility problem `R ∧ (violation row)`
//! into a margin OPTIMIZATION and maps the optimum back to the ORIGINAL
//! feasibility verdict. The contract these tests pin down:
//!
//! 1. The reframed verdict EQUALS the plain feasibility verdict on the same
//!    model — for BOTH a property that HOLDS (original infeasible = the band is
//!    unreachable) and one that is VIOLATED (original feasible = the band is
//!    reached), across `<=` and `>=` rows, continuous and integral.
//! 2. An exported Farkas certificate independently verifies against the
//!    ORIGINAL model.
//! 3. The reframe is FAIL-SAFE: the kill switch and every ill-fitting shape
//!    fall back to the plain feasibility solve with an identical verdict.

use ay_milp::{BabSession, Model, Outcome, SolveOpts};

fn opts() -> SolveOpts {
    SolveOpts::new().with_time_limit(std::time::Duration::from_secs(30))
}

fn solve(m: &Model) -> Outcome {
    BabSession::new(m.clone(), &opts())
        .expect("session")
        .check()
        .expect("check")
}

/// True for a satisfiable verdict (`Optimal`/`Feasible`).
fn is_sat(o: &Outcome) -> bool {
    o.is_sat()
}

/// A verdict class label, so a mismatch prints usefully.
fn tag(o: &Outcome) -> &'static str {
    match o {
        Outcome::Optimal { .. } => "OPTIMAL",
        Outcome::Feasible { .. } => "FEASIBLE",
        Outcome::Infeasible { .. } => "INFEASIBLE",
        Outcome::Unbounded => "UNBOUNDED",
        Outcome::Bound { .. } => "BOUND",
        Outcome::Unknown { .. } => "UNKNOWN",
        _ => "OTHER",
    }
}

/// Build `R ∧ (margin row)` where `R` is a single row `sum_x in [rest_lo,
/// rest_hi]` over two `[0,1]` variables (continuous unless `integral`), and the
/// margin row is `sum_x <= band` (`le`) or `sum_x >= band` (`ge`).
///
/// Returns `(with_mark, plain)`: identical models, but `with_mark` names the
/// margin row (reframe path) and `plain` leaves it a normal constraint
/// (feasibility path). Both must reach the same verdict.
fn build(integral: bool, rest_lo: f64, rest_hi: f64, le: bool, band: f64) -> (Model, Model) {
    let mut m = Model::new();
    let x = if integral {
        m.add_int_col(0.0, 1.0)
    } else {
        m.add_col(0.0, 1.0)
    };
    let y = if integral {
        m.add_int_col(0.0, 1.0)
    } else {
        m.add_col(0.0, 1.0)
    };
    // R: rest_lo <= x + y <= rest_hi
    m.add_row(rest_lo, rest_hi, &[(x, 1.0), (y, 1.0)]);
    // violation row: x + y <= band (le) or x + y >= band (ge)
    let vrow = if le {
        m.add_row(f64::NEG_INFINITY, band, &[(x, 1.0), (y, 1.0)])
    } else {
        m.add_row(band, f64::INFINITY, &[(x, 1.0), (y, 1.0)])
    };
    let plain = m.clone();
    m.mark_margin_row(vrow).expect("one-sided margin row");
    (m, plain)
}

/// The reframe verdict must MATCH the plain feasibility verdict, and both must
/// have the expected satisfiability. This is the core soundness property.
fn assert_reframe_matches_plain(with_mark: &Model, plain: &Model, want_sat: bool) {
    let reframed = solve(with_mark);
    let feas = solve(plain);
    assert_eq!(
        is_sat(&reframed),
        want_sat,
        "reframe verdict {} disagrees with the expected {}",
        tag(&reframed),
        if want_sat { "SAT" } else { "INFEASIBLE" }
    );
    assert_eq!(
        is_sat(&reframed),
        is_sat(&feas),
        "reframe verdict {} != plain feasibility verdict {}",
        tag(&reframed),
        tag(&feas)
    );
    // Neither path may EVER answer the opposite of the truth.
    if want_sat {
        assert!(!reframed.is_infeasible(), "reframe wrongly INFEASIBLE");
        assert!(!feas.is_infeasible(), "plain wrongly INFEASIBLE");
    } else {
        assert!(
            reframed.is_infeasible(),
            "reframe failed to prove INFEASIBLE (got {})",
            tag(&reframed)
        );
    }
}

// ---- property HOLDS: original INFEASIBLE (band unreachable) ----

#[test]
fn le_row_property_holds_is_infeasible_continuous() {
    // R forces x+y >= 1.5; the band asks x+y <= 1.0 -> min(x+y)=1.5 > 1.0.
    let (mark, plain) = build(false, 1.5, 2.0, true, 1.0);
    assert_reframe_matches_plain(&mark, &plain, false);
}

#[test]
fn le_row_property_holds_is_infeasible_integral() {
    // Binaries: R forces x+y >= 2 (both 1); band asks x+y <= 1 -> infeasible.
    let (mark, plain) = build(true, 2.0, 2.0, true, 1.0);
    assert_reframe_matches_plain(&mark, &plain, false);
}

#[test]
fn ge_row_property_holds_is_infeasible_continuous() {
    // R forces x+y <= 0.5; the band asks x+y >= 2.0 -> max(x+y)=0.5 < 2.0.
    let (mark, plain) = build(false, 0.0, 0.5, false, 2.0);
    assert_reframe_matches_plain(&mark, &plain, false);
}

// ---- property VIOLATED: original FEASIBLE (band reached) ----

#[test]
fn le_row_property_violated_is_feasible_continuous() {
    // R allows x+y in [0.5, 2]; band asks x+y <= 1.0 -> min=0.5 <= 1.0 -> SAT.
    let (mark, plain) = build(false, 0.5, 2.0, true, 1.0);
    assert_reframe_matches_plain(&mark, &plain, true);
}

#[test]
fn le_row_property_violated_is_feasible_integral() {
    // Binaries: R allows x+y in [1,2]; band asks x+y <= 1 -> x+y=1 -> SAT.
    let (mark, plain) = build(true, 1.0, 2.0, true, 1.0);
    assert_reframe_matches_plain(&mark, &plain, true);
}

#[test]
fn ge_row_property_violated_is_feasible_continuous() {
    // R allows x+y in [0, 0.6]; band asks x+y >= 0.3 -> max=0.6 >= 0.3 -> SAT.
    let (mark, plain) = build(false, 0.0, 0.6, false, 0.3);
    assert_reframe_matches_plain(&mark, &plain, true);
}

/// The reframe's FEASIBLE witness must actually satisfy the ORIGINAL model,
/// violation row included (the reframe returns the point; `finish` re-checks
/// it, so a wrong point would surface as `Unknown`, never a false SAT).
#[test]
fn feasible_witness_satisfies_the_original_model() {
    let (mark, _plain) = build(false, 0.5, 2.0, true, 1.0);
    match solve(&mark) {
        Outcome::Feasible { model_values, .. } | Outcome::Optimal { model_values, .. } => {
            mark.check_point(&model_values)
                .expect("reframe witness must satisfy the original model incl. the band row");
        }
        other => panic!("expected a witnessed SAT verdict, got {}", tag(&other)),
    }
}

// ---- certificate export ----

/// On an infeasible-because-band-unreachable instance the reframe should EXPORT
/// a Farkas certificate that independently verifies against the ORIGINAL model.
#[test]
fn infeasible_exports_verifiable_farkas() {
    let (mark, _plain) = build(false, 1.5, 2.0, true, 1.0);
    match solve(&mark) {
        Outcome::Infeasible { cert, tree_cert } => {
            // At least one exact witness, and it must verify against the model.
            let farkas = cert.expect("a continuous margin reframe exports a Farkas witness");
            farkas
                .verify(&mark)
                .expect("Farkas certificate must verify against the ORIGINAL model");
            assert!(tree_cert.is_none() || tree_cert.unwrap().verify(&mark).is_ok());
        }
        other => panic!("expected INFEASIBLE, got {}", tag(&other)),
    }
}

/// `>=` direction: same, with the LOWER-side fact composed in.
#[test]
fn ge_infeasible_exports_verifiable_farkas() {
    let (mark, _plain) = build(false, 0.0, 0.5, false, 2.0);
    match solve(&mark) {
        Outcome::Infeasible { cert, .. } => {
            let farkas = cert.expect("Farkas witness");
            farkas.verify(&mark).expect("verifies against original");
        }
        other => panic!("expected INFEASIBLE, got {}", tag(&other)),
    }
}

// ---- multiple inequality rows: folding ONE is still sound ----

/// `R` itself contains several inequality rows; the margin row is just one of
/// them. Folding it into the objective while the others stay as constraints
/// must still give the correct feasibility verdict.
#[test]
fn multiple_inequality_rows_fold_one_soundly() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 10.0);
    let y = m.add_col(0.0, 10.0);
    // Several ordinary inequality rows in R.
    m.add_row(3.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]); // x+y >= 3
    m.add_row(f64::NEG_INFINITY, 8.0, &[(x, 1.0)]); //        x   <= 8
    m.add_row(1.0, f64::INFINITY, &[(y, 1.0)]); //            y   >= 1
                                                // The band: x <= 0.5. With x+y>=3, y>=1, x can still be 0 (y=3), so min x=0
                                                // <= 0.5 -> the band IS reachable -> original FEASIBLE.
    let vrow = m.add_row(f64::NEG_INFINITY, 0.5, &[(x, 1.0)]);
    let plain = m.clone();
    m.mark_margin_row(vrow).expect("one-sided");
    assert_reframe_matches_plain(&m, &plain, true);

    // Now make the band unreachable: x >= 6 while x <= 8, but also x+y>=3 and a
    // tightening row x+y <= 5 with y>=1 forces x <= 4 -> x >= 6 unreachable.
    let mut m2 = Model::new();
    let x = m2.add_col(0.0, 10.0);
    let y = m2.add_col(0.0, 10.0);
    m2.add_row(3.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]); // x+y >= 3
    m2.add_row(f64::NEG_INFINITY, 5.0, &[(x, 1.0), (y, 1.0)]); // x+y <= 5
    m2.add_row(1.0, f64::INFINITY, &[(y, 1.0)]); // y >= 1 -> x <= 4
    let vrow2 = m2.add_row(6.0, f64::INFINITY, &[(x, 1.0)]); // band: x >= 6 (unreachable)
    let plain2 = m2.clone();
    m2.mark_margin_row(vrow2).expect("one-sided");
    assert_reframe_matches_plain(&m2, &plain2, false);
}

// ---- fail-safe: kill switch and ill-fitting shapes fall back ----

/// With the kill switch set, the reframe declines and the plain feasibility
/// solve decides — same verdict.
#[test]
fn kill_switch_falls_back_to_plain() {
    let (mark, plain) = build(false, 1.5, 2.0, true, 1.0);
    // Safe: this crate's tests are single-process; set/solve/reset in sequence.
    std::env::set_var("AY_MILP_NO_MARGIN_REFRAME", "1");
    let reframed = solve(&mark);
    let feas = solve(&plain);
    std::env::remove_var("AY_MILP_NO_MARGIN_REFRAME");
    assert_eq!(
        is_sat(&reframed),
        is_sat(&feas),
        "kill-switched reframe must equal plain feasibility ({} vs {})",
        tag(&reframed),
        tag(&feas)
    );
    assert!(
        reframed.is_infeasible(),
        "still the correct INFEASIBLE verdict"
    );
}

/// A two-sided (range) or equality row is not a single margin: `mark_margin_row`
/// must reject it, so the reframe can never fire on an ambiguous shape.
#[test]
fn non_one_sided_rows_are_rejected() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 10.0);
    let range = m.add_row(1.0, 5.0, &[(x, 1.0)]); // two-sided
    assert!(
        m.mark_margin_row(range).is_err(),
        "range row must be rejected"
    );
    let eq = m.add_row(3.0, 3.0, &[(x, 1.0)]); // equality
    assert!(
        m.mark_margin_row(eq).is_err(),
        "equality row must be rejected"
    );
    let empty = m.add_row(f64::NEG_INFINITY, 1.0, &[]); // no coefficients
    assert!(
        m.mark_margin_row(empty).is_err(),
        "empty row must be rejected"
    );
    assert!(
        m.margin_row().is_none(),
        "no margin should be set after failures"
    );
}

/// A model that names a margin but also carries a REAL objective is a misuse:
/// the reframe declines (objective ≢ 0) and the plain optimization runs.
#[test]
fn nonzero_objective_declines_reframe() {
    use ay_milp::Sense;
    let mut m = Model::new();
    let x = m.add_col(0.0, 10.0);
    let y = m.add_col(0.0, 10.0);
    m.add_row(3.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
    let vrow = m.add_row(f64::NEG_INFINITY, 0.5, &[(x, 1.0)]);
    m.set_objective(&[(x, 1.0), (y, 1.0)], Sense::Minimize); // real objective
    m.mark_margin_row(vrow).expect("one-sided");
    // The reframe gate declines (objective ≢ 0): the plain optimization runs and
    // returns the genuine optimum of the model WITH the band row as a constraint.
    match solve(&m) {
        Outcome::Optimal { value, .. } => {
            // min x+y s.t. x+y>=3, x<=0.5 -> x=0.5, y=2.5 -> 3. The band is a
            // hard constraint here (not folded away), so the optimum is 3.
            assert_eq!(value, num_rational::BigRational::from_integer(3.into()));
        }
        other => panic!("expected OPTIMAL 3, got {}", tag(&other)),
    }
}
