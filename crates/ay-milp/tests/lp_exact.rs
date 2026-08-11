// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-lane LP tests: geometry_consumer twin pairs for optima, infeasibility, and
//! certificates (the development design notes §3).

use ay_milp::{
    read_mps, BabSession, BoundSide, Col, FactRef, LpSession, Model, Multiplier, Outcome, Sense,
    SolveOpts, UnknownReason,
};
use num_rational::BigRational;
use num_traits::One;
use std::path::Path;

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

/// The R1 ny-repro shape: c0, c1 in [0,1], c0 + c1 − c4 = 1.
/// True max of c4 is 1, true min is −1.
fn ny_repro_model() -> (Model, Col) {
    let mut m = Model::new();
    let c0 = m.add_col(0.0, 1.0);
    let c1 = m.add_col(0.0, 1.0);
    let c4 = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    m.add_row(1.0, 1.0, &[(c0, 1.0), (c1, 1.0), (c4, -1.0)]);
    (m, c4)
}

#[test]
fn ny_repro_maximize_reports_exact_optimum() {
    let (m, c4) = ny_repro_model();
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    match s.optimize(c4, Sense::Maximize).unwrap() {
        Outcome::Optimal {
            value,
            model_values,
            cert,
        } => {
            assert_eq!(value, BigRational::one(), "true max is 1, not -1/2^128");
            m.check_point(&model_values).unwrap();
            assert_eq!(m.num_cols(), model_values.len());
            let cert = cert.expect("exact lane always certifies");
            cert.verify(&m).unwrap();
            assert_eq!(cert.bound, BigRational::one());
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

#[test]
fn ny_repro_minimize_reports_exact_optimum() {
    let (m, c4) = ny_repro_model();
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    match s.optimize(c4, Sense::Minimize).unwrap() {
        Outcome::Optimal { value, cert, .. } => {
            assert_eq!(value, rat(-1, 1));
            cert.expect("certified").verify(&m).unwrap();
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

/// FALSE VARIANT (must refute): a tampered optimality certificate fails
/// independent verification.
#[test]
fn tampered_optimality_certificate_refutes() {
    let (m, c4) = ny_repro_model();
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    let Outcome::Optimal {
        cert: Some(cert), ..
    } = s.optimize(c4, Sense::Maximize).unwrap()
    else {
        panic!("expected certified Optimal");
    };
    // Claim a stronger bound than proved.
    let mut too_strong = cert.clone();
    too_strong.bound += BigRational::one();
    assert!(too_strong.verify(&m).is_err(), "inflated bound must refute");
    // Corrupt a multiplier.
    let mut wrong_mult = cert.clone();
    wrong_mult.multipliers[0].coeff += rat(1, 7);
    assert!(
        wrong_mult.verify(&m).is_err(),
        "corrupt multiplier must refute"
    );
    // Drop a multiplier.
    let mut dropped = cert;
    dropped.multipliers.pop();
    assert!(
        dropped.verify(&m).is_err(),
        "missing multiplier must refute"
    );
}

#[test]
fn infeasible_lp_yields_verifying_farkas() {
    // x >= 1 (col bound) but x <= 0 (row): infeasible.
    let mut m = Model::new();
    let x = m.add_col(1.0, f64::INFINITY);
    m.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    match s.optimize(x, Sense::Minimize).unwrap() {
        Outcome::Infeasible { cert, .. } => {
            let cert = cert.expect("exact lane certifies infeasibility");
            cert.verify(&m).unwrap();
        }
        other => panic!("expected Infeasible, got {other:?}"),
    }
}

/// TWIN (must prove): relaxing the conflicting bound restores feasibility.
#[test]
fn relaxed_variant_is_feasible() {
    let mut m = Model::new();
    let x = m.add_col(0.0, f64::INFINITY);
    m.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    match s.optimize(x, Sense::Minimize).unwrap() {
        Outcome::Optimal { value, .. } => assert_eq!(value, rat(0, 1)),
        other => panic!("expected Optimal, got {other:?}"),
    }
}

/// FALSE VARIANT (must refute): a Farkas certificate for a FEASIBLE model
/// cannot verify.
#[test]
fn farkas_certificate_on_feasible_model_refutes() {
    let mut infeasible = Model::new();
    let x = infeasible.add_col(1.0, f64::INFINITY);
    infeasible.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
    let mut s = LpSession::new(&infeasible, &SolveOpts::new()).unwrap();
    let Outcome::Infeasible {
        cert: Some(cert), ..
    } = s.optimize(x, Sense::Minimize).unwrap()
    else {
        panic!("expected certified Infeasible");
    };
    // Same shape, but the conflict is gone: x >= 0, x <= 5.
    let mut feasible = Model::new();
    let y = feasible.add_col(0.0, f64::INFINITY);
    feasible.add_row(f64::NEG_INFINITY, 5.0, &[(y, 1.0)]);
    assert!(
        cert.verify(&feasible).is_err(),
        "Farkas cert must not transfer to a feasible model"
    );
}

#[test]
fn unbounded_objective_reported() {
    let mut m = Model::new();
    let x = m.add_col(0.0, f64::INFINITY);
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    match s.optimize(x, Sense::Maximize).unwrap() {
        Outcome::Unbounded => {}
        other => panic!("expected Unbounded, got {other:?}"),
    }
    // TWIN: capping the column bounds the objective.
    let mut capped = Model::new();
    let y = capped.add_col(0.0, 7.0);
    let mut s = LpSession::new(&capped, &SolveOpts::new()).unwrap();
    match s.optimize(y, Sense::Maximize).unwrap() {
        Outcome::Optimal { value, .. } => assert_eq!(value, rat(7, 1)),
        other => panic!("expected Optimal, got {other:?}"),
    }
}

/// The ny ay_backend integration shape: y = 2x, x in [1/4, 1].
#[test]
fn tighten_col_bounds_reports_exact_range() {
    let mut m = Model::new();
    let x = m.add_col(0.25, 1.0);
    let y = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    m.add_row(0.0, 0.0, &[(x, 2.0), (y, -1.0)]);
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    let (lo, hi) = s.tighten_col_bounds(y).unwrap();
    match lo {
        Outcome::Optimal { value, cert, .. } => {
            assert_eq!(value, rat(1, 2));
            cert.expect("certified").verify(&m).unwrap();
        }
        other => panic!("expected Optimal min, got {other:?}"),
    }
    match hi {
        Outcome::Optimal { value, cert, .. } => {
            assert_eq!(value, rat(2, 1));
            cert.expect("certified").verify(&m).unwrap();
        }
        other => panic!("expected Optimal max, got {other:?}"),
    }
}

/// Warm re-solves on one session: alternating objectives stay exact.
#[test]
fn warm_resolves_stay_exact() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 1.0);
    let y = m.add_col(0.0, 1.0);
    m.add_row(f64::NEG_INFINITY, 1.5, &[(x, 1.0), (y, 1.0)]);
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    for _ in 0..3 {
        match s.optimize(x, Sense::Maximize).unwrap() {
            Outcome::Optimal { value, .. } => assert_eq!(value, rat(1, 1)),
            other => panic!("expected Optimal, got {other:?}"),
        }
        // x + y <= 3/2 binds when maximizing the sum through the row's
        // logical variable: max y alone is still 1.
        match s.optimize(y, Sense::Maximize).unwrap() {
            Outcome::Optimal { value, .. } => assert_eq!(value, rat(1, 1)),
            other => panic!("expected Optimal, got {other:?}"),
        }
        match s.optimize(y, Sense::Minimize).unwrap() {
            Outcome::Optimal { value, .. } => assert_eq!(value, rat(0, 1)),
            other => panic!("expected Optimal, got {other:?}"),
        }
    }
}

/// Degenerate passthrough chain (the R1 termination shape): p3 = p2 = p1 =
/// x + y with x, y in [0,1]. Must terminate at the exact optimum 2.
#[test]
fn degenerate_passthrough_terminates_at_optimum() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 1.0);
    let y = m.add_col(0.0, 1.0);
    let p1 = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    let p2 = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    let p3 = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    m.add_row(0.0, 0.0, &[(x, 1.0), (y, 1.0), (p1, -1.0)]);
    m.add_row(0.0, 0.0, &[(p1, 1.0), (p2, -1.0)]);
    m.add_row(0.0, 0.0, &[(p2, 1.0), (p3, -1.0)]);
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    match s.optimize(p3, Sense::Maximize).unwrap() {
        Outcome::Optimal { value, cert, .. } => {
            assert_eq!(value, rat(2, 1));
            cert.expect("certified").verify(&m).unwrap();
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

/// A constant empty row that contradicts its own bound.
#[test]
fn empty_row_infeasibility_certified() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 1.0);
    m.add_row(1.0, 2.0, &[]); // 1 <= 0 <= 2 is false
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    match s.optimize(x, Sense::Minimize).unwrap() {
        Outcome::Infeasible { cert, .. } => cert.expect("certified").verify(&m).unwrap(),
        other => panic!("expected Infeasible, got {other:?}"),
    }
}

/// The model objective (coefficients + offset + sense) solves end-to-end.
#[test]
fn model_objective_with_offset() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 4.0);
    let y = m.add_col(0.0, 4.0);
    m.add_row(f64::NEG_INFINITY, 6.0, &[(x, 1.0), (y, 1.0)]);
    m.set_objective(&[(x, 1.0), (y, 2.0)], Sense::Maximize);
    m.set_objective_offset(10.0);
    let mut s = LpSession::new(&m, &SolveOpts::new()).unwrap();
    match s.optimize_model_objective().unwrap() {
        Outcome::Optimal { value, cert, .. } => {
            // max x + 2y st x+y<=6, x,y<=4: y=4, x=2 -> 10; +offset = 20.
            assert_eq!(value, rat(20, 1));
            let cert = cert.expect("certified");
            cert.verify(&m).unwrap();
            assert_eq!(cert.bound, rat(10, 1), "cert bounds the pure linear form");
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

/// Hand-built certificates are accepted/rejected on their own merits.
#[test]
fn hand_built_farkas_certificate_verifies() {
    // Rows: x + y >= 3 and x + y <= 1 — infeasible.
    let mut m = Model::new();
    let x = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    let y = m.add_col(f64::NEG_INFINITY, f64::INFINITY);
    let r0 = m.add_row(3.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
    let r1 = m.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, 1.0)]);
    let cert = ay_milp::FarkasCertificate {
        multipliers: vec![
            Multiplier {
                fact: FactRef::RowBound {
                    row: r0,
                    side: BoundSide::Lower,
                },
                coeff: BigRational::one(),
            },
            Multiplier {
                fact: FactRef::RowBound {
                    row: r1,
                    side: BoundSide::Upper,
                },
                coeff: BigRational::one(),
            },
        ],
    };
    cert.verify(&m).unwrap();
}

/// The float lane (P1) and the exact rim must agree, exactly.
///
/// `LpSession` runs the f64 revised simplex and then has the basis it proposes
/// adjudicated in exact rationals; a continuous `BabSession` goes straight down
/// the exact rim. They are independent implementations of the same question, so
/// this is the in-crate differential that keeps the fast lane honest: the float
/// lane may only be *fast*, never *different*.
///
/// The instance is sized where the two lanes genuinely diverge in cost (the rim
/// takes tens of seconds on a 60x40 of this shape, the float lane milliseconds),
/// so this also pins that the fast lane is actually engaging.
#[test]
fn float_lane_and_exact_rim_agree_on_a_medium_lp() {
    // Deterministic small-integer LP; x = 0 is feasible, and the box bounds it.
    let mut lcg: u64 = 987_654_321;
    let mut next = || {
        lcg = lcg.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        f64::from(((lcg >> 33) as u32) % 9) - 4.0
    };

    let mut m = Model::new();
    let cols: Vec<_> = (0..40).map(|_| m.add_col(0.0, 10.0)).collect();
    for _ in 0..30 {
        let terms: Vec<_> = cols
            .iter()
            .filter_map(|&c| {
                let a = next();
                (a != 0.0).then_some((c, a))
            })
            .collect();
        if !terms.is_empty() {
            m.add_row(f64::NEG_INFINITY, 25.0, &terms);
        }
    }
    let obj: Vec<_> = cols.iter().map(|&c| (c, next())).collect();
    m.set_objective(&obj, Sense::Maximize);

    // Fast lane: float search, exact adjudication.
    let mut fast = LpSession::new(&m, &SolveOpts::new()).unwrap();
    let fast_out = fast.optimize_model_objective().unwrap();

    // Slow lane: the exact rim, no floats anywhere.
    let mut rim = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    let rim_out = rim.check().unwrap();

    match (&fast_out, &rim_out) {
        (
            Outcome::Optimal {
                value: v1,
                model_values: p1,
                cert,
            },
            Outcome::Optimal { value: v2, .. },
        ) => {
            assert_eq!(*v1, *v2, "the float lane must not change the optimum");
            m.check_point(p1).expect("its point must be feasible");
            let cert = cert.as_ref().expect("the float lane must certify");
            cert.verify(&m).expect("and the certificate must verify");
            assert_eq!(cert.bound, *v1, "the dual bound must MEET the optimum");
        }
        other => panic!("expected both lanes Optimal, got {other:?}"),
    }
}

/// COVERAGE + SOUNDNESS (r12 rational coefficients). A coefficient of `2^53 + 1`
/// is not an `f64` (it rounds DOWN to `2^53`), so the reader stores the rounded
/// proxy for the float lane and the TRUE rational in the side-store instead of
/// refusing the file. The model is genuinely feasible on its true coefficients
/// (`(2^53+1)·x >= 2^53+1` ⇔ `x >= 1`, optimum `x = 1`), so the solver must
/// return a feasible answer or a clean `Unknown` — and it must NEVER call it
/// infeasible or hand back a point that violates the TRUE row.
#[test]
fn inexact_coefficient_model_solves_or_declines_but_never_lies() {
    // 2^53 + 1 = 9007199254740993, the smallest positive integer no f64 holds.
    let src = "\
NAME          inexact
ROWS
 N  obj
 G  r1
COLUMNS
    MARK0     'MARKER'                 'INTORG'
    x         obj              1.0   r1        9007199254740993
    MARK1     'MARKER'                 'INTEND'
RHS
    RHS       r1        9007199254740993
BOUNDS
 UP BND       x                  5
ENDATA
";
    let prob = read_mps(src).expect("an inexact coefficient must PARSE, not refuse");
    let m = prob.model;
    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).expect("session");
    match s.check().expect("check") {
        // A feasible incumbent (an inexact MILP cannot certify integer
        // optimality here, so `Optimal` is downgraded to `Feasible`): its point
        // must satisfy the TRUE model.
        Outcome::Feasible { model_values, .. } => {
            m.check_point(&model_values)
                .expect("a reported feasible point must satisfy the TRUE row");
            // The only feasible integers in [0,5] are 1..=5; the value equals x.
            let v = m.objective_value_at(&model_values);
            assert!(v >= BigRational::one(), "true feasibility requires x >= 1");
        }
        // The one thing a feasible model may NEVER be told it is.
        other @ (Outcome::Infeasible { .. } | Outcome::Unbounded) => {
            panic!("a feasible inexact model was wrongly adjudicated {other:?}");
        }
        // An `Optimal` here is legal ONLY when it is the TRUE optimum.
        //
        // `fail_closed_for_inexact` exists to stop a float search over rounded
        // proxy coefficients shipping an optimality claim it cannot support,
        // and `finish_exact_reduction` deliberately skips it (session.rs) for
        // lanes that never touched the proxy: an exact structural reduction
        // reads every row and objective fact through the model's rational side
        // store, so its verdict has no proxy dependency to fail closed on.
        //
        // So the assertion is not "no Optimal" — that would erase correct exact
        // verdicts and undo a deliberate design. It is "no WRONG Optimal": the
        // point must satisfy the TRUE row, and the value must be the true
        // optimum, which is exactly 1 (x >= (2^53+1)/(2^53+1) = 1 over the true
        // coefficients; the rounded proxy is a DIFFERENT system).
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            m.check_point(&model_values)
                .expect("an Optimal point must satisfy the TRUE row");
            assert_eq!(
                value,
                m.objective_value_at(&model_values),
                "the reported value must be the TRUE objective at the reported point"
            );
            assert_eq!(
                value,
                BigRational::one(),
                "x = 1 is the true optimum; anything else is the rounded proxy's \
                 answer wearing an exact verdict's clothes"
            );
        }
        // Fail-closed is a SUCCESS: an honest non-answer (`Unknown`/`Bound`),
        // never a wrong one.
        _ => {}
    }
}

/// THE INVARIANT THAT JUSTIFIES SKIPPING `fail_closed_for_inexact`.
///
/// `finish_exact_reduction` is sound only because every lane that exits through
/// it reads model facts from the exact rational side store — `row_coeff_exact`,
/// `obj_coeff_exact_at`, `row_lb_exact`/`row_ub_exact`, `col_*_exact` — and
/// never from the `f64` proxy the reader keeps for the float lane. Add a lane
/// to that block without the property and a rounded-proxy search result is
/// silently relabelled an exact verdict, with the float-search backstop
/// removed.
///
/// Nothing enforced this structurally, so it is enforced here: a source scan,
/// in the style of `tests/env_ledger.rs`, over the modules the exact-reduction
/// block dispatches to.
#[test]
fn every_exact_reduction_lane_reads_the_rational_side_store() {
    // Each module reachable from the `finish_exact_reduction` block in
    // `BabSession::check`. Adding a route there means adding it here.
    const LANES: &[&str] = &[
        "pb_translate.rs",
        "direct_cnf.rs",
        "sat_relu.rs",
        "hybrid_pb_lp.rs",
        "hybrid_integer_lift.rs",
        "network_design_pb.rs",
        "open_domain.rs",
        "parity.rs",
    ];
    // Any one of these proves the lane consults the exact side store.
    const EXACT_READS: &[&str] = &[
        "row_coeff_exact",
        "obj_coeff_exact_at",
        "row_lb_exact",
        "row_ub_exact",
        "col_lb_exact",
        "col_ub_exact",
        "obj_offset_exact",
        "has_inexact_coeffs",
    ];
    let src = Path::new(env!("CARGO_MANIFEST_DIR")).join("src");
    for lane in LANES {
        let path = src.join(lane);
        let text = std::fs::read_to_string(&path)
            .unwrap_or_else(|e| panic!("exact-reduction lane {lane} is unreadable: {e}"));
        assert!(
            EXACT_READS.iter().any(|needle| text.contains(needle)),
            "{lane} exits through `finish_exact_reduction`, which SKIPS \
             `fail_closed_for_inexact`, but reads no exact side-store accessor. \
             Either it reads the rounded f64 proxy — in which case its verdict \
             is not exact and the skip is unsound — or it declines outright and \
             should say so here."
        );
    }
}

/// An objective-row RHS is an objective offset. When its exact MPS value is
/// not representable as `f64`, the continuous BabSession certificate path must
/// add the side-store value rather than the rounded search proxy.
#[test]
fn inexact_objective_offset_survives_bab_certificate_end_to_end() {
    let src = "\
NAME          inexact-offset
ROWS
 N  obj
COLUMNS
    x         obj                       1
RHS
    RHS       obj       -9007199254740993
BOUNDS
 FX BND       x                         0
ENDATA
";
    let prob = read_mps(src).expect("inexact objective offset must parse");
    let mut s = BabSession::new(prob.model.clone(), &SolveOpts::new()).expect("continuous session");
    match s.check().expect("check") {
        Outcome::Optimal {
            value,
            model_values,
            cert,
        } => {
            assert_eq!(
                prob.unscale(&value),
                rat(9_007_199_254_740_993, 1),
                "reported value must use the exact objective offset"
            );
            assert_eq!(value, prob.model.objective_value_at(&model_values));
            let cert = cert.expect("continuous optimum must be certified");
            cert.verify(&prob.model).expect("certificate must verify");
            assert_eq!(cert.bound, rat(0, 1), "x is fixed to zero");
        }
        other => panic!("expected certified Optimal, got {other:?}"),
    }
}

/// Native branch-and-bound has no unbounded ray to replay against the exact
/// side-store. An inexact integral model must therefore decline an `Unbounded`
/// search opinion instead of publishing it as a proof.
#[test]
fn native_inexact_unbounded_fails_closed_end_to_end() {
    let src = "\
NAME          inexact-unbounded
OBJSENSE MAX
ROWS
 N  obj
COLUMNS
    MARK0     'MARKER'                 'INTORG'
    x         obj        9007199254740993
    MARK1     'MARKER'                 'INTEND'
BOUNDS
 LO BND       x                         0
ENDATA
";
    let prob = read_mps(src).expect("inexact integer objective must parse");
    let mut s = BabSession::new(prob.model.clone(), &SolveOpts::new()).expect("native session");
    assert!(matches!(
        s.check().expect("check"),
        Outcome::Unknown {
            reason: UnknownReason::CertificateUnavailable
        }
    ));
}
