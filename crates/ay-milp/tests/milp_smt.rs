// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MILP tests through the L0 `smt` lane: binary columns, scoped
//! `fix_col`/`add_row`, and the LP-relaxation Farkas enrichment.

#![cfg(feature = "smt")]

use ay_milp::{BabSession, Model, Outcome, Sense, SolveOpts, UnknownReason};
use num_rational::BigRational;
use std::time::{Duration, Instant};

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

/// Options that pin the solve on NATIVE branch-and-bound, so the LP-relaxation
/// Farkas lane this file is about is the lane that answers.
///
/// The exact structure-recognition routes settle these small binary models
/// before an LP relaxation is built, refuting them with a PB decision DAG
/// instead. That artifact is independently replayable and is tamper-tested per
/// format in `tests/cert_io.rs` section (b2); what it is NOT is a
/// `FarkasCertificate` on the `Outcome`. A test that asserts a Farkas must ask
/// for the lane that makes one.
fn native_opts() -> SolveOpts {
    SolveOpts::new().with_structure_routing(false)
}

#[test]
fn binary_feasibility_finds_witness() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    m.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    match s.check().unwrap() {
        Outcome::Feasible { model_values, .. } => {
            m.check_point(&model_values).unwrap();
            assert_eq!(
                model_values[x.index()].clone() + model_values[y.index()].clone(),
                rat(1, 1)
            );
        }
        other => panic!("expected Feasible, got {other:?}"),
    }
}

#[test]
fn expired_deadline_fails_closed_before_binary_feasibility() {
    let mut m = Model::new();
    let _ = m.add_binary_col();
    let expired_deadline = Instant::now()
        .checked_sub(Duration::from_millis(1))
        .expect("test clock must support a one-millisecond lookback");
    let opts = SolveOpts::new().with_deadline(expired_deadline);
    let mut session = BabSession::new(m.clone(), &opts).unwrap();
    assert!(matches!(
        session.check().unwrap(),
        Outcome::Unknown {
            reason: UnknownReason::Timeout
        }
    ));
}

/// FALSE VARIANT (must refute): contradictory rows are Infeasible, and the
/// LP-relaxation Farkas certificate verifies.
#[test]
fn binary_lp_infeasibility_certified() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    m.add_row(2.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
    m.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, 1.0)]);
    let mut s = BabSession::new(m.clone(), &native_opts()).unwrap();
    match s.check().unwrap() {
        Outcome::Infeasible { cert, .. } => {
            let cert = cert.expect("LP-relaxation conflict must be certified");
            cert.verify(&m).unwrap();
        }
        other => panic!("expected Infeasible, got {other:?}"),
    }

    // ... and under the SHIPPED default, where a routed lane owns it, the
    // verdict must still arrive with evidence that replays against this model.
    let mut routed = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    match routed.check().unwrap() {
        Outcome::Infeasible { cert, tree_cert } => {
            let on_outcome = cert.is_some() || tree_cert.is_some();
            let on_session = routed.single_row_dp_infeasibility_certificate().is_some()
                || routed.multi_row_bdd_infeasibility_certificate().is_some();
            assert!(
                on_outcome || on_session,
                "the default posture returned a bare Infeasible: no Farkas, no \
                 tree, no typed exact-reduction artifact. Nothing re-checks such \
                 a verdict at the session boundary."
            );
        }
        other => panic!("expected Infeasible, got {other:?}"),
    }
}

/// Integer-infeasible but LP-feasible: no ROOT certificate exists (the
/// relaxation is satisfiable), so `cert` stays honestly `None` — and the P2
/// case-split lane may close the gap with a whole-tree certificate instead.
/// Whether `tree_cert` arrives here depends on which engine layer settles the
/// instance (presolve's propagation proof carries no tree), so this test pins
/// only what must ALWAYS hold: no root Farkas, and any tree certificate that
/// does arrive must verify against the caller's model.
#[test]
fn integer_infeasibility_reports_honestly_uncertified() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    // x + y = 1/2 has the LP point (1/4, 1/4) but no 0/1 point.
    m.add_row(0.5, 0.5, &[(x, 1.0), (y, 1.0)]);
    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    match s.check().unwrap() {
        Outcome::Infeasible { cert, tree_cert } => {
            assert!(cert.is_none(), "the satisfiable relaxation has no Farkas");
            if let Some(tree_cert) = tree_cert {
                tree_cert.verify(&m).unwrap();
            }
        }
        other => panic!("expected Infeasible, got {other:?}"),
    }
}

/// FAIL-CLOSED: under `require_certificates` a caller never receives a bare
/// verdict. Either the verdict is withheld as `Unknown(CertificateUnavailable)`,
/// or it arrives WITH evidence that replays against the caller's own model.
///
/// The original form of this test pinned the first branch only, because
/// `x + y = 1/2` over binaries had no exportable proof at all. It does now —
/// the single-row DP route refutes it succinctly and `ay-milp verify` exits 0 —
/// so demanding `Unknown` here would demand that the engine THROW AWAY a real
/// proof, which is strictly worse than the behaviour the test was written to
/// protect.
///
/// What must not be relaxed is the disjunction itself. Widening this to
/// `matches!(out, Outcome::Infeasible { .. })` would delete the guarantee at
/// exactly the moment `Outcome` lost the ability to express it: `Infeasible`
/// carries `cert`/`tree_cert` and nothing else, so a supplementally-proved
/// verdict and a bare one are the same value. The proof lives on the session,
/// and that is where this test looks.
#[test]
fn require_certificates_degrades_uncertified_verdicts() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    m.add_row(0.5, 0.5, &[(x, 1.0), (y, 1.0)]);
    let opts = SolveOpts::new().with_require_certificates(true);
    let mut s = BabSession::new(m.clone(), &opts).unwrap();
    match s.check().unwrap() {
        Outcome::Unknown {
            reason: UnknownReason::CertificateUnavailable,
        } => {}
        Outcome::Infeasible { cert, tree_cert } => {
            let mut evidence = 0usize;
            if let Some(cert) = &cert {
                cert.verify(&m).expect("an admitted Farkas must replay");
                evidence += 1;
            }
            if let Some(tree_cert) = &tree_cert {
                tree_cert
                    .verify(&m)
                    .expect("an admitted tree cert must replay");
                evidence += 1;
            }
            if let Some(artifact) = s.single_row_dp_infeasibility_certificate() {
                ay_milp::verify_single_row_dp_infeasibility_certificate(&m, artifact)
                    .expect("an admitted single-row DP artifact must replay");
                evidence += 1;
            }
            if let Some(artifact) = s.multi_row_bdd_infeasibility_certificate() {
                ay_milp::verify_multi_row_bdd_infeasibility_certificate(&m, artifact)
                    .expect("an admitted multi-row BDD artifact must replay");
                evidence += 1;
            }
            assert!(
                evidence > 0,
                "`require_certificates` admitted an INFEASIBLE with no \
                 independently checkable evidence anywhere — that is the bare \
                 verdict this test exists to forbid"
            );
        }
        other => panic!(
            "expected Unknown(CertificateUnavailable) or certified Infeasible, got {other:?}"
        ),
    }
}

/// The composed fail-closed invariant, over every infeasible shape this file
/// builds and both routing postures: `require_certificates` must NEVER yield an
/// `Infeasible` that no artifact backs.
///
/// The policy gate itself is proved directly by
/// `session::certificate_policy_tests::full_policy_accepts_typed_side_refutations_only_when_named`
/// (bare + `SupplementalProof::None` -> `Unknown(CertificateUnavailable)`).
/// What THIS test adds is that no lane reaches the gate carrying a supplemental
/// proof it did not earn — i.e. every early return that claims certificate
/// posture really did publish a replayable artifact.
///
/// Deliberately does not assume any particular model is unprovable. Such a test
/// goes vacuous the moment a new lane learns to prove the model, and then it
/// asserts nothing while still looking like a fail-closed test.
#[test]
fn require_certificates_never_yields_an_unbacked_infeasible() {
    let mut root_conflict = Model::new();
    let a = root_conflict.add_binary_col();
    let b = root_conflict.add_binary_col();
    root_conflict.add_row(2.0, f64::INFINITY, &[(a, 1.0), (b, 1.0)]);
    root_conflict.add_row(f64::NEG_INFINITY, 1.0, &[(a, 1.0), (b, 1.0)]);

    let mut case_split = Model::new();
    let c = case_split.add_binary_col();
    let d = case_split.add_binary_col();
    case_split.add_row(0.5, 0.5, &[(c, 1.0), (d, 1.0)]);

    let mut inexact = Model::new();
    let e = inexact.add_int_col(0.0, f64::INFINITY);
    inexact.add_row(1.0, f64::INFINITY, &[(e, 0.1)]);
    inexact.add_row(f64::NEG_INFINITY, 0.0, &[(e, 0.1)]);

    for m in [root_conflict, case_split, inexact] {
        for routing in [true, false] {
            let opts = SolveOpts::new()
                .with_require_certificates(true)
                .with_structure_routing(routing);
            let mut s = BabSession::new(m.clone(), &opts).unwrap();
            let outcome = s.check().unwrap();
            let Outcome::Infeasible { cert, tree_cert } = &outcome else {
                continue; // Unknown / withheld is the other legal answer.
            };
            let mut backed = cert.is_some() || tree_cert.is_some();
            if let Some(artifact) = s.single_row_dp_infeasibility_certificate() {
                ay_milp::verify_single_row_dp_infeasibility_certificate(&m, artifact)
                    .expect("a published single-row DP artifact must replay");
                backed = true;
            }
            if let Some(artifact) = s.multi_row_bdd_infeasibility_certificate() {
                ay_milp::verify_multi_row_bdd_infeasibility_certificate(&m, artifact)
                    .expect("a published multi-row BDD artifact must replay");
                backed = true;
            }
            if s.parity_infeasibility_certificate().is_some()
                || s.hybrid_pb_lp_infeasibility_certificate().is_some()
                || s.hybrid_integer_lift_infeasibility_certificate().is_some()
                || s.network_design_infeasibility_certificate().is_some()
                || s.open_domain_single_row_dp_infeasibility_certificate()
                    .is_some()
                || s.open_domain_multi_row_bdd_infeasibility_certificate()
                    .is_some()
            {
                backed = true;
            }
            assert!(
                backed,
                "`require_certificates` returned an INFEASIBLE with no \
                 independently checkable evidence (routing={routing}): {outcome:?}"
            );
        }
    }
}

#[test]
fn minimize_over_binaries_reports_exact_optimum() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    m.add_row(1.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
    m.set_objective(&[(x, 1.0), (y, 2.0)], Sense::Minimize);
    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    match s.check().unwrap() {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            assert_eq!(value, rat(1, 1), "x=1, y=0 is optimal");
            m.check_point(&model_values).unwrap();
        }
        other => panic!("expected Optimal, got {other:?}"),
    }
}

/// TWIN: maximize on the same shape (the P0 subprocess lane had to rewrite
/// maximize through an aux column; in-process post-R1 it must be direct).
#[test]
fn maximize_over_binaries_reports_exact_optimum() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    m.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, 1.0)]);
    m.set_objective(&[(x, 1.0), (y, 2.0)], Sense::Maximize);
    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    match s.check().unwrap() {
        Outcome::Optimal { value, .. } => assert_eq!(value, rat(2, 1), "y=1, x=0"),
        other => panic!("expected Optimal, got {other:?}"),
    }
}

/// Scoped phase-split: fix binaries under push/pop, the downstream optimization consumer's 2^k racing shape.
#[test]
fn scoped_fix_col_partitions_and_restores() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    m.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
    // The scoped conflict below is asserted to be Farkas-certifiable, which is
    // a claim about the LP relaxation lane; see `native_opts`.
    let mut s = BabSession::new(m.clone(), &native_opts()).unwrap();

    // Split x=0: y must be 1.
    s.push().unwrap();
    s.fix_col(x, 0.0).unwrap();
    match s.check().unwrap() {
        Outcome::Feasible { model_values, .. } => {
            assert_eq!(model_values[y.index()], rat(1, 1));
        }
        other => panic!("x=0 split should be feasible, got {other:?}"),
    }
    s.pop().unwrap();

    // Split x=0 AND y=0: infeasible, certified by the LP relaxation.
    s.push().unwrap();
    s.fix_col(x, 0.0).unwrap();
    s.fix_col(y, 0.0).unwrap();
    match s.check().unwrap() {
        Outcome::Infeasible { cert, .. } => {
            // The fixings are scoped MODEL rows, so the certificate must
            // verify against the session's current view — which pops below.
            assert!(cert.is_some(), "relaxation conflict is certifiable");
        }
        other => panic!("x=y=0 split should be infeasible, got {other:?}"),
    }
    s.pop().unwrap();

    // Back at the root: still feasible.
    match s.check().unwrap() {
        Outcome::Feasible { .. } => {}
        other => panic!("root should be feasible after pops, got {other:?}"),
    }
}

/// add_row inside a scope is retracted by pop.
#[test]
fn scoped_add_row_is_retracted() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    s.push().unwrap();
    s.add_row(1.0, 1.0, &[(x, 1.0)]).unwrap(); // force x = 1
    match s.check().unwrap() {
        Outcome::Feasible { model_values, .. } => assert_eq!(model_values[0], rat(1, 1)),
        other => panic!("expected Feasible, got {other:?}"),
    }
    s.pop().unwrap();
    s.push().unwrap();
    s.add_row(0.0, 0.0, &[(x, 1.0)]).unwrap(); // force x = 0
    match s.check().unwrap() {
        Outcome::Feasible { model_values, .. } => assert_eq!(model_values[0], rat(0, 1)),
        other => panic!("expected Feasible, got {other:?}"),
    }
    s.pop().unwrap();
}

#[test]
fn pop_at_depth_zero_is_a_session_error() {
    let mut m = Model::new();
    let _ = m.add_binary_col();
    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    assert!(s.pop().is_err());
}

/// Continuous models route through the exact rim inside BabSession and get
/// certificates without the smt lane.
#[test]
fn continuous_model_in_bab_session_is_certified() {
    let mut m = Model::new();
    let x = m.add_col(0.0, 1.0);
    m.add_row(2.0, f64::INFINITY, &[(x, 1.0)]); // x >= 2 vs x <= 1
    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    match s.check().unwrap() {
        Outcome::Infeasible { cert, .. } => cert.expect("exact rim certifies").verify(&m).unwrap(),
        other => panic!("expected Infeasible, got {other:?}"),
    }
}

/// Advice-only surfaces accept input at L0.
#[test]
fn advice_surfaces_accept_input() {
    let mut m = Model::new();
    let x = m.add_binary_col();
    let y = m.add_binary_col();
    m.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    s.seed_incumbent(&[1.0, 0.0]);
    s.hint_branch_order(&[y, x]);
    s.shortlist_root_strong_branch_candidates(&[x, y]);
    assert_eq!(s.incumbent_seed(), Some(&[1.0, 0.0][..]));
    assert_eq!(s.branch_hints(), &[y, x]);
    assert_eq!(s.root_strong_branch_shortlist(), &[x, y]);
    assert!(s.harvest_cuts().is_empty(), "L0 lanes never emit cuts");
    assert!(s.check().unwrap().is_sat());
}

/// An equality row reaches the solver as a `>=`/`<=` PAIR (this crate never
/// lowers `=`, so the certificate lane stays alive — see `smt.rs`). The LRA
/// simplex used to cycle on the degenerate vertex that shape produces, burn its
/// 10_000-iteration budget, and hand back `unknown` for a two-variable LP.
///
/// x0 - x1 = 1 over x0 in [0,1], x1 in [-1,1]; minimize -x0 + 2*x1.
/// Substituting gives obj = x0 - 2, so the optimum is exactly -2 at (0, -1).
#[test]
fn equality_row_as_inequality_pair_reports_exact_optimum() {
    let mut m = Model::new();
    let x0 = m.add_col(0.0, 1.0);
    let x1 = m.add_col(-1.0, 1.0);
    let _b = m.add_binary_col(); // routes through the smt lane
    m.add_row(1.0, 1.0, &[(x0, 1.0), (x1, -1.0)]);
    m.set_objective(&[(x0, -1.0), (x1, 2.0)], Sense::Minimize);

    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    match s.check().unwrap() {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            assert_eq!(value, rat(-2, 1), "true optimum is -2 (z3-confirmed)");
            m.check_point(&model_values).unwrap();
            assert_eq!(model_values[x0.index()], rat(0, 1));
            assert_eq!(model_values[x1.index()], rat(-1, 1));
        }
        other => panic!("expected Optimal(-2), got {other:?}"),
    }
}

/// Negative control for the pair-encoding test: the same shape with the row
/// bound moved past the box is genuinely infeasible, so the lane must REFUTE it
/// rather than report the (now unreachable) optimum. x0 - x1 = 5 cannot hold
/// for x0 <= 1, x1 >= -1.
#[test]
fn equality_row_as_inequality_pair_outside_the_box_is_infeasible() {
    let mut m = Model::new();
    let x0 = m.add_col(0.0, 1.0);
    let x1 = m.add_col(-1.0, 1.0);
    let _b = m.add_binary_col();
    m.add_row(5.0, 5.0, &[(x0, 1.0), (x1, -1.0)]);
    m.set_objective(&[(x0, -1.0), (x1, 2.0)], Sense::Minimize);

    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    let out = s.check().unwrap();
    assert!(
        out.is_infeasible(),
        "x0 - x1 = 5 is unreachable inside the box; expected Infeasible, got {out:?}"
    );
}

/// A fixed column (`lb == ub`) also arrives as a `>=`/`<=` pair. Three or more
/// columns pinned to the SAME value make LRA's final check ask for speculative
/// model equalities (#4906) instead of answering `Sat` — a theory-COMBINATION
/// request that the optimizer used to read as "not applicable", disabling the
/// simplex lane and falling back to a crawl that returned `unknown`.
///
/// Fixed columns are not exotic: they are what `fix_col` produces on every
/// phase-split, so this shape sits under essentially every real MILP.
///
/// c0 = c1 = c3 = 0, c2 in [0,4]; minimize -(c0+c1+c2+c3) = -c2 → -4 at c2 = 4.
#[test]
fn three_columns_pinned_to_one_value_reports_exact_optimum() {
    let mut m = Model::new();
    let c0 = m.add_col(0.0, 0.0);
    let c1 = m.add_col(0.0, 0.0);
    let c2 = m.add_col(0.0, 4.0);
    let c3 = m.add_col(0.0, 0.0);
    let _b = m.add_binary_col();
    m.set_objective(
        &[(c0, -1.0), (c1, -1.0), (c2, -1.0), (c3, -1.0)],
        Sense::Minimize,
    );

    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    match s.check().unwrap() {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            assert_eq!(value, rat(-4, 1), "true optimum is -4 (z3-confirmed)");
            m.check_point(&model_values).unwrap();
            assert_eq!(model_values[c2.index()], rat(4, 1));
        }
        other => panic!("expected Optimal(-4), got {other:?}"),
    }
}

/// The same pinned-column shape reached through `fix_col` rather than through
/// the column bounds — the phase-split path ny actually drives, and the reason
/// this bug reached every real MILP rather than a corner of the API. Three
/// columns pinned to the same value inside one scope must still optimize
/// exactly, and the scope must restore cleanly afterwards.
#[test]
fn fix_col_pinning_still_reports_exact_optimum() {
    let mut m = Model::new();
    let c0 = m.add_col(0.0, 1.0);
    let c1 = m.add_col(0.0, 1.0);
    let c2 = m.add_col(0.0, 4.0);
    let c3 = m.add_col(0.0, 1.0);
    let b = m.add_binary_col();
    m.set_objective(
        &[(c0, -1.0), (c1, -1.0), (c2, -1.0), (c3, -1.0)],
        Sense::Minimize,
    );

    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    s.push().unwrap();
    s.fix_col(c0, 0.0).unwrap();
    s.fix_col(c1, 0.0).unwrap();
    s.fix_col(c3, 0.0).unwrap();
    match s.check().unwrap() {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            assert_eq!(
                value,
                rat(-4, 1),
                "c0 = c1 = c3 = 0 pinned, so the optimum is -c2 = -4"
            );
            m.check_point(&model_values).unwrap();
            assert_eq!(model_values[c2.index()], rat(4, 1));
        }
        other => panic!("expected Optimal(-4), got {other:?}"),
    }
    s.pop().unwrap();

    // Out of the scope the pins are gone and the optimum widens to -7.
    match s.check().unwrap() {
        Outcome::Optimal { value, .. } => assert_eq!(
            value,
            rat(-7, 1),
            "unpinned, every column is free to take its upper bound"
        ),
        other => panic!("expected Optimal(-7) after pop, got {other:?}"),
    }
    let _ = b;
}

/// The native branch-and-bound (P2) against an answer HiGHS independently
/// agrees with.
///
/// This 20-binary knapsack is the instance `examples/milp_speed.rs` generates
/// with the default seed; HiGHS puts its primal AND dual bound at 52, so 52 is
/// not ay marking its own homework. The lane it replaces — the ay-dpll `smt`
/// lowering — does not solve this instance at all (`unknown` after 300s), which
/// is why the native lane exists.
#[test]
fn native_branch_and_bound_matches_an_independently_known_optimum() {
    let mut lcg: u64 = 2_026;
    let mut next = || {
        lcg = lcg.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        (lcg >> 33) as u32
    };

    let mut m = Model::new();
    let cols: Vec<_> = (0..20).map(|_| m.add_binary_col()).collect();
    for _ in 0..15 {
        let terms: Vec<_> = cols
            .iter()
            .filter_map(|&c| {
                let a = f64::from(next() % 9) - 4.0;
                (a != 0.0).then_some((c, a))
            })
            .collect();
        if terms.is_empty() {
            continue;
        }
        let b = f64::from(next() % 12) + 3.0;
        m.add_row(f64::NEG_INFINITY, b, &terms);
    }
    let obj: Vec<_> = cols
        .iter()
        .map(|&c| (c, f64::from(next() % 10) + 1.0))
        .collect();
    m.set_objective(&obj, Sense::Maximize);

    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    match s.check().unwrap() {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            assert_eq!(value, rat(52, 1), "HiGHS puts both bounds at 52");
            // The witness must be a real 0/1 point of the real model.
            m.check_point(&model_values)
                .expect("the optimal point must satisfy every row, bound and integrality");
        }
        other => panic!("expected Optimal(52), got {other:?}"),
    }
}

/// The Gomory cut path, against an independently known optimum.
///
/// This 40-binary instance is the one `examples/milp_speed.rs` generates at that
/// size; HiGHS puts its primal bound at 157. It is large enough that the root
/// separates GMI cuts (the 20-binary test above does not), so it is the regression
/// that actually guards them — and the property it guards is the one that matters:
/// **a cut must never delete the optimum.** An invalid cut does not crash, it
/// quietly returns a smaller number, and only a known answer catches that.
#[test]
fn gomory_cuts_preserve_an_independently_known_optimum() {
    let mut lcg: u64 = 2_026;
    let mut next = || {
        lcg = lcg.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        (lcg >> 33) as u32
    };

    let mut m = Model::new();
    let cols: Vec<_> = (0..40).map(|_| m.add_binary_col()).collect();
    for _ in 0..30 {
        let terms: Vec<_> = cols
            .iter()
            .filter_map(|&c| {
                let a = f64::from(next() % 9) - 4.0;
                (a != 0.0).then_some((c, a))
            })
            .collect();
        if terms.is_empty() {
            continue;
        }
        let b = f64::from(next() % 12) + 3.0;
        m.add_row(f64::NEG_INFINITY, b, &terms);
    }
    let obj: Vec<_> = cols
        .iter()
        .map(|&c| (c, f64::from(next() % 10) + 1.0))
        .collect();
    m.set_objective(&obj, Sense::Maximize);

    let mut s = BabSession::new(m.clone(), &SolveOpts::new()).unwrap();
    match s.check().unwrap() {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            assert_eq!(value, rat(157, 1), "HiGHS puts the primal bound at 157");
            m.check_point(&model_values)
                .expect("the optimal point must satisfy the ORIGINAL model");
        }
        other => panic!("expected Optimal(157), got {other:?}"),
    }
}

/// A 70-binary instance must be PROVEN optimal, not merely feasible.
///
/// This one needs 236,499 nodes. It used to return an honest incumbent-only
/// `Feasible` because the node budget was 200,000 — the answer was four seconds of
/// work away and the search was cut off. A budget that low is not a safety limit,
/// it is a silent quality ceiling, and this test is what stops one being
/// reintroduced. HiGHS puts the primal bound at 270.
///
/// This is intentionally part of the default suite: a deadline, rather than a
/// hidden internal node ceiling, is the caller-visible way to bound search.
#[test]
fn seventy_binaries_are_proven_optimal_not_merely_feasible() {
    let mut lcg: u64 = 2_026;
    let mut next = || {
        lcg = lcg.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        (lcg >> 33) as u32
    };

    let mut m = Model::new();
    let cols: Vec<_> = (0..70).map(|_| m.add_binary_col()).collect();
    for _ in 0..52 {
        let terms: Vec<_> = cols
            .iter()
            .filter_map(|&c| {
                let a = f64::from(next() % 9) - 4.0;
                (a != 0.0).then_some((c, a))
            })
            .collect();
        if terms.is_empty() {
            continue;
        }
        let b = f64::from(next() % 12) + 3.0;
        m.add_row(f64::NEG_INFINITY, b, &terms);
    }
    let obj: Vec<_> = cols
        .iter()
        .map(|&c| (c, f64::from(next() % 10) + 1.0))
        .collect();
    m.set_objective(&obj, Sense::Maximize);

    let opts = SolveOpts::new().with_time_limit(Duration::from_mins(2));
    let mut s = BabSession::new(m.clone(), &opts).unwrap();
    match s.check().unwrap() {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            assert_eq!(value, rat(270, 1), "HiGHS puts the primal bound at 270");
            m.check_point(&model_values)
                .expect("the point must be real");
        }
        other => panic!("expected a PROVEN Optimal(270), got {other:?}"),
    }
}

/// SOUNDNESS, BRUTE-FORCED: the optimum reported for a model with GENERAL INTEGER columns must be
/// the optimum, checked against every point of its box.
///
/// This exists because a real one got through. Reduced-cost fixing pins a column when moving it off
/// its bound cannot pay for itself — and it charged the move at the column's WHOLE SPAN rather than
/// at one unit. For a binary those are the same thing (span = 1), so a binary-only corpus never
/// sees it; give a column the range [0, 10] and the arithmetic overstates the cost tenfold and pins
/// a column that could have stepped one unit and paid. On MIPLIB's qnet1 (129 general integer
/// columns) it pinned the optimum away and reported OPTIMAL 16030.99 for an instance whose optimum
/// is 16029.69 — a WRONG ANSWER, and the only one this crate has ever produced.
///
/// The bug was latent for as long as the incumbent was too weak to fix anything at all. Nothing but
/// an exhaustive check would have found it on purpose.
#[test]
fn general_integer_optima_match_brute_force() {
    use num_rational::BigRational;

    let mut seed = 0x5EED_1234_u64;
    let mut rnd = || {
        seed = seed.wrapping_mul(6_364_136_223_846_793_005).wrapping_add(1);
        (seed >> 33) as i64
    };

    const HI: i64 = 4; // each column ranges over [0, 4] -- span 4, so the span/unit bug shows
    for case in 0..150 {
        let mut m = Model::new();
        let n = 3 + (case % 2); // 3 or 4 integer columns
        let cols: Vec<_> = (0..n).map(|_| m.add_int_col(0.0, HI as f64)).collect();

        let mut rows: Vec<(Vec<f64>, f64)> = Vec::new();
        for _ in 0..3 {
            let a: Vec<f64> = (0..n).map(|_| (rnd() % 7 - 3) as f64).collect();
            if a.iter().all(|&v| v == 0.0) {
                continue;
            }
            let b = (rnd() % 20) as f64;
            let terms: Vec<_> = cols
                .iter()
                .zip(&a)
                .filter(|(_, &v)| v != 0.0)
                .map(|(&c, &v)| (c, v))
                .collect();
            m.add_row(f64::NEG_INFINITY, b, &terms);
            rows.push((a, b));
        }
        let obj: Vec<f64> = (0..n).map(|_| (rnd() % 9 - 4) as f64).collect();
        let terms: Vec<_> = cols
            .iter()
            .zip(&obj)
            .filter(|(_, &v)| v != 0.0)
            .map(|(&c, &v)| (c, v))
            .collect();
        m.set_objective(&terms, Sense::Minimize);

        // Every point of the box, by hand.
        let mut truth: Option<i64> = None;
        let total = (HI + 1).pow(n as u32);
        for code in 0..total {
            let mut x = vec![0i64; n];
            let mut t = code;
            for v in x.iter_mut() {
                *v = t % (HI + 1);
                t /= HI + 1;
            }
            let ok = rows
                .iter()
                .all(|(a, b)| a.iter().zip(&x).map(|(&c, &v)| c * v as f64).sum::<f64>() <= *b);
            if !ok {
                continue;
            }
            let val: i64 = obj.iter().zip(&x).map(|(&c, &v)| c as i64 * v).sum();
            truth = Some(truth.map_or(val, |t: i64| t.min(val)));
        }

        let mut s = BabSession::new(m.clone(), &SolveOpts::new()).expect("model");
        match (s.check().expect("solve"), truth) {
            (Outcome::Optimal { value, .. }, Some(t)) => {
                assert_eq!(
                    value,
                    BigRational::from_integer(t.into()),
                    "case {case}: ay says {value}, brute force says {t}"
                );
            }
            (Outcome::Infeasible { .. }, None) => {}
            (Outcome::Infeasible { .. }, Some(t)) => {
                panic!("case {case}: ay says INFEASIBLE, brute force found {t}")
            }
            (Outcome::Optimal { value, .. }, None) => {
                panic!("case {case}: ay says OPTIMAL {value}, brute force says infeasible")
            }
            (other, _) => panic!("case {case}: unexpected {other:?}"),
        }
    }
}
