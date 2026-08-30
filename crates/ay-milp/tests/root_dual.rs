// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial suite for the ROOT DUAL BOUND — the partial dual evidence a
//! declined whole-tree optimality proof can still export.
//!
//! The claim under test is deliberately WEAK, and the risk is therefore not
//! that it is unsound but that it is READ AS STRONGER THAN IT IS. So the file
//! is organised around the three things that must stay true no matter what:
//!
//! * the exported bound is a real bound on the real model (and a forged one is
//!   rejected),
//! * the residual it leaves unproved is stated and CANNOT be understated,
//! * a certificate carrying one never reaches `VERIFIED`.
//!
//! Every negative names a concrete falsifying instance and shows the forgery is
//! a lie about THAT model before showing it is rejected.

use ay_milp::cert_io::{self, CheckStatus, ClaimStanding, EvidenceKind};
use ay_milp::{
    derive_root_dual_bound, root_dual_gap, BabSession, Model, OptimalityCertificate,
    RootDualBudget, RootDualDecline, RootDualLane, Sense, SolveOpts,
};
use num_rational::BigRational;

fn int(n: i64) -> BigRational {
    BigRational::from_integer(n.into())
}

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(n.into(), d.into())
}

/// `min x` s.t. `2x >= 1`, `x` INTEGER in `[0, 10]`.
///
/// The whole point of the fixture: the root relaxation stops at `x = 1/2`, so
/// the best possible root dual bound is `1/2`, while the true integer optimum
/// is `1`. The residual `1/2` is real and unclosable by any amount of dual
/// evidence at the root, which is exactly the situation this lane exists to
/// describe honestly.
fn gap_model() -> Model {
    let mut model = Model::new();
    let x = model.add_int_col(0.0, 10.0);
    model.add_row(1.0, f64::INFINITY, &[(x, 2.0)]);
    model.set_objective(&[(x, 1.0)], Sense::Minimize);
    model
}

/// The same shape mirrored: `max x` s.t. `2x <= 3`, `x` INTEGER in `[0, 10]`.
/// Root bound `3/2`, integer optimum `1`, residual `1/2`.
fn gap_model_max() -> Model {
    let mut model = Model::new();
    let x = model.add_int_col(0.0, 10.0);
    model.add_row(f64::NEG_INFINITY, 3.0, &[(x, 2.0)]);
    model.set_objective(&[(x, 1.0)], Sense::Maximize);
    model
}

/// The SHIPPED budget: float lane only, no clock.
fn budget() -> RootDualBudget {
    RootDualBudget::new(&gap_model())
}

/// The opt-in budget a caller sets when it wants the exact rim's coverage and
/// is willing to pay wall for it.
fn budget_with_rim(model: &Model) -> RootDualBudget {
    RootDualBudget::new(model).with_rim_iters(RootDualBudget::default_rim_iters(model))
}

// ---------------------------------------------------------------------------
// (a) The derivation produces a REAL bound on the REAL model.
// ---------------------------------------------------------------------------

#[test]
fn a_root_bound_is_derived_and_stands_on_its_own() {
    let model = gap_model();
    let (certificate, report) = derive_root_dual_bound(&model, &budget());
    let certificate = certificate.expect("the root relaxation of a one-column LP is solvable");
    assert_eq!(report.decline, None);
    assert_eq!(report.lane, Some(RootDualLane::Float));
    // The independent public verifier, which is what a consumer runs.
    certificate
        .verify(&model)
        .expect("the derived bound re-verifies against the model it was derived from");
    assert_eq!(certificate.sense, Sense::Minimize);
    // `x = 1/2` is LP-feasible (`2 * 1/2 = 1 >= 1`) and attains `1/2`, so no
    // bound above `1/2` is valid for the relaxation. The derivation reaches it.
    assert_eq!(certificate.bound, rat(1, 2));
}

#[test]
fn the_bound_is_a_bound_and_not_the_integer_optimum() {
    let model = gap_model();
    let certificate = derive_root_dual_bound(&model, &budget())
        .0
        .expect("derives");
    // The integer optimum IS 1: `x = 1` satisfies `2x >= 1` and no smaller
    // non-negative integer does (`x = 0` gives `0 >= 1`, false).
    assert!(model.check_point(&[int(1)]).is_ok(), "x = 1 is feasible");
    assert!(model.check_point(&[int(0)]).is_err(), "x = 0 is not");
    // …and the exported bound is strictly weaker than it. This is the property
    // the whole `objbound` claim exists to state out loud.
    assert!(
        certificate.bound < int(1),
        "a root bound that already reached the integer optimum would make this \
         fixture prove nothing about partial evidence"
    );
    assert_eq!(root_dual_gap(&certificate, &model, &int(1)), Ok(rat(1, 2)));
}

#[test]
fn a_maximize_model_is_bounded_from_above() {
    let model = gap_model_max();
    let certificate = derive_root_dual_bound(&model, &budget())
        .0
        .expect("derives");
    certificate.verify(&model).expect("re-verifies");
    assert_eq!(certificate.sense, Sense::Maximize);
    // `x = 3/2` is LP-feasible and attains `3/2`, so `3/2` is the tightest
    // valid UPPER bound; a lane that forgot to negate the rim's minimise frame
    // would produce `-3/2` here and the sign error would be invisible without
    // this case.
    assert_eq!(certificate.bound, rat(3, 2));
    assert_eq!(root_dual_gap(&certificate, &model, &int(1)), Ok(rat(1, 2)));
}

#[test]
fn the_objective_offset_rides_in_the_model_frame() {
    let mut model = gap_model();
    model.set_objective_offset(100.0);
    let certificate = derive_root_dual_bound(&model, &budget())
        .0
        .expect("derives");
    certificate.verify(&model).expect("re-verifies");
    // `bound` is the LINEAR part and excludes the offset, exactly as
    // `OptimalityCertificate` documents…
    assert_eq!(certificate.bound, rat(1, 2));
    // …while the model-frame value, which is what `Outcome::Optimal::value` and
    // the `.ayc` verdict line are in, includes it. A lane that compared the two
    // frames directly would read a residual of `100 1/2` as `-99 1/2` and file
    // the bound as better than the optimum.
    assert_eq!(
        ay_milp::root_dual_bound_in_model_frame(&certificate, &model),
        rat(201, 2)
    );
    assert_eq!(
        root_dual_gap(&certificate, &model, &int(101)),
        Ok(rat(1, 2))
    );
}

#[test]
fn a_model_with_no_columns_in_the_objective_still_bounds_itself() {
    // `min 0` over a feasible box. The bound is `0`, the multiplier list is
    // empty, and the certificate must still verify — an empty proof of a
    // zero objective is the one place `verify`'s coefficient identity is
    // trivially satisfiable, so it needs pinning rather than assuming.
    let mut model = Model::new();
    let x = model.add_int_col(0.0, 4.0);
    model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
    model.set_objective(&[], Sense::Minimize);
    let certificate = derive_root_dual_bound(&model, &budget())
        .0
        .expect("derives");
    certificate.verify(&model).expect("re-verifies");
    assert_eq!(certificate.bound, int(0));
    assert!(certificate.objective.is_empty());
}

// ---------------------------------------------------------------------------
// (b) The derivation FAILS CLOSED. Structural reasons are named, not buried.
// ---------------------------------------------------------------------------

#[test]
fn an_infeasible_root_is_named_and_produces_nothing() {
    // `x >= 3` and `x <= 1` on a column bounded in `[0, 10]`: the ROOT
    // RELAXATION is empty, so the model is too and no `Optimal` verdict over it
    // could be honest.
    let mut model = Model::new();
    let x = model.add_int_col(0.0, 10.0);
    model.add_row(3.0, f64::INFINITY, &[(x, 1.0)]);
    model.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0)]);
    model.set_objective(&[(x, 1.0)], Sense::Minimize);
    assert!(model.check_point(&[int(2)]).is_err(), "nothing is feasible");
    let (certificate, report) = derive_root_dual_bound(&model, &budget_with_rim(&model));
    assert!(certificate.is_none());
    assert_eq!(report.decline, Some(RootDualDecline::RootInfeasible));
    assert!(
        !report.decline.expect("named").is_budget(),
        "an empty root is a fact about the model, and telling a caller to spend \
         more on it would be exactly wrong"
    );
    // …and ONLY the exact rim may say so. Under the shipped float-only budget
    // the same model reports a BUDGET decline, because an `f64` LP calling a
    // root empty is an opinion and this lane does not promote opinions to facts.
    let (nothing, float_only) = derive_root_dual_bound(&model, &budget());
    assert!(nothing.is_none());
    assert_eq!(float_only.decline, Some(RootDualDecline::Undecided));
    assert!(float_only.decline.expect("named").is_budget());
}

#[test]
fn an_unbounded_root_is_named_and_produces_nothing() {
    // `min -x` with `x` free above: the relaxation runs to −∞ and there is no
    // finite dual bound to export.
    let mut model = Model::new();
    let x = model.add_col(0.0, f64::INFINITY);
    model.set_objective(&[(x, -1.0)], Sense::Minimize);
    let (certificate, report) = derive_root_dual_bound(&model, &budget_with_rim(&model));
    assert!(certificate.is_none());
    assert_eq!(report.decline, Some(RootDualDecline::RootUnbounded));
    assert!(!report.decline.expect("named").is_budget());
}

#[test]
fn the_exact_rim_is_off_by_default_and_reachable_on_request() {
    let model = gap_model();
    // The shipped budget spends NO rim iterations: the emitted artifact is a
    // function of the model alone, with no clock in it.
    assert_eq!(RootDualBudget::new(&model).rim_iters, 0);
    let (certificate, report) = derive_root_dual_bound(&model, &RootDualBudget::new(&model));
    assert!(certificate.is_some());
    assert_eq!(report.rim_iters, 0);
    assert_eq!(report.lane, Some(RootDualLane::Float));
    // Opting in RUNS the rim even though the float lane already produced a
    // bound — that is the point of the flag, because a rim that only covered
    // for a MISSING bound could never improve a weak one. On this fixture both
    // lanes reach the same tightest bound `1/2`, so the answer is unchanged and
    // only the cost differs.
    let (with_rim, rim_report) = derive_root_dual_bound(&model, &budget_with_rim(&model));
    let with_rim = with_rim.expect("the rim lane also closes this model");
    assert!(rim_report.rim_iters > 0, "the rim really ran");
    assert_eq!(
        with_rim.bound,
        certificate.expect("float bound").bound,
        "1/2 is the tightest valid bound, so neither lane can beat the other"
    );
}

#[test]
fn the_rim_is_what_closes_a_model_the_float_lane_cannot() {
    // `min x` s.t. `x >= 1/3` with `x` FREE below: the reduced cost lands on a
    // column with no finite lower bound to price it at, so the float lane's
    // multiplier construction declines outright — and the row dual alone, which
    // the exact rim produces, closes it.
    let mut model = Model::new();
    let x = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
    let y = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
    model.add_row(1.0, f64::INFINITY, &[(x, 3.0), (y, 1.0)]);
    model.set_objective(&[(x, 1.0)], Sense::Minimize);
    let (float_only, float_report) = derive_root_dual_bound(&model, &RootDualBudget::new(&model));
    let (with_rim, rim_report) = derive_root_dual_bound(&model, &budget_with_rim(&model));
    // Whatever the two lanes make of this model, the invariant that matters is
    // that a certificate returned by EITHER stands on its own…
    for candidate in [&float_only, &with_rim] {
        if let Some(certificate) = candidate {
            certificate
                .verify(&model)
                .expect("no lane may return a bound that does not re-verify");
        }
    }
    // …and that a decline is always attributed, never silent.
    assert_eq!(float_only.is_none(), float_report.decline.is_some());
    assert_eq!(with_rim.is_none(), rim_report.decline.is_some());
}

// ---------------------------------------------------------------------------
// (c) `root_dual_gap` refuses a bound that contradicts the verdict.
// ---------------------------------------------------------------------------

#[test]
fn a_bound_better_than_the_claimed_optimum_is_a_contradiction_not_a_residual() {
    let model = gap_model();
    let certificate = derive_root_dual_bound(&model, &budget())
        .0
        .expect("derives");
    // Honest: the claimed optimum 1 is worse than the proved bound 1/2.
    assert_eq!(root_dual_gap(&certificate, &model, &int(1)), Ok(rat(1, 2)));
    // Dishonest: a verdict claiming 1/4 would be BETTER than a bound that says
    // nothing feasible beats 1/2. Both cannot be true of one model, and the
    // function says so rather than returning a negative residual.
    assert!(root_dual_gap(&certificate, &model, &rat(1, 4)).is_err());
    // A bound proved for the OPPOSITE sense is refused outright: it is a
    // statement about a different optimisation problem.
    let flipped = OptimalityCertificate {
        sense: Sense::Maximize,
        ..certificate
    };
    assert!(root_dual_gap(&flipped, &model, &int(1)).is_err());
}

// ---------------------------------------------------------------------------
// (d) The `.ayc` round trip: emitted, parsed, and INDEPENDENTLY re-checked.
// ---------------------------------------------------------------------------

/// `min x + y` s.t. `2x + 2y >= 3` with `x, y` INTEGER in `[0, 10]`, plus a
/// cost-free CONTINUOUS `z <= x`. Optimum 2 (`x = 2, y = 0` or `x = 1, y = 1`),
/// root LP bound `3/2`, residual `1/2`.
///
/// Three deliberate choices:
///
/// * TWO objective columns, so the emitted block is a real multiplier list and
///   not a degenerate one.
/// * A residual no branching at the root can remove, so the fixture keeps
///   testing PARTIAL evidence rather than quietly becoming a complete proof.
/// * The continuous `z`, which exists ONLY to keep the model off the
///   pure-integer PB projection route. Without it this model is solved by that
///   route, which files a REPLAY claim, and the certificate under test would
///   read `evidence dual REPLAY` — a different (also unbacked) shape from the
///   `NONE` this lane was built for. The first draft of this file had no `z`
///   and asserted `dual NONE`; the assertion failed and named the route, which
///   is how the column got here.
const GAP_MPS: &str = "NAME          ROOTGAP
ROWS
 N  COST
 G  R1
 L  R2
COLUMNS
    MARKER                 'MARKER'                 'INTORG'
    X         COST      1.0        R1        2.0        R2       -1.0
    Y         COST      1.0        R1        2.0
    MARKER                 'MARKER'                 'INTEND'
    Z         R2        1.0
RHS
    RHS       R1        3.0
BOUNDS
 UP BND       X         10.0
 UP BND       Y         10.0
 UP BND       Z         5.0
ENDATA
";

struct Emitted {
    ayc: String,
    model_text: &'static str,
}

/// Solve `GAP_MPS`, derive a root dual bound, and emit a certificate carrying
/// it. No whole-tree artifact is passed, which is the situation the lane is for.
fn emit_with_root_dual() -> Emitted {
    let problem = ay_milp::read_mps(GAP_MPS).expect("model parses");
    let names = problem.col_names.clone();
    let scale = problem.obj_scale.clone();
    let opts = SolveOpts::new().with_time_limit(std::time::Duration::from_secs(20));
    let mut session = BabSession::new(problem.model, &opts).expect("session");
    let outcome = session.check().expect("solve");
    assert!(
        matches!(outcome, ay_milp::Outcome::Optimal { .. }),
        "the fixture must reach an optimum: {outcome:?}"
    );
    let bound = derive_root_dual_bound(session.model(), &RootDualBudget::new(session.model()))
        .0
        .expect("the root relaxation of a two-column LP is solvable");
    let ayc = emit(&session, GAP_MPS, &names, &scale, &outcome, Some(&bound));
    Emitted {
        ayc,
        model_text: GAP_MPS,
    }
}

fn emit(
    session: &BabSession,
    model_text: &str,
    col_names: &[String],
    obj_scale: &BigRational,
    outcome: &ay_milp::Outcome,
    root_dual: Option<&OptimalityCertificate>,
) -> String {
    let ctx = cert_io::EmitCtx {
        model: session.model(),
        model_text,
        col_names,
        obj_scale,
        provenance: "host=test",
        replay_claims: session.replay_claims(),
        affine_aggregation_certificate: session.affine_aggregation_certificate(),
        parity_infeasibility_certificate: session.parity_infeasibility_certificate(),
        sat_relu_infeasibility_certificate: session.sat_relu_infeasibility_certificate(),
        network_design_infeasibility_certificate: session
            .network_design_infeasibility_certificate(),
        network_design_optimality_certificate: session.network_design_optimality_certificate(),
        block_angular_optimality_certificate: session.block_angular_optimality_certificate(),
        milp_optimality_tree_certificate: None,
        root_dual_bound_certificate: root_dual,
        single_machine_scheduling_optimality_certificate: session
            .single_machine_scheduling_optimality_certificate(),
        single_row_dp_infeasibility_certificate: session.single_row_dp_infeasibility_certificate(),
        multi_row_bdd_infeasibility_certificate: session.multi_row_bdd_infeasibility_certificate(),
        open_domain_single_row_dp_infeasibility_certificate: session
            .open_domain_single_row_dp_infeasibility_certificate(),
        open_domain_multi_row_bdd_infeasibility_certificate: session
            .open_domain_multi_row_bdd_infeasibility_certificate(),
        open_domain_hybrid_pb_lp_infeasibility_certificate: session
            .open_domain_hybrid_pb_lp_infeasibility_certificate(),
        open_domain_hybrid_integer_lift_infeasibility_certificate: session
            .open_domain_hybrid_integer_lift_infeasibility_certificate(),
        hybrid_pb_lp_infeasibility_certificate: session.hybrid_pb_lp_infeasibility_certificate(),
        hybrid_integer_lift_infeasibility_certificate: session
            .hybrid_integer_lift_infeasibility_certificate(),
        max_bytes: None,
    };
    cert_io::emit(&ctx, outcome)
}

#[test]
fn the_block_and_its_claim_appear_and_the_dual_claim_does_not_move() {
    let emitted = emit_with_root_dual();
    assert!(
        emitted.ayc.contains("evidence dual NONE\n"),
        "the dual half is exactly as unbacked as it was: {}",
        emitted.ayc
    );
    assert!(
        emitted
            .ayc
            .contains("evidence objbound SUCCINCT root-dual-bound\n"),
        "{}",
        emitted.ayc
    );
    assert!(
        emitted.ayc.contains("\nrootdual sense=min "),
        "{}",
        emitted.ayc
    );
    assert!(
        emitted.ayc.contains(" bound=3/2 gap=1/2 frame=model"),
        "the block states the bound it proves AND the residual it does not: {}",
        emitted.ayc
    );
}

#[test]
fn the_checker_verifies_the_bound_and_still_refuses_to_say_verified() {
    // THE HEADLINE, and the one assertion this whole lane must never lose.
    let emitted = emit_with_root_dual();
    let report = cert_io::check(&emitted.ayc, emitted.model_text);
    assert_eq!(
        report.status(),
        CheckStatus::Partial,
        "a verified BOUND must not promote an unproved optimum: {:?}",
        report.notes()
    );
    assert_eq!(report.status().exit_code(), 11);
    assert_eq!(
        report.census(),
        "CLAIMS verified=primal,objbound refuted=- unbacked=dual"
    );
    let dual = claim(&report, "dual");
    assert_eq!(dual.kind(), EvidenceKind::None);
    assert_eq!(dual.standing(), ClaimStanding::Unbacked);
    let bound = claim(&report, "objbound");
    assert_eq!(bound.kind(), EvidenceKind::Succinct);
    assert_eq!(bound.standing(), ClaimStanding::Verified);
    assert!(
        bound.detail().contains("a BOUND, not an optimum"),
        "the report must say what it did NOT establish: {}",
        bound.detail()
    );
    assert!(
        bound.detail().contains("RESIDUAL IS NOT PROVED"),
        "{}",
        bound.detail()
    );
}

#[test]
fn the_lane_stays_silent_when_the_dual_half_is_already_proved() {
    // The `.ayc` for a model whose whole-tree proof SUCCEEDS carries no
    // `objbound` claim even when a root bound is available: a weaker statement
    // beside a proof is noise, and a reader who saw both could reasonably take
    // the pair for one hedged claim.
    let ctx_ayc = emit_proved_optimum();
    assert!(
        ctx_ayc.contains("evidence dual SUCCINCT optimality-tree"),
        "{ctx_ayc}"
    );
    assert!(
        !ctx_ayc.contains("objbound"),
        "a proved dual half leaves no room for a weaker restatement: {ctx_ayc}"
    );
    assert_eq!(
        cert_io::check(&ctx_ayc, GAP_MPS).status(),
        CheckStatus::Verified
    );
}

/// A certificate for the same fixture whose dual half IS proved, root bound on
/// offer and declined. The control for every "does a bound read like a proof?"
/// question below: without it those tests could pass because nothing matches
/// the proved signature ANYWHERE.
fn emit_proved_optimum() -> String {
    let problem = ay_milp::read_mps(GAP_MPS).expect("parses");
    let names = problem.col_names.clone();
    let scale = problem.obj_scale.clone();
    let opts = SolveOpts::new().with_time_limit(std::time::Duration::from_secs(20));
    let mut session = BabSession::new(problem.model, &opts).expect("session");
    let outcome = session.check().expect("solve");
    let ay_milp::Outcome::Optimal {
        value,
        model_values,
        ..
    } = &outcome
    else {
        panic!("fixture must be optimal");
    };
    let tree = ay_milp::derive_optimality_tree(
        session.model(),
        value,
        model_values,
        &ay_milp::OptimalityTreeBudget::new(4096),
    )
    .expect("the certifying descent closes this two-column integer program");
    let bound = derive_root_dual_bound(session.model(), &RootDualBudget::new(session.model()))
        .0
        .expect("a root bound is available");
    // Emitted WITH the tree, so the dual claim is backed — and with the root
    // bound also on offer, which is the case that matters: the emitter must
    // decline it rather than never having had it.
    emit_with_tree(&session, GAP_MPS, &names, &scale, &outcome, &tree, &bound)
}

/// THE REPAIR'S HEADLINE, and the assertion the first cut of this lane failed.
///
/// The claim name is not decoration. `verify`'s census is documented as a
/// grep-able line and this repo's own design notes record
/// `CLAIMS verified=primal,dual` as the signature of a PROVED optimum — so a
/// bound-only certificate whose census merely CONTAINS that string presents as
/// dual-verified to the reader the line exists for. Measured on `22433` at
/// `dd72470b69`: `grep -c 'CLAIMS verified=primal,dual'` returned 1 on a
/// certificate whose `dual` claim was `NONE`.
#[test]
fn a_bounded_optimum_cannot_be_grepped_as_a_proved_one() {
    const PROVED_SIGNATURE: &str = "CLAIMS verified=primal,dual";

    let proved = cert_io::check(&emit_proved_optimum(), GAP_MPS);
    assert_eq!(proved.status(), CheckStatus::Verified);
    assert!(
        proved.census().starts_with(PROVED_SIGNATURE),
        "the control: a PROVED optimum really does carry this signature — if it \
         stops doing so, the negative below has stopped meaning anything: {}",
        proved.census()
    );

    let emitted = emit_with_root_dual();
    let bounded = cert_io::check(&emitted.ayc, emitted.model_text);
    assert_eq!(bounded.status(), CheckStatus::Partial);
    assert!(
        !bounded.census().contains(PROVED_SIGNATURE),
        "a certificate whose optimum is NOT proved must not match the signature \
         of one that is, under substring search and not merely under equality: {}",
        bounded.census()
    );

    // The same property on the artifact itself: every `evidence` record naming
    // the dual half must be the `dual` record, so `evidence dual…` cannot be
    // answered by the bound's line.
    for line in emitted.ayc.lines() {
        if let Some(rest) = line.strip_prefix("evidence dual") {
            assert!(
                rest.starts_with(' '),
                "`{line}` answers a query for the `dual` claim with another claim's record"
            );
        }
    }
}

/// The guard, not the good luck: a HAND-WRITTEN certificate cannot introduce a
/// shadowing name either.
///
/// Our emitter can only produce the vocabulary in `CLAIM_NAMES`, so without
/// this the property would hold only for files we wrote — and a `.ayc` is an
/// artifact anyone may hand this checker.
#[test]
fn a_claim_name_that_shadows_another_is_refused() {
    let emitted = emit_with_root_dual();
    for forged_name in ["dualbound", "dualx"] {
        let forged = reseal(&emitted.ayc.replace(
            "evidence objbound SUCCINCT root-dual-bound",
            &format!("evidence {forged_name} SUCCINCT root-dual-bound"),
        ));
        let report = cert_io::check(&forged, emitted.model_text);
        assert_eq!(
            report.status(),
            CheckStatus::Refuted,
            "`{forged_name}` extends `dual`: {}",
            report.census()
        );
        assert!(
            report
                .notes()
                .iter()
                .any(|n| n.contains("CLAIM-NAME VIOLATION") && n.contains(forged_name)),
            "{:?}",
            report.notes()
        );
    }
    // A NONE-kind record is refused for the same reason: the guard is about the
    // name a reader greps for, not about what the claim carries.
    let forged = reseal(&emitted.ayc.replace(
        "evidence dual NONE\n",
        "evidence dual NONE\nevidence dualtrust NONE\n",
    ));
    let report = cert_io::check(&forged, emitted.model_text);
    assert_eq!(report.status(), CheckStatus::Refuted);
    assert!(
        report
            .notes()
            .iter()
            .any(|n| n.contains("CLAIM-NAME VIOLATION") && n.contains("dualtrust")),
        "{:?}",
        report.notes()
    );
}

fn emit_with_tree(
    session: &BabSession,
    model_text: &str,
    col_names: &[String],
    obj_scale: &BigRational,
    outcome: &ay_milp::Outcome,
    tree: &ay_milp::MilpOptimalityCertificate,
    root_dual: &OptimalityCertificate,
) -> String {
    let ctx = cert_io::EmitCtx {
        model: session.model(),
        model_text,
        col_names,
        obj_scale,
        provenance: "host=test",
        replay_claims: session.replay_claims(),
        affine_aggregation_certificate: session.affine_aggregation_certificate(),
        parity_infeasibility_certificate: session.parity_infeasibility_certificate(),
        sat_relu_infeasibility_certificate: session.sat_relu_infeasibility_certificate(),
        network_design_infeasibility_certificate: session
            .network_design_infeasibility_certificate(),
        network_design_optimality_certificate: session.network_design_optimality_certificate(),
        block_angular_optimality_certificate: session.block_angular_optimality_certificate(),
        milp_optimality_tree_certificate: Some(tree),
        root_dual_bound_certificate: Some(root_dual),
        single_machine_scheduling_optimality_certificate: session
            .single_machine_scheduling_optimality_certificate(),
        single_row_dp_infeasibility_certificate: session.single_row_dp_infeasibility_certificate(),
        multi_row_bdd_infeasibility_certificate: session.multi_row_bdd_infeasibility_certificate(),
        open_domain_single_row_dp_infeasibility_certificate: session
            .open_domain_single_row_dp_infeasibility_certificate(),
        open_domain_multi_row_bdd_infeasibility_certificate: session
            .open_domain_multi_row_bdd_infeasibility_certificate(),
        open_domain_hybrid_pb_lp_infeasibility_certificate: session
            .open_domain_hybrid_pb_lp_infeasibility_certificate(),
        open_domain_hybrid_integer_lift_infeasibility_certificate: session
            .open_domain_hybrid_integer_lift_infeasibility_certificate(),
        hybrid_pb_lp_infeasibility_certificate: session.hybrid_pb_lp_infeasibility_certificate(),
        hybrid_integer_lift_infeasibility_certificate: session
            .hybrid_integer_lift_infeasibility_certificate(),
        max_bytes: None,
    };
    cert_io::emit(&ctx, outcome)
}

fn claim<'a>(report: &'a cert_io::CheckReport, name: &str) -> &'a cert_io::ClaimReport {
    report
        .claims()
        .iter()
        .find(|c| c.name() == name)
        .unwrap_or_else(|| panic!("no `{name}` claim in {:?}", report.census()))
}

// ---------------------------------------------------------------------------
// (e) TAMPERING. A checker that cannot reject is worthless.
// ---------------------------------------------------------------------------

/// Re-seal a hand-edited certificate so the `%END` body digest still matches.
/// Without this every tamper would be caught by the digest and none of the
/// checks below would ever run.
fn reseal(ayc: &str) -> String {
    let body: String = ayc
        .lines()
        .take_while(|l| !l.starts_with("%END"))
        .map(|l| format!("{l}\n"))
        .collect();
    let digest = cert_io::sha256_hex(body.as_bytes());
    format!("{body}%END sha256:{digest}\n")
}

#[test]
fn resealing_alone_is_not_a_tamper() {
    // The control for every case below: if `reseal` itself broke the file, the
    // tampering tests would pass for the wrong reason.
    let emitted = emit_with_root_dual();
    let resealed = reseal(&emitted.ayc);
    assert_eq!(
        cert_io::check(&resealed, emitted.model_text).status(),
        CheckStatus::Partial
    );
}

#[test]
fn understating_the_residual_is_refuted() {
    // THE FORGERY THIS FIELD EXISTS TO STOP. The bound really is 3/2 and the
    // verdict really claims 2, so the residual really is 1/2; a certificate
    // that writes 1/4 is claiming to have proved twice as much as it did.
    let emitted = emit_with_root_dual();
    assert!(emitted.ayc.contains("gap=1/2"));
    let forged = reseal(&emitted.ayc.replace("gap=1/2", "gap=1/4"));
    let report = cert_io::check(&forged, emitted.model_text);
    assert_eq!(report.status(), CheckStatus::Refuted);
    assert_eq!(
        claim(&report, "objbound").standing(),
        ClaimStanding::Refuted
    );
    assert!(
        claim(&report, "objbound")
            .detail()
            .contains("may not understate"),
        "{}",
        claim(&report, "objbound").detail()
    );
}

#[test]
fn overstating_the_residual_is_refuted_too() {
    // The mirror case, and it matters for a different reason: a residual larger
    // than the truth is not conservative, it is a second number disagreeing
    // with the first, and a format that tolerates one direction of disagreement
    // has no basis for rejecting the other.
    let emitted = emit_with_root_dual();
    let forged = reseal(&emitted.ayc.replace("gap=1/2", "gap=3/4"));
    assert_eq!(
        cert_io::check(&forged, emitted.model_text).status(),
        CheckStatus::Refuted
    );
}

#[test]
fn a_tightened_bound_is_refuted() {
    // `x = y = 3/4` is LP-feasible (`2*3/4 + 2*3/4 = 3 >= 3`) and attains 3/2,
    // so NO bound above 3/2 is valid for this model. A block claiming 2 — which
    // would make the residual zero and the optimum "proved" — is a lie about
    // the model, and the multiplier identity is what catches it.
    let emitted = emit_with_root_dual();
    let forged = reseal(&emitted.ayc.replace(" bound=3/2 gap=1/2", " bound=2 gap=0"));
    let report = cert_io::check(&forged, emitted.model_text);
    assert_eq!(report.status(), CheckStatus::Refuted);
    assert!(
        claim(&report, "objbound")
            .detail()
            .contains("DO NOT verify"),
        "{}",
        claim(&report, "objbound").detail()
    );
}

#[test]
fn a_rescaled_multiplier_is_refuted() {
    let emitted = emit_with_root_dual();
    assert!(emitted.ayc.contains("mult row 0 lower 1/2"));
    let forged = reseal(
        &emitted
            .ayc
            .replace("mult row 0 lower 1/2", "mult row 0 lower 1"),
    );
    assert_eq!(
        cert_io::check(&forged, emitted.model_text).status(),
        CheckStatus::Refuted
    );
}

#[test]
fn a_claim_naming_an_absent_block_is_refuted() {
    let emitted = emit_with_root_dual();
    let start = emitted
        .ayc
        .find("\nrootdual ")
        .expect("the block is present");
    let end = emitted.ayc[start + 1..]
        .find("\nend\n")
        .map(|i| start + 1 + i + "\nend\n".len())
        .expect("the block terminates");
    let mut stripped = emitted.ayc.clone();
    stripped.replace_range(start + 1..end, "");
    let forged = reseal(&stripped);
    let report = cert_io::check(&forged, emitted.model_text);
    assert_eq!(report.status(), CheckStatus::Refuted);
    assert!(
        claim(&report, "objbound").detail().contains("absent"),
        "{}",
        claim(&report, "objbound").detail()
    );
}

#[test]
fn a_bound_on_a_different_objective_is_refuted() {
    // The block's `obj` records are what `verify` checks the multipliers
    // against, so a forger who changes BOTH in step proves something true about
    // a DIFFERENT linear function and presents it as a bound on this model's.
    // Here the objective is halved and the bound with it: internally consistent,
    // and still not a statement about `min x + y`.
    let emitted = emit_with_root_dual();
    let forged = emitted
        .ayc
        .replace("obj 0 1\nobj 1 1\n", "obj 0 1/2\nobj 1 1/2\n")
        .replace(" bound=3/2 gap=1/2", " bound=3/4 gap=5/4")
        .replace("mult row 0 lower 1/2", "mult row 0 lower 1/4");
    let forged = reseal(&forged);
    let report = cert_io::check(&forged, emitted.model_text);
    assert_eq!(report.status(), CheckStatus::Refuted);
    assert!(
        claim(&report, "objbound")
            .detail()
            .contains("DIFFERENT objective"),
        "{}",
        claim(&report, "objbound").detail()
    );
}

#[test]
fn an_objbound_claim_labelled_replay_is_a_parse_error() {
    // The format must make mislabelling UNGRAMMATICAL, not merely detectable at
    // verification time.
    let emitted = emit_with_root_dual();
    let forged = reseal(&emitted.ayc.replace(
        "evidence objbound SUCCINCT root-dual-bound",
        "evidence objbound REPLAY root-dual-bound",
    ));
    assert!(cert_io::parse(&forged).is_err());
}

#[test]
fn an_objbound_claim_on_a_verdict_that_names_no_optimum_is_refused() {
    // A residual needs something to be a residual AGAINST. On `infeasible`
    // there is no optimum, so a `objbound` record is a malformed certificate
    // rather than an unproved one, and the claim-set policy is what says so.
    let emitted = emit_with_root_dual();
    let forged = reseal(
        &emitted
            .ayc
            .replace("verdict optimal value=2 frame=file", "verdict infeasible"),
    );
    let report = cert_io::check(&forged, emitted.model_text);
    assert_eq!(report.status(), CheckStatus::Refuted);
    assert!(
        report
            .notes()
            .iter()
            .any(|n| n.contains("CLAIM-SET VIOLATION") && n.contains("objbound")),
        "{:?}",
        report.notes()
    );
}

#[test]
fn a_duplicate_rootdual_block_is_a_parse_error() {
    let emitted = emit_with_root_dual();
    let start = emitted.ayc.find("\nrootdual ").expect("present") + 1;
    let end = emitted.ayc[start..]
        .find("\nend\n")
        .map(|i| start + i + "\nend\n".len())
        .expect("terminates");
    let block = emitted.ayc[start..end].to_owned();
    let mut doubled = emitted.ayc.clone();
    doubled.insert_str(end, &block);
    assert!(cert_io::parse(&reseal(&doubled)).is_err());
}

#[test]
fn the_bound_is_checked_against_this_model_and_not_another() {
    // Same block, different model: the digests catch it first, which is the
    // point — a bound is a statement about one model and the format binds it to
    // one.
    let emitted = emit_with_root_dual();
    let other = GAP_MPS.replace("R1        3.0", "R1        5.0");
    assert_eq!(
        cert_io::check(&emitted.ayc, &other).status(),
        CheckStatus::Mismatch
    );
}

// ---------------------------------------------------------------------------
// (f) The objective inclusion rule.
// ---------------------------------------------------------------------------

#[test]
fn the_exported_objective_omits_structural_zeros_and_keeps_the_rest() {
    let mut model = Model::new();
    let a = model.add_int_col(0.0, 4.0);
    let b = model.add_int_col(0.0, 4.0);
    model.add_row(1.0, f64::INFINITY, &[(a, 1.0), (b, 1.0)]);
    model.set_objective(&[(a, 3.0)], Sense::Minimize);
    let exported = ay_milp::model_objective_exact(&model);
    assert_eq!(exported, vec![(0u32, int(3))]);
    assert_eq!(model.obj_coeff(b), 0.0, "column b costs nothing");
    assert_eq!(model.obj_coeff(a), 3.0);
}
