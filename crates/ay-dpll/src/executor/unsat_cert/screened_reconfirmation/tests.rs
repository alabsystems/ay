// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pins for the deferred-trust re-decisions' posture, and for the
//! trace-backed step-(3) record the default posture keeps.

use ay_core::{AletheRule, Proof, ProofId, ProofStep, TermId};

use super::super::{
    ProbeUnsatAuthority, UnsatCertificationError, WHOLE_PROBLEM_RECONFIRMATION_LIMITS,
};
use super::ReconfirmationReading;
use crate::executor::Executor;
use crate::executor_types::SolveResult;

/// The CLI's synthesized-default reconstruction budget.
const BEST_EFFORT_BUDGET: u64 = 1_000_000;

/// A SAT solver as the executor's lanes arm one: a clause trace, then the
/// executor's search-time bookkeeping budget. Whether it keeps the proof-mode
/// inprocessing controls past that budget.
fn lane_solver_keeps_proof_inprocessing(exec: &Executor) -> bool {
    let mut sat = ay_sat::Solver::new(2);
    sat.enable_clause_trace();
    sat.set_proof_bookkeeping_budget(exec.search_proof_bookkeeping_budget());
    sat.keeps_proof_inprocessing_after_exhaustion()
}

/// A re-decision whose class nobody reads is metered as the outer query's
/// search was (`Executor::new()` drops the budget), its SAT solvers keep the
/// proof-mode inprocessing controls past the meter while the posture's scope
/// is open, and it runs no trust-elimination members.
#[test]
fn a_redecision_whose_class_nobody_reads_runs_metered_and_clamped() {
    let mut outer = Executor::new();
    outer.set_best_effort_produce_proofs(BEST_EFFORT_BUDGET);
    let mut nested = outer.new_derived_query_executor();
    assert_eq!(nested.proof_reconstruction_step_budget, None);
    assert!(!nested.skips_trust_elimination_repairs());
    assert!(!lane_solver_keeps_proof_inprocessing(&outer));
    let scope = outer.arm_reconfirmation_posture(&mut nested, ReconfirmationReading::EitherClass);
    assert!(scope.is_some());
    assert!(lane_solver_keeps_proof_inprocessing(&nested));
    drop(scope);
    assert!(!lane_solver_keeps_proof_inprocessing(&nested));
    assert_eq!(
        nested.proof_reconstruction_step_budget,
        Some(BEST_EFFORT_BUDGET)
    );
    assert_eq!(
        nested.search_proof_bookkeeping_budget(),
        outer.search_proof_bookkeeping_budget()
    );
    assert!(nested.search_proof_bookkeeping_budget().is_some());
    assert!(nested.skips_trust_elimination_repairs());
    assert!(!outer.skips_trust_elimination_repairs());
}

/// NEGATIVE TWIN: the closed-sentence certificates read the class, so their
/// re-decision keeps the unchanged executor, and so does a re-decision under
/// an explicit proof demand, whose outer query has no budget to pass on.
#[test]
fn a_sealed_class_or_an_explicit_demand_keeps_the_unbudgeted_executor() {
    let mut outer = Executor::new();
    outer.set_best_effort_produce_proofs(BEST_EFFORT_BUDGET);
    let mut sealed = outer.new_derived_query_executor();
    let scope = outer.arm_reconfirmation_posture(&mut sealed, ReconfirmationReading::SealedClass);
    assert!(scope.is_none());
    assert_eq!(sealed.proof_reconstruction_step_budget, None);
    assert!(!sealed.skips_trust_elimination_repairs());

    let mut explicit = Executor::new();
    explicit.set_produce_proofs(true);
    let mut nested = explicit.new_derived_query_executor();
    let _scope =
        explicit.arm_reconfirmation_posture(&mut nested, ReconfirmationReading::EitherClass);
    assert_eq!(nested.proof_reconstruction_step_budget, None);
    assert_eq!(nested.search_proof_bookkeeping_budget(), None);
}

/// An executor that has elaborated `script` and opened its public solve, as
/// the funnel finds it after a first solve.
fn elaborated(script: &str) -> Executor {
    let commands = ay_frontend::parse(script).expect("fixture parses");
    let mut exec = Executor::new();
    exec.execute_all(&commands).expect("fixture elaborates");
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    exec
}

/// The first solve's proof, forged as the closer the default posture leaves on
/// a refutation it could not reconstruct (`assume-family-trust-closure`): an
/// `assume` per root, a `trust` step for the clause of their negations, and
/// the resolutions to the empty clause. Every root must be a positive atom.
fn forge_bare_trust_closer(exec: &mut Executor) {
    let roots = exec.ctx.assertions.clone();
    let closer: Vec<TermId> = roots
        .iter()
        .map(|&root| exec.ctx.terms.mk_not(root))
        .collect();
    let mut steps: Vec<ProofStep> = roots.iter().map(|&root| ProofStep::Assume(root)).collect();
    let mut resolvent = closer.clone();
    let mut last = ProofId(u32::try_from(steps.len()).expect("few roots"));
    steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: closer.clone(),
        premises: Vec::new(),
        args: Vec::new(),
    });
    for (index, &root) in roots.iter().enumerate() {
        resolvent = resolvent[1..].to_vec();
        steps.push(ProofStep::Resolution {
            clause: resolvent.clone(),
            pivot: root,
            clause1: ProofId(u32::try_from(index).expect("few roots")),
            clause2: last,
        });
        last = ProofId(u32::try_from(steps.len() - 1).expect("few steps"));
    }
    exec.last_proof = Some(Proof::from_steps(steps));
    exec.last_checked_sat_refutation = None;
}

/// `x < y` and `y < x` over 8-bit `x`, `y`.
const CONTRADICTORY_ORDER: &str = "(set-logic QF_BV)
     (declare-const x (_ BitVec 8))
     (declare-const y (_ BitVec 8))
     (assert (bvult x y))
     (assert (bvult y x))";

/// `a = store(b, i, v)` and `select(a, i) < v` over 8-bit indices and values,
/// refuted by read-over-write.
const READ_BELOW_WRITTEN: &str = "(set-logic QF_ABV)
     (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
     (declare-const b (Array (_ BitVec 8) (_ BitVec 8)))
     (declare-const i (_ BitVec 8))
     (declare-const v (_ BitVec 8))
     (assert (= a (store b i v)))
     (assert (bvult (select a i) v))";

/// The record of the corroboration, by its stable tag.
fn corroboration_tag(exec: &Executor) -> Option<&'static str> {
    exec.last_unsat_corroboration().map(|record| record.tag())
}

/// The posture is the re-decisions' alone: step (3) still discharges a bare
/// trust closer over the whole scope with a strictly checked nested proof
/// (its BV lane re-decides the two 8-bit roots), and the record keeps the
/// stronger `standalone-tautology` evidence instead of a reproduction.
#[test]
fn a_bare_trust_closer_keeps_its_checked_step_3_discharge() {
    let mut exec = elaborated(CONTRADICTORY_ORDER);
    exec.set_best_effort_produce_proofs(BEST_EFFORT_BUDGET);
    forge_bare_trust_closer(&mut exec);
    let proof = exec.last_proof.clone().expect("the forged proof");
    let plain_error = exec
        .check_proof_strict_with_datatypes(&proof)
        .expect_err("the closer is a trust step");
    let controls = exec.certification_discharge_controls();
    assert!(exec
        .discharge_trust_steps_for_certification(&plain_error, &[], &controls)
        .is_ok());
    assert_eq!(corroboration_tag(&exec), Some("standalone-tautology"));
}

/// Pigeonhole 8 into 7 over an uninterpreted sort, with pigeons 2..7 each
/// barred from one hole so the symmetry strengthening stays off.
const BARRED_PIGEONHOLE: &str = "(set-logic QF_UF)
     (declare-sort U 0)
     (declare-const a0 U) (declare-const a1 U) (declare-const a2 U) (declare-const a3 U)
     (declare-const a4 U) (declare-const a5 U) (declare-const a6 U) (declare-const a7 U)
     (declare-const h0 U) (declare-const h1 U) (declare-const h2 U) (declare-const h3 U)
     (declare-const h4 U) (declare-const h5 U) (declare-const h6 U)
     (assert (or (= a0 h0) (= a0 h1) (= a0 h2) (= a0 h3) (= a0 h4) (= a0 h5) (= a0 h6)))
     (assert (or (= a1 h0) (= a1 h1) (= a1 h2) (= a1 h3) (= a1 h4) (= a1 h5) (= a1 h6)))
     (assert (or (= a2 h0) (= a2 h1) (= a2 h3) (= a2 h4) (= a2 h5) (= a2 h6)))
     (assert (or (= a3 h0) (= a3 h1) (= a3 h2) (= a3 h4) (= a3 h5) (= a3 h6)))
     (assert (or (= a4 h0) (= a4 h1) (= a4 h2) (= a4 h3) (= a4 h5) (= a4 h6)))
     (assert (or (= a5 h0) (= a5 h1) (= a5 h2) (= a5 h3) (= a5 h4) (= a5 h6)))
     (assert (or (= a6 h0) (= a6 h1) (= a6 h2) (= a6 h3) (= a6 h4) (= a6 h5)))
     (assert (or (= a7 h1) (= a7 h2) (= a7 h3) (= a7 h4) (= a7 h5) (= a7 h6)))
     (assert (distinct a0 a1 a2 a3 a4 a5 a6 a7))";

/// Step (3)'s lanes keep their unmetered clause trace in the default
/// posture. Here the outer search exhausts its bookkeeping meter, the closer
/// is a bare trust step, and step (3)'s native array lane re-decides it with
/// a checked SAT refutation built from the lane's own whole clause trace. The
/// record is therefore the stronger `standalone-tautology`, not step (4a)'s
/// reproduction.
///
/// Running step (3)'s pool lanes under the query's reconstruction budget
/// (the rejected first r30-step3-lanes patch) turns this record into
/// `entailment`: the lane's trace is exhausted and its refutation declines.
/// The cost that patch went after is the trace-mode search's re-walk of its
/// pinned root-trail slots (`ay_sat`'s `#pinned-retry-no-proof`).
#[test]
fn a_trace_backed_step_3_discharge_is_kept_in_the_default_posture() {
    let script = format!("{BARRED_PIGEONHOLE}\n(check-sat)\n");
    let commands = ay_frontend::parse(&script).expect("fixture parses");
    let mut exec = Executor::new();
    exec.set_best_effort_produce_proofs(BEST_EFFORT_BUDGET);
    let outputs = exec.execute_all(&commands).expect("fixture runs");
    assert_eq!(outputs, ["unsat"]);
    assert_eq!(corroboration_tag(&exec), Some("standalone-tautology"));
}

/// The closer publishes through the funnel on a scope outside the
/// Boolean/bit-vector fragment, whose native certificate lanes would answer
/// before the funnel does, in the default posture.
#[test]
fn a_bare_trust_closer_publishes_through_the_funnel() {
    let mut exec = elaborated(READ_BELOW_WRITTEN);
    exec.set_best_effort_produce_proofs(BEST_EFFORT_BUDGET);
    forge_bare_trust_closer(&mut exec);
    let published = exec.certify_unsat_for_publication(SolveResult::unsat(), &[]);
    assert!(published.is_unsat(), "a refuted scope must publish");
    let corroboration = corroboration_tag(&exec);
    assert!(corroboration.is_some(), "{corroboration:?}");
    assert!(exec.take_unsat_certificate().is_some());
}

/// NEGATIVE TWIN through the funnel: the same closer over a SATISFIABLE
/// scope, with the forged-UNSAT guard kept silent by an unbounded universal,
/// so step (4) is what must refuse it. Its fresh executor runs in the new
/// posture and still cannot answer `unsat`.
#[test]
fn a_forged_closer_over_a_satisfiable_scope_is_refused_at_step_4() {
    let fixture = || {
        let mut exec = elaborated(
            "(set-logic AUFLIA)
             (declare-const a (Array Int Int))
             (declare-const b (Array Int Int))
             (declare-const i Int)
             (declare-const j Int)
             (declare-const v Int)
             (declare-fun h (Int) Int)
             (assert (forall ((x Int)) (> (h (+ x 1)) (h x))))
             (assert (= a (store b i v)))
             (assert (< (select a j) v))",
        );
        exec.set_best_effort_produce_proofs(BEST_EFFORT_BUDGET);
        forge_bare_trust_closer(&mut exec);
        exec
    };
    match fixture().mint_unsat_certificate(&[]) {
        Err(UnsatCertificationError::StrictProofRejected { reason }) => assert!(
            reason.contains("deferred-trust discharge failed"),
            "the guard must stay silent and step (2) must pass, so step (4) decides: {reason}"
        ),
        Err(other) => panic!("unexpected certification error: {other:?}"),
        Ok(_) => panic!("a forged closer minted a certificate"),
    }
    let mut exec = fixture();
    let published = exec.certify_unsat_for_publication(SolveResult::unsat(), &[]);
    assert!(published.is_unknown(), "a forged closer must not publish");
    assert!(exec.take_unsat_certificate().is_none());
    assert_eq!(exec.last_unsat_corroboration(), None);
}

/// The re-decision of a refuted 8-bit scope answers in both readings: the
/// trust-accepting posture loses no re-decision the unchanged executor makes.
#[test]
fn both_readings_reconfirm_a_refuted_scope() {
    let mut exec = elaborated(CONTRADICTORY_ORDER);
    exec.set_best_effort_produce_proofs(BEST_EFFORT_BUDGET);
    let scope = exec.ctx.assertions.clone();
    let either = exec.reconfirm_unsat_within(
        &scope,
        None,
        WHOLE_PROBLEM_RECONFIRMATION_LIMITS,
        &exec.certification_discharge_controls(),
        false,
        ReconfirmationReading::EitherClass,
    );
    let sealed = exec.reconfirm_unsat_within(
        &scope,
        None,
        WHOLE_PROBLEM_RECONFIRMATION_LIMITS,
        &exec.certification_discharge_controls(),
        false,
        ReconfirmationReading::SealedClass,
    );
    assert!(either.is_some(), "{either:?}");
    assert!(sealed.is_some(), "{sealed:?}");
}

/// model-checker-consumer's export of `div_u32_ten` (u32 `x < 10^6`, then `x / 10 < 10^5`).
const DIV_U32_TEN: &str = r#"(set-logic QF_AUFBV)
(declare-const memory (Array (_ BitVec 64) (_ BitVec 8)))
(declare-const ay_any_0 (_ BitVec 32))
(declare-const |div_u32_ten::local_3_0| Bool)
(assert (= |div_u32_ten::local_3_0| (bvult ay_any_0 #x000f4240)))
(declare-const ay_assume_ctx_1 Bool)
(assert (= ay_assume_ctx_1 |div_u32_ten::local_3_0|))
(declare-const |div_u32_ten::local_5_0| Bool)
(assert (= |div_u32_ten::local_5_0| (= #x0000000a #x00000000)))
(declare-const ay_violation_div_by_zero_check_0 Bool)
(assert (= ay_violation_div_by_zero_check_0 (and ay_assume_ctx_1 (not (not |div_u32_ten::local_5_0|)))))
(declare-const ay_reach_div_by_zero_check_0 Bool)
(assert (= ay_reach_div_by_zero_check_0 ay_assume_ctx_1))
(declare-const ay_violation_div_by_zero_check_1 Bool)
(assert (= ay_violation_div_by_zero_check_1 (and ay_assume_ctx_1 (and (not |div_u32_ten::local_5_0|) (= #x0000000a #x00000000)))))
(declare-const ay_reach_div_by_zero_check_1 Bool)
(assert (= ay_reach_div_by_zero_check_1 (and ay_assume_ctx_1 (not |div_u32_ten::local_5_0|))))
(declare-const |div_u32_ten::local_4_0| (_ BitVec 32))
(declare-const |div_u32_ten::local_4__ssa_init_b5e7ddd5bb85e9ce| (_ BitVec 32))
(assert (= |div_u32_ten::local_4_0| (ite (not |div_u32_ten::local_5_0|) (bvudiv ay_any_0 #x0000000a) |div_u32_ten::local_4__ssa_init_b5e7ddd5bb85e9ce|)))
(declare-const |div_u32_ten::local_9_0| Bool)
(declare-const |div_u32_ten::local_9__ssa_init_bd60acb658c79e45| Bool)
(assert (= |div_u32_ten::local_9_0| (ite (not |div_u32_ten::local_5_0|) (bvult |div_u32_ten::local_4_0| #x000186a0) |div_u32_ten::local_9__ssa_init_bd60acb658c79e45|)))
(declare-const |div_u32_ten::local_8_0| Bool)
(declare-const |div_u32_ten::local_8__ssa_init_bd60acb658c79e45| Bool)
(assert (= |div_u32_ten::local_8_0| (ite (not |div_u32_ten::local_5_0|) (not |div_u32_ten::local_9_0|) |div_u32_ten::local_8__ssa_init_bd60acb658c79e45|)))
(declare-const |div_u32_ten::local_7_0| Bool)
(declare-const |div_u32_ten::local_7__ssa_init_bd60acb658c79e45| Bool)
(assert (= |div_u32_ten::local_7_0| (ite (not |div_u32_ten::local_5_0|) (not |div_u32_ten::local_8_0|) |div_u32_ten::local_7__ssa_init_bd60acb658c79e45|)))
(declare-const ay_violation_kani_assert_2 Bool)
(assert (= ay_violation_kani_assert_2 (and ay_assume_ctx_1 (and (not |div_u32_ten::local_5_0|) (not |div_u32_ten::local_7_0|)))))
(declare-const ay_reach_kani_assert_2 Bool)
(assert (= ay_reach_kani_assert_2 (and ay_assume_ctx_1 (not |div_u32_ten::local_5_0|))))
(declare-const ay_assume_ctx_2 Bool)
(assert (= ay_assume_ctx_2 (and ay_assume_ctx_1 (=> (not |div_u32_ten::local_5_0|) |div_u32_ten::local_7_0|))))
(declare-const ay_assume_final Bool)
(assert (= ay_assume_final ay_assume_ctx_2))
(assert (or (or ay_violation_div_by_zero_check_0 ay_violation_div_by_zero_check_1) ay_violation_kani_assert_2))"#;

/// The trust-accepting posture skips the trust-elimination members. On this
/// scope the unchanged executor's members replace the re-decision's trust
/// leaf with a checked derivation (`Checked`); the posture leaves the leaf
/// (`DischargedTrust`), which the deferred-trust funnel accepts alike, and the
/// sealed reading keeps the class. Measured in the test profile: 0.14 s
/// against 0.58 s here, and 0.12 s against 15.4 s on `rem_u32_digits`.
#[test]
fn the_trust_accepting_posture_skips_the_trust_elimination_members() {
    let mut exec = elaborated(DIV_U32_TEN);
    exec.set_best_effort_produce_proofs(BEST_EFFORT_BUDGET);
    let scope = exec.ctx.assertions.clone();
    let reconfirm = |reading| {
        exec.reconfirm_unsat_within(
            &scope,
            None,
            WHOLE_PROBLEM_RECONFIRMATION_LIMITS,
            &exec.certification_discharge_controls(),
            false,
            reading,
        )
    };
    assert_eq!(
        reconfirm(ReconfirmationReading::EitherClass),
        Some(ProbeUnsatAuthority::DischargedTrust)
    );
    assert_eq!(
        reconfirm(ReconfirmationReading::SealedClass),
        Some(ProbeUnsatAuthority::Checked)
    );
}
