// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! T-c, the proof-export path: a stop ends the deferred-trust rescue as
//! [`StrictProofVerdict::Stopped`], never as `Rejected` (P4a.1).

use super::*;

/// `a = store(b, i, v)` and `(select a i) != v` over 8-bit indices and
/// values, with the refutation forged as a `trust` step for
/// `(= (select a i) v)` resolved against its authored negation: every step
/// but the trust step is strictly valid, so the rescue collects exactly that
/// clause, which is entailed but no array tautology.
fn read_over_write_refutation() -> (crate::Executor, ay_core::Proof) {
    let commands = ay_frontend::parse(
        "(set-logic QF_ABV)
         (declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
         (declare-const b (Array (_ BitVec 8) (_ BitVec 8)))
         (declare-const i (_ BitVec 8))
         (declare-const v (_ BitVec 8))
         (assert (= a (store b i v)))
         (assert (not (= (select a i) v)))",
    )
    .expect("fixture parses");
    let mut exec = crate::Executor::new();
    exec.execute_all(&commands).expect("fixture elaborates");
    let negated_fact = *exec.ctx.assertions.last().expect("the fixture has roots");
    let fact = match exec.ctx.terms.get(negated_fact) {
        ay_core::term::TermData::Not(inner) => *inner,
        other => panic!("the fixture's last root must be a negation, got {other:?}"),
    };
    let proof = ay_core::Proof::from_steps(vec![
        ProofStep::Step {
            rule: AletheRule::Trust,
            clause: vec![fact],
            premises: Vec::new(),
            args: Vec::new(),
        },
        ProofStep::Assume(negated_fact),
        ProofStep::Resolution {
            clause: Vec::new(),
            pivot: fact,
            clause1: ay_core::ProofId(0),
            clause2: ay_core::ProofId(1),
        },
    ]);
    (exec, proof)
}

fn export_verdict(
    exec: &crate::Executor,
    proof: &ay_core::Proof,
    controls: &TrustClauseDischargeControls,
) -> StrictProofVerdict {
    let terms = &exec.ctx.terms;
    let plain = ay_proof::check_proof_strict(proof, terms);
    assert!(
        matches!(plain, Err(ProofCheckError::TrustStep { .. })),
        "the fixture fails plain strict checking only at its trust step: {plain:?}"
    );
    let quality = check_proof_with_quality(proof, terms).expect("diagnostic quality");
    let verdict = strict_verdict_with_deferred_trust(
        plain,
        &quality,
        proof,
        terms,
        &exec.ctx.assertions,
        &exec.ctx,
        controls,
    );
    stopped_verdict(verdict, controls)
}

fn controls_for(exec: &crate::Executor) -> TrustClauseDischargeControls {
    TrustClauseDischargeControls::new(None, None, None, None, CertificationEffort::for_query(exec))
}

/// A process-memory stop that one poll of the rescue saw, and that has lapsed
/// by the time it returns, is the exported verdict, and the consumer boundary
/// refuses it as a stop, not as a rejection. Negative control: with nothing
/// stopping it the same proof verifies.
#[test]
fn a_stop_one_lane_saw_is_the_exported_verdict_never_a_rejection() {
    let (exec, proof) = read_over_write_refutation();
    assert!(
        matches!(
            export_verdict(&exec, &proof, &controls_for(&exec)),
            StrictProofVerdict::Verified(_)
        ),
        "with nothing stopping it the rescue verifies the refutation"
    );

    arm_one_poll_memory_stop_for_testing();
    let verdict = export_verdict(&exec, &proof, &controls_for(&exec));
    assert!(!ay_sys::process_memory_exceeded(), "the stop has lapsed");
    assert_eq!(
        verdict,
        StrictProofVerdict::Stopped(StrictVerdictStop::MemoryLimit { term_store: false })
    );
}

/// The stop names map as the export documents them, and a spent count is not
/// a stop.
#[test]
fn envelope_stops_name_their_export_stop() {
    assert_eq!(
        StrictVerdictStop::of_envelope(EnvelopeStop::Interrupt),
        StrictVerdictStop::Interrupted
    );
    assert_eq!(
        StrictVerdictStop::of_envelope(EnvelopeStop::LaneShare),
        StrictVerdictStop::MemoryLimit { term_store: false }
    );
    assert_eq!(
        StrictVerdictStop::of_envelope(EnvelopeStop::TermMemory),
        StrictVerdictStop::MemoryLimit { term_store: true }
    );
    let spent = TrustClauseDischargeControls::new(
        None,
        None,
        None,
        None,
        CertificationEffort::with_allowance(0, None),
    );
    let rejected = StrictProofVerdict::Rejected("pool spent".to_string());
    assert_eq!(stopped_verdict(rejected.clone(), &spent), rejected);
}

/// The export's own strict walk, cancelled by a stop, reached no verdict: it
/// is exported as the stop the walk recorded, never as `Rejected`.
#[test]
fn a_cancelled_export_walk_is_a_stopped_verdict() {
    let mut solver = super::super::Solver::new(super::super::Logic::QfUf);
    solver.set_produce_proofs(true);
    let p = solver.declare_const("cancelled_export_walk_p", super::super::Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);
    assert!(solver.check_sat().is_unsat());
    let verified = solver
        .export_last_unsat_artifact()
        .expect("the refutation exports");
    assert!(matches!(
        verified.strict_verdict,
        StrictProofVerdict::Verified(_)
    ));

    ay_sys::force_process_memory_exceeded_for_testing(true);
    let stopped = solver.export_last_unsat_artifact();
    ay_sys::force_process_memory_exceeded_for_testing(false);
    let stopped = stopped.expect("a stopped walk still exports its artifact");
    assert_eq!(
        stopped.strict_verdict,
        StrictProofVerdict::Stopped(StrictVerdictStop::MemoryLimit { term_store: false })
    );
    assert_eq!(
        stopped.accept_for_consumer(ProofAcceptanceMode::Strict),
        Err(ProofAcceptanceError::StrictStopped {
            stop: StrictVerdictStop::MemoryLimit { term_store: false }
        })
    );
    assert!(!stopped.restricted_rule_subset);
}
