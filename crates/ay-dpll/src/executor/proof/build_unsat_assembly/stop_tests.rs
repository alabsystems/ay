// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A stop reaches UNSAT proof assembly and its empty-clause ladder, fails
//! closed, and changes nothing when it has not fired.

use std::sync::atomic::AtomicBool;
use std::sync::Arc;

use ay_core::{time::Instant, AletheRule, Proof, ProofStep, Sort};

use crate::executor::{Executor, ProofDeclineMechanism};

/// `p` and `(not p)`: the smallest refutation every ladder rung can close.
fn contradiction() -> Executor {
    let mut exec = Executor::new();
    let script = "(set-logic QF_UF)(declare-const p Bool)(assert p)(assert (not p))";
    for command in &ay_frontend::parse(script).expect("parse the contradiction") {
        let output = exec.execute(command).expect("execute the contradiction");
        assert!(output.is_none(), "the fixture holds no query command");
    }
    exec
}

/// The two stop signals, each already fired.
fn fired_stops() -> [(Option<Arc<AtomicBool>>, Option<Instant>); 2] {
    [
        (Some(Arc::new(AtomicBool::new(true))), None),
        (None, Some(Instant::now())),
    ]
}

fn is_poison(proof: &Proof) -> bool {
    matches!(
        proof.steps.as_slice(),
        [ProofStep::Step {
            rule: AletheRule::Trust,
            clause,
            premises,
            ..
        }] if clause.is_empty() && premises.is_empty()
    )
}

fn derives_empty_clause(proof: &Proof) -> bool {
    proof.steps.iter().any(|step| {
        matches!(
            step,
            ProofStep::Resolution { clause, .. } | ProofStep::Step { clause, .. }
                if clause.is_empty()
        )
    })
}

#[test]
fn a_fired_stop_discards_the_assembly_and_no_stop_assembles_as_before() {
    let mut unstopped = contradiction();
    unstopped.build_unsat_proof();
    let proof = unstopped
        .last_proof
        .as_ref()
        .expect("an unstopped assembly installs its proof");
    assert!(derives_empty_clause(proof), "the refutation is derived");
    assert!(!is_poison(proof), "an unstopped assembly is never poisoned");
    assert_ne!(
        unstopped.last_proof_decline,
        Some(ProofDeclineMechanism::ProofAssemblyStopped)
    );

    // A live deadline that has not fired is no stop: the same proof.
    let mut far = contradiction();
    far.set_solve_controls(
        Some(Arc::new(AtomicBool::new(false))),
        Instant::now().checked_add(std::time::Duration::from_secs(3_600)),
    );
    far.build_unsat_proof();
    assert_eq!(
        format!("{:?}", far.last_proof.as_ref().map(|p| &p.steps)),
        format!("{:?}", Some(&proof.steps)),
        "an idle stop changes nothing"
    );

    for (interrupt, deadline) in fired_stops() {
        let mut exec = contradiction();
        exec.set_solve_controls(interrupt, deadline);
        exec.last_lrat_certificate = Some(vec![7]);
        exec.build_unsat_proof();
        let proof = exec
            .last_proof
            .as_ref()
            .expect("a stopped assembly leaves the fail-closed poison");
        assert!(
            is_poison(proof),
            "a stopped assembly must not finish or install its partial proof: {proof:?}"
        );
        assert_eq!(
            exec.last_proof_decline,
            Some(ProofDeclineMechanism::ProofAssemblyStopped)
        );
        assert!(
            exec.last_lrat_certificate.is_none(),
            "no LRAT export survives beside the poison"
        );
    }
}

/// #certification-envelope-isolation, the assembly half (the twin of
/// `unsat_cert`'s `an_expired_search_slice_does_not_starve_the_corroborating_resolve`).
/// A search lane narrows only the search wall, assembles the refutation it
/// found inside that slice, and restores the wall before publication
/// (`arrays_to_lia.rs`, the DT lazy lane): an expired slice under a live
/// certification envelope must assemble exactly as with no deadline at all.
/// The quantified backstop moves the wall the other way and is unwound before
/// publication: an expired envelope under a live wall stops the assembly.
#[test]
fn assembly_stops_on_the_certification_envelope_not_on_a_search_slice() {
    let mut unstopped = contradiction();
    unstopped.build_unsat_proof();
    let expected = format!("{:?}", unstopped.last_proof.as_ref().map(|p| &p.steps));
    let far = Instant::now().checked_add(std::time::Duration::from_secs(3_600));

    let mut sliced = contradiction();
    sliced.set_deadline(far);
    sliced.set_search_deadline(Some(Instant::now()));
    assert!(
        sliced.make_should_stop()(),
        "fixture: the search slice has expired"
    );
    sliced.build_unsat_proof();
    sliced.set_search_deadline(far);
    assert_ne!(
        sliced.last_proof_decline,
        Some(ProofDeclineMechanism::ProofAssemblyStopped),
        "an expired search slice is not the command's stop"
    );
    assert_eq!(
        format!("{:?}", sliced.last_proof.as_ref().map(|p| &p.steps)),
        expected,
        "the refutation the lane found assembles as with no deadline"
    );

    let mut expired = contradiction();
    expired.set_deadline(far);
    expired.certification_deadline.set(Some(Instant::now()));
    assert!(
        !expired.make_should_stop()(),
        "fixture: the search wall is live"
    );
    expired.build_unsat_proof();
    assert!(expired.last_proof.as_ref().is_some_and(is_poison));
    assert_eq!(
        expired.last_proof_decline,
        Some(ProofDeclineMechanism::ProofAssemblyStopped)
    );
}

#[test]
fn a_fired_stop_leaves_the_empty_clause_ladder_before_any_rung() {
    let leaves = |exec: &mut Executor| {
        let p = exec.ctx.terms.mk_var("ladder_stop_p", Sort::Bool);
        let not_p = exec.ctx.terms.mk_not(p);
        let mut proof = Proof::new();
        proof.add_assume(p, None);
        proof.add_assume(not_p, None);
        proof
    };

    let mut unstopped = Executor::new();
    let mut proof = leaves(&mut unstopped);
    unstopped.ensure_empty_clause_derivation(&mut proof);
    assert!(
        derives_empty_clause(&proof),
        "an unstopped ladder closes p, (not p)"
    );

    for (interrupt, deadline) in fired_stops() {
        let mut exec = Executor::new();
        let mut proof = leaves(&mut exec);
        exec.set_solve_controls(interrupt, deadline);
        exec.ensure_empty_clause_derivation(&mut proof);
        assert_eq!(
            proof.steps.len(),
            2,
            "no rung ran after the stop: {proof:?}"
        );
        assert!(!derives_empty_clause(&proof));
        assert!(
            exec.last_trust_closure_census.is_none(),
            "the last-resort trust closure is never reached after a stop"
        );
    }
}
