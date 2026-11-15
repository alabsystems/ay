// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! W2/R22 content-bearing cyclic-array acceptance targets, authored UNRUN.
//!
//! These are AY-authored semantic fixtures, NOT captured typed MODEL_CHECKER_CONSUMER requests
//! or consumer qualification. Unlike the unread-array R22 fixtures, a store's
//! value crosses a predicate edge before the body assertion, and crosses four
//! iterations before the exit assertion. Merely folding a clause-local
//! `select(store(a, 1, 9), 1)` cannot discharge the original query.
//!
//! One caller-owned 20-second deadline covers parsing, solving, original-model
//! verification, checked replay and cleanup. Public APIs accept durations, not
//! the private absolute-deadline scopes: each gets only the remaining time, with
//! one shared cancellation timer and mandatory post-phase/post-cleanup checks.
//! Relative-to-absolute conversion, timer scheduling and opaque work can drift;
//! this is neither a drift-free internal deadline nor a hard return-time bound.
//! Run serially under an external process/resource guard. No consumer quarantine
//! is removed by these tests.

use ay_chc::{
    engines, validate_chc_ground_derivation_artifact_with_progress, CancellationGuard,
    CancellationToken, ChcExpr, ChcGroundDerivationArtifactErrorReason, ChcParser, ChcPdrProofRun,
    ChcProblem, ChcSort, ClauseHead, Counterexample, PdrConfig, VerifiedChcResult,
};
use ay_core::time::Instant;
use std::{cell::Cell, time::Duration};

const WHOLE_CASE_BUDGET: Duration = Duration::from_secs(20);

struct Budget {
    phase: Cell<&'static str>,
    deadline: Instant,
    cancellation: CancellationToken,
    timer: CancellationGuard,
}

impl Budget {
    fn new() -> Self {
        let deadline = Instant::now() + WHOLE_CASE_BUDGET;
        let cancellation = CancellationToken::new();
        let timer = cancellation.cancel_after(deadline.saturating_duration_since(Instant::now()));
        Self {
            phase: Cell::new("parsing original source"),
            deadline,
            cancellation,
            timer,
        }
    }

    fn check(&self) {
        if Instant::now() >= self.deadline {
            self.cancellation.cancel();
        }
        assert!(
            !self.cancellation.is_cancelled(),
            "whole-case 20s budget exhausted during {}",
            self.phase.get()
        );
    }

    fn remaining(&self) -> Duration {
        self.check();
        let remaining = self.deadline.saturating_duration_since(Instant::now());
        assert!(!remaining.is_zero(), "no remaining phase allowance");
        remaining
    }

    fn config(&self) -> PdrConfig {
        // Both public verification entry points retain the original clauses;
        // private configuration fields are not a downstream API.
        let mut config = PdrConfig::production(false).with_strict_proofs(true);
        config.cancellation_token = Some(self.cancellation.clone());
        config.solve_timeout = Some(self.remaining());
        config
    }

    fn finish(self) {
        let Self {
            phase,
            deadline,
            cancellation,
            timer,
        } = self;
        // CancellationGuard wakes and joins its timer, including on unwinding.
        // Include successful timer teardown in the final admission check too.
        drop(timer);
        assert!(
            Instant::now() < deadline,
            "cleanup exceeded the original deadline during {}",
            phase.get()
        );
        assert!(
            !cancellation.is_cancelled(),
            "cancellation observed during cleanup during {}",
            phase.get()
        );
    }
}

#[derive(Clone, Copy, Debug)]
enum Observation {
    Body,
    Exit,
}

#[derive(Clone, Copy, Debug)]
enum Expected {
    SafeNine,
    UnsafeTen,
}

fn source(observation: Observation, expected: Expected) -> String {
    let (predicate, guard) = match observation {
        Observation::Body => ("B", "true"),
        Observation::Exit => ("H", "(bvuge i #x0000000000000004)"),
    };
    let value = match expected {
        Expected::SafeNine => "#x00000009",
        Expected::UnsafeTen => "#x0000000a",
    };
    // H is entered at i=0; only i<4 advances through B to H(i+1).
    // Thus the first exit is i=4, with exactly four writes and no overflow.
    // Lane 1 is in the intended [0,4) source array; no junk lane is observed.
    format!(
        r#"(set-logic HORN)
(declare-fun H ((Array (_ BitVec 64) (_ BitVec 32)) (_ BitVec 64)) Bool)
(declare-fun B ((Array (_ BitVec 64) (_ BitVec 32)) (_ BitVec 64)) Bool)
(assert (H ((as const (Array (_ BitVec 64) (_ BitVec 32))) #x00000005)
           #x0000000000000000))
(assert (forall ((a (Array (_ BitVec 64) (_ BitVec 32))) (i (_ BitVec 64)))
  (=> (and (H a i) (bvult i #x0000000000000004))
      (B (store a #x0000000000000001 #x00000009) i))))
(assert (forall ((a (Array (_ BitVec 64) (_ BitVec 32))) (i (_ BitVec 64)))
  (=> (B a i) (H a (bvadd i #x0000000000000001)))))
(assert (forall ((a (Array (_ BitVec 64) (_ BitVec 32))) (i (_ BitVec 64)))
  (=> (and ({predicate} a i) {guard}
           (not (= (select a #x0000000000000001) {value}))) false)))
(check-sat)
"#
    )
}

fn assert_shape(problem: &ChcProblem, observation: Observation) {
    assert_eq!(problem.predicates().len(), 2);
    assert_eq!(problem.clauses().len(), 4);
    let sorts = vec![
        ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(32))),
        ChcSort::BitVec(64),
    ];
    for name in ["H", "B"] {
        let id = problem.lookup_predicate(name).expect("original relation");
        assert_eq!(problem.predicates()[id.index()].arg_sorts, sorts);
    }
    let ClauseHead::Predicate(head, arguments) = &problem.clauses()[0].head else {
        panic!("constant-array initializer must remain a fact");
    };
    assert_eq!(Some(*head), problem.lookup_predicate("H"));
    assert!(
        matches!(&arguments[0], ChcExpr::ConstArray(ChcSort::BitVec(64), value)
        if value.as_ref() == &ChcExpr::BitVec(5, 32))
    );
    assert_eq!(arguments[1], ChcExpr::BitVec(0, 64));
    let query = problem.clauses().last().unwrap();
    assert!(matches!(query.head, ClauseHead::False));
    assert_eq!(query.body.predicates.len(), 1);
    let observed = match observation {
        Observation::Body => "B",
        Observation::Exit => "H",
    };
    assert_eq!(
        Some(query.body.predicates[0].0),
        problem.lookup_predicate(observed)
    );
    // The query reads its carried array, not a locally constructed store term.
    let rendered = query.body.constraint.as_ref().unwrap().to_string();
    assert!(rendered.contains("select"));
    assert!(!rendered.contains("store"));
}

fn assert_same_problem(original: &ChcProblem, actual: &ChcProblem) {
    assert_eq!(actual.normalized_input(), original.normalized_input());
    assert_eq!(
        actual.normalized_input_sha256(),
        original.normalized_input_sha256()
    );
    assert_eq!(actual.predicates().len(), original.predicates().len());
    for (a, b) in actual.predicates().iter().zip(original.predicates()) {
        assert_eq!((a.id, &a.name, &a.arg_sorts), (b.id, &b.name, &b.arg_sorts));
    }
    assert_eq!(actual.clauses().len(), original.clauses().len());
    for (a, b) in actual.clauses().iter().zip(original.clauses()) {
        assert_eq!(a.body.predicates, b.body.predicates);
        assert_eq!(a.body.constraint, b.body.constraint);
        assert_eq!(a.action_id, b.action_id);
        match (&a.head, &b.head) {
            (ClauseHead::False, ClauseHead::False) => {}
            (ClauseHead::Predicate(a, aa), ClauseHead::Predicate(b, ba)) => {
                assert_eq!((a, aa), (b, ba));
            }
            _ => panic!("original clause head changed"),
        }
    }
}

fn require_safe(run: &ChcPdrProofRun, original: &ChcProblem, budget: &Budget) {
    let VerifiedChcResult::Safe(invariant) = run.result() else {
        panic!("Safe required, not {}", run.result());
    };
    let model = invariant.model();
    assert_eq!(model.len(), original.predicates().len());
    for predicate in original.predicates() {
        let interpretation = model.get(&predicate.id).expect("full original model");
        let sorts: Vec<_> = interpretation.vars.iter().map(|v| v.sort.clone()).collect();
        assert_eq!(
            sorts, predicate.arg_sorts,
            "original signature {}",
            predicate.name
        );
    }
    budget.phase.set("original invariant obligations");
    let obligations = model
        .replay_obligations(original)
        .expect("original clause obligations");
    assert_eq!(obligations.len(), original.clauses().len());
    for (index, obligation) in obligations.iter().enumerate() {
        assert_eq!(obligation.clause_index, index);
    }
    drop(obligations);
    budget.check();
    budget.phase.set("original invariant verification");
    assert!(
        engines::validate_external_invariant_model(original, model, &budget.config())
            .expect("full original-model verification")
    );
    budget.check();
    budget.phase.set("strict checked Safe replay");
    let checked = run
        .run_checked_replay_with_cancellation(budget.remaining(), &budget.cancellation)
        .expect("Safe needs checked replay, not metadata-only evidence");
    budget.check();
    assert!(checked.manifest().trust_full_verifier_admissible());
    assert!(checked
        .proof_run()
        .metadata()
        .trust_full_verifier_admissible());
    assert_eq!(checked.proof_run().metadata().replay_status(), "replayable");
    assert_eq!(
        checked.proof_run().metadata().transcript_status(),
        "replayable"
    );
    assert!(checked.proof_run().accepted_as_proof());
    assert!(matches!(
        checked.proof_run().result(),
        VerifiedChcResult::Safe(_)
    ));
    assert_same_problem(original, checked.proof_run().problem());
    assert_eq!(
        checked.problem_bytes(),
        original.normalized_input().as_bytes()
    );
    assert!(!checked.certificate_bytes().is_empty());
    assert!(!checked.checked_report_bytes().is_empty());
    drop(checked);
    budget.check();
}

fn require_unsafe(
    run: &ChcPdrProofRun,
    original: &ChcProblem,
    observation: Observation,
    input: &str,
    budget: &Budget,
) {
    let VerifiedChcResult::Unsafe(verified) = run.result() else {
        panic!("validated Unsafe required, not {}", run.result());
    };
    let witness = verified.counterexample();
    assert!(
        witness.has_ground_derivation()
            || witness
                .witness
                .as_ref()
                .is_some_and(|w| !w.entries.is_empty()),
        "strict original confirmation must return witness-bearing evidence"
    );
    budget.check();
    budget.phase.set("original Unsafe ground check");
    assert!(
        matches!(witness.ground_checks_unsafe(original), Ok(true)),
        "returned witness must independently ground-confirm on original clauses"
    );
    budget.check();

    check_unsafe_source_neighbors(run, witness, original, observation, input, budget);
}

#[derive(Clone, Copy)]
enum ChangedSource {
    SafeQuery,
    SafeStoreTen,
    UnsafeStoreEight,
}

fn source_bound_ground_bytes(
    run: &ChcPdrProofRun,
    original: &ChcProblem,
    budget: &Budget,
) -> Vec<u8> {
    let mut live = || !budget.cancellation.is_cancelled() && Instant::now() < budget.deadline;
    budget.phase.set("original ground artifact export");
    let bytes = run
        .unsafe_ground_derivation_artifact_bytes_with_progress(&mut live)
        .expect("original durable ground evidence must export without error")
        .expect("Unsafe acceptance needs actual ground bytes, not merely candidate topology");
    budget.check();
    budget.phase.set("original ground artifact replay");
    let checked =
        validate_chc_ground_derivation_artifact_with_progress(original, &bytes, &mut live)
            .expect("original sealed ground bytes must independently validate");
    assert_eq!(
        checked.normalized_input_sha256(),
        original.normalized_input_sha256()
    );
    drop(checked);
    budget.check();
    bytes
}

fn check_unsafe_source_neighbors(
    run: &ChcPdrProofRun,
    witness: &Counterexample,
    original: &ChcProblem,
    observation: Observation,
    input: &str,
    budget: &Budget,
) {
    // These ORIGINAL bytes stay fixed across every changed-source check.
    // Re-exporting under a changed problem would test a NEW artifact instead.
    let artifact = source_bound_ground_bytes(run, original, budget);
    let safe_input = source(observation, Expected::SafeNine);
    assert_eq!(input.matches("#x0000000a").count(), 1);
    assert_eq!(safe_input, input.replacen("#x0000000a", "#x00000009", 1));
    let store = "(store a #x0000000000000001 #x00000009)";
    assert_eq!(input.matches(store).count(), 1);
    let neighbors = [
        (ChangedSource::SafeQuery, safe_input),
        (
            ChangedSource::SafeStoreTen,
            input.replacen(store, "(store a #x0000000000000001 #x0000000a)", 1),
        ),
        (
            ChangedSource::UnsafeStoreEight,
            input.replacen(store, "(store a #x0000000000000001 #x00000008)", 1),
        ),
    ];
    for (kind, changed_input) in neighbors {
        check_changed_unsafe_source(
            kind,
            &changed_input,
            witness,
            original,
            observation,
            &artifact,
            budget,
        );
        drop(changed_input);
        budget.check();
    }
    drop(artifact);
    budget.check();
}

fn check_changed_unsafe_source(
    kind: ChangedSource,
    changed_input: &str,
    witness: &Counterexample,
    original: &ChcProblem,
    observation: Observation,
    artifact: &[u8],
    budget: &Budget,
) {
    budget.check();
    budget.phase.set("changed-source parsing");
    let changed = ChcParser::parse(changed_input).expect("changed original fixture");
    assert_shape(&changed, observation);
    assert_ne!(
        changed.normalized_input_sha256(),
        original.normalized_input_sha256()
    );
    assert_eq!(changed.predicates().len(), original.predicates().len());
    for (a, b) in changed.predicates().iter().zip(original.predicates()) {
        assert_eq!((a.id, &a.name, &a.arg_sorts), (b.id, &b.name, &b.arg_sorts));
    }
    assert_eq!(changed.clauses().len(), original.clauses().len());
    budget.check();
    budget.phase.set("changed-source candidate ground check");
    let raw_candidate = witness.ground_checks_unsafe(&changed);
    budget.check();
    match kind {
        ChangedSource::SafeQuery | ChangedSource::SafeStoreTen => assert!(
            !matches!(raw_candidate, Ok(true)),
            "a safe changed source cannot admit any derived Unsafe candidate"
        ),
        ChangedSource::UnsafeStoreEight => {
            // Store8 still violates asserted10. Ok(true) is permitted ONLY
            // because this API fully grounds against CURRENT clauses.
            // It is not evidence that old array9 values or source bytes
            // were authenticated for changed8. False/refusal is not Safe.
            if let Ok(true) = raw_candidate {
                assert!(changed_input.contains("(store a #x0000000000000001 #x00000008)"));
                assert!(changed_input.contains("#x0000000a"));
            }
        }
    }
    let mut live = || !budget.cancellation.is_cancelled() && Instant::now() < budget.deadline;
    budget.phase.set("changed-source sealed artifact rejection");
    let error =
        validate_chc_ground_derivation_artifact_with_progress(&changed, artifact, &mut live)
            .expect_err("original sealed source-bound bytes cannot rebind to changed source");
    assert_eq!(
        error.reason,
        ChcGroundDerivationArtifactErrorReason::ProblemHashMismatch
    );
    budget.check();
    drop(changed);
    budget.check();
}

fn run(observation: Observation, expected: Expected) {
    let budget = Budget::new();
    let input = source(observation, expected);
    let original = ChcParser::parse(&input).expect("authored original CHC must parse");
    assert_shape(&original, observation);
    budget.check();
    eprintln!("W2 array contents {observation:?}/{expected:?}: strict original solve");
    budget.phase.set("strict original solve");
    let run = engines::solve_pdr_proof(original.clone(), budget.config())
        .expect("strict original solve must not error");
    budget.check();
    assert_same_problem(&original, run.problem());
    assert!(
        run.accepted_as_proof(),
        "Unknown is not acceptance: {}",
        run.result()
    );
    match expected {
        Expected::SafeNine => require_safe(&run, &original, &budget),
        Expected::UnsafeTen => require_unsafe(&run, &original, observation, &input, &budget),
    }
    budget.check();
    budget.phase.set("original run and source cleanup");
    drop(run);
    drop(original);
    drop(input);
    budget.check();
    budget.finish();
}

#[test]
fn carried_store_body_requires_safe_original_model_and_checked_replay() {
    run(Observation::Body, Expected::SafeNine);
}

#[test]
fn carried_store_body_wrong_value_requires_original_unsafe_witness() {
    run(Observation::Body, Expected::UnsafeTen);
}

#[test]
fn carried_store_after_four_iterations_requires_safe_original_model_and_checked_replay() {
    run(Observation::Exit, Expected::SafeNine);
}

#[test]
fn carried_store_after_four_iterations_wrong_value_requires_original_unsafe_witness() {
    run(Observation::Exit, Expected::UnsafeTen);
}
