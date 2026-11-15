// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Additional REQUIRED-success controls, not passing measurement harnesses.
//! Original eight acceptance/neighbor controls remain completely unchanged.

use super::*;
use crate::{
    engines, CancellationGuard, CancellationToken, ChcParser, ChcPdrProofRun, ChcProblem,
    PdrConfig, VerifiedChcResult,
};
use ay_core::time::Instant;
use std::time::Duration;

const R22_SCALAR: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/group_bv/model_checker_consumer_cyclic_arrays/loop_repro_array_false.smt2"
));
const R22_ARRAY: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/group_bv/model_checker_consumer_cyclic_arrays/loop_repro_array_true.smt2"
));
const W2_BODY: &str = include_str!("fixtures/carried_store_body.smt2");
const W2_EXIT: &str = include_str!("fixtures/carried_store_exit.smt2");

enum Wall {
    R22Phases,
    W2Whole {
        deadline: Instant,
        cancellation: CancellationToken,
        timer: CancellationGuard,
    },
}
impl Wall {
    fn whole() -> Self {
        let deadline = Instant::now() + Duration::from_secs(20);
        let cancellation = CancellationToken::new();
        let timer = cancellation.cancel_after(deadline.saturating_duration_since(Instant::now()));
        Self::W2Whole {
            deadline,
            cancellation,
            timer,
        }
    }
    fn check(&self) {
        if let Self::W2Whole {
            deadline,
            cancellation,
            ..
        } = self
        {
            if Instant::now() >= *deadline {
                cancellation.cancel();
            }
            assert!(
                !cancellation.is_cancelled(),
                "original whole-case 20s wall exhausted"
            );
        }
    }
    fn remaining(&self) -> Duration {
        match self {
            Self::R22Phases => Duration::from_secs(30),
            Self::W2Whole { deadline, .. } => {
                self.check();
                let remaining = deadline.saturating_duration_since(Instant::now());
                assert!(
                    !remaining.is_zero(),
                    "original whole-case allowance exhausted"
                );
                remaining
            }
        }
    }
    fn config(&self) -> PdrConfig {
        let mut config = PdrConfig::production(false);
        config.solve_timeout = Some(self.remaining());
        if let Self::W2Whole { cancellation, .. } = self {
            config = config.with_strict_proofs(true);
            config.cancellation_token = Some(cancellation.clone());
        }
        config
    }
    fn finish(self) {
        if let Self::W2Whole {
            deadline,
            cancellation,
            timer,
        } = self
        {
            drop(timer);
            assert!(
                Instant::now() < deadline,
                "cleanup exceeded original 20s wall"
            );
            assert!(
                !cancellation.is_cancelled(),
                "original cancellation observed during cleanup"
            );
        }
    }
}

/// What the census can attribute in a case's native UNSAT row proofs.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NativeSources {
    /// BV theory-lemma or `evaluate` steps the source census records.
    Required,
    /// R22's model (`head = true`, `body(i) = i <u 4`, `error = false`)
    /// leaves Boolean rows only: `(not true)`, `(and l (not l))`. The fold
    /// rescue refutes those with `and_pos`, `true` and resolution, so they
    /// carry no theory step to attribute. Every row is still inventoried.
    BooleanOnly,
}

fn same_source(original: &ChcProblem, actual: &ChcProblem) {
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
        assert_eq!(
            (&a.body.predicates, &a.body.constraint, a.action_id),
            (&b.body.predicates, &b.body.constraint, b.action_id)
        );
        match (&a.head, &b.head) {
            (crate::ClauseHead::False, crate::ClauseHead::False) => {}
            (crate::ClauseHead::Predicate(x, xa), crate::ClauseHead::Predicate(y, ya)) => {
                assert_eq!((x, xa), (y, ya));
            }
            _ => panic!("original head changed"),
        }
    }
}

fn original_model(run: &ChcPdrProofRun, original: &ChcProblem, wall: &Wall) {
    let VerifiedChcResult::Safe(invariant) = run.result() else {
        panic!("original Safe result required, not {}", run.result());
    };
    let model = invariant.model();
    assert_eq!(model.len(), original.predicates().len());
    for predicate in original.predicates() {
        let interpretation = model.get(&predicate.id).expect("full original model");
        let sorts: Vec<_> = interpretation
            .vars
            .iter()
            .map(|var| var.sort.clone())
            .collect();
        assert_eq!(sorts, predicate.arg_sorts);
    }
    let obligations = model
        .replay_obligations(original)
        .expect("all original obligations");
    assert_eq!(obligations.len(), original.clauses().len());
    for (index, obligation) in obligations.iter().enumerate() {
        assert_eq!(obligation.clause_index, index);
    }
    drop(obligations);
    wall.check();
    assert!(
        engines::validate_external_invariant_model(original, model, &wall.config())
            .expect("fresh full original model validation")
    );
    wall.check();
}

fn required_success(
    case: &'static str,
    input: &str,
    predicates: usize,
    clauses: usize,
    wall: Wall,
    sources: NativeSources,
) {
    let original = ChcParser::parse(input).expect("exact original fixture");
    assert_eq!(original.predicates().len(), predicates);
    assert_eq!(original.clauses().len(), clauses);
    wall.check();
    let run = engines::solve_pdr_proof(original.clone(), wall.config())
        .expect("original strict production PDR");
    same_source(&original, run.problem());
    wall.check();
    original_model(&run, &original, &wall);

    // Census starts only around the SAME actual production retained request.
    // It neither inserts a native solve nor reconstructs a diagnostic proof.
    let recording = start(case);
    let result = match &wall {
        Wall::R22Phases => run.run_checked_replay(wall.remaining()),
        Wall::W2Whole { cancellation, .. } => {
            run.run_checked_replay_with_cancellation(wall.remaining(), cancellation)
        }
    };
    let summary = CURRENT.with(|slot| {
        slot.borrow().as_ref().map(|census| {
            (
                census.owners,
                census.owner_caps.0,
                census.snapshots,
                census.source_count,
                census.incomplete,
            )
        })
    });
    drop(recording); // Dump after production operation/owner cleanup, also on red.
    let checked = result.expect("actual strict checked Safe replay MUST succeed");
    wall.check();
    let summary = summary.expect("active diagnostic census");
    assert_eq!(
        summary.0, 1,
        "one original request owner across every row/walk"
    );
    // One retained row's envelope at request creation: three metered walks
    // times the published whole-proof work bound of 400,000,000. Each
    // declared row adds one more (progress/settlement.rs); the row count
    // never scales it up front.
    assert_eq!(summary.1, 1_200_000_000, "one row's original work envelope");
    // Safe: every original clause is one UNSAT row, each with its own
    // native proof snapshot.
    assert_eq!(
        summary.2, clauses,
        "actual exact obligation discharge inventory required for every row"
    );
    if sources == NativeSources::Required {
        assert!(
            summary.3 > 0,
            "actual native proof source inventory required"
        );
    }
    assert!(
        !summary.4,
        "bounded diagnostic census may not silently truncate"
    );
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
    same_source(&original, checked.proof_run().problem());
    assert_eq!(
        checked.problem_bytes(),
        original.normalized_input().as_bytes()
    );
    assert!(!checked.certificate_bytes().is_empty());
    assert!(!checked.checked_report_bytes().is_empty());
    drop(checked);
    drop(run);
    drop(original);
    wall.check();
    wall.finish();
}

#[test]
fn census_r22_scalar_original_requires_checked_safe_same_owner() {
    required_success(
        "R22Scalar",
        R22_SCALAR,
        3,
        5,
        Wall::R22Phases,
        NativeSources::BooleanOnly,
    );
}
#[test]
fn census_r22_array_original_requires_checked_safe_same_owner() {
    required_success(
        "R22Array",
        R22_ARRAY,
        3,
        5,
        Wall::R22Phases,
        NativeSources::BooleanOnly,
    );
}
#[test]
fn census_w2_body_original_requires_checked_safe_same_owner() {
    required_success(
        "W2Body",
        W2_BODY,
        2,
        4,
        Wall::whole(),
        NativeSources::Required,
    );
}
#[test]
fn census_w2_exit_original_requires_checked_safe_same_owner() {
    required_success(
        "W2Exit",
        W2_EXIT,
        2,
        4,
        Wall::whole(),
        NativeSources::Required,
    );
}
