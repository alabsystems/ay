// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! R22 acceptance targets, not an implemented solver fix or a qualification claim.
//!
//! The two fixtures are byte-identical to MODEL_CHECKER_CONSUMER's September 28 cyclic-array
//! request. Their names mean array-column absent/present, not unsafe/safe.
//! Both are Safe: `head = true`, `body(i) = i <u 4`, `error = false` is an
//! inductive model. The negative controls change ONLY the error-edge guard,
//! making `head(0) -> body(0) -> error` reachable (choose `x = 0` if needed).
//!
//! Exercise the strict in-process production PDR entry, not the CLI portfolio.
//! Safe acceptance separately requires full original-model verification and
//! checked certificate replay; metadata-only success is insufficient. These
//! unignored tests may fail until R22 is implemented. They were authored UNRUN.
//! Solve, model verification and checked replay each have an explicit 30-second
//! diagnostic phase budget, not one preserved 90-second deadline or the
//! consumer's whole-run 20/30-second acceptance envelope. That consumer lane
//! still needs its own measurement. Parsing, rendering and opaque cleanup are not hard-wall bounded;
//! run serially under an outer process/resource guard with normal test capture.

use ay_chc::{
    engines, ChcExpr, ChcParser, ChcPdrProofRun, ChcProblem, ChcSort, ClauseHead, PdrConfig,
    VerifiedChcResult,
};
use sha2::{Digest, Sha256};
use std::time::Duration;

const NO_ARRAY: &str =
    include_str!("model_checker_consumer_cyclic_arrays/loop_repro_array_false.smt2");
const WITH_ARRAY: &str =
    include_str!("model_checker_consumer_cyclic_arrays/loop_repro_array_true.smt2");
const PHASE_BUDGET: Duration = Duration::from_secs(30);
const SAFE_GUARD: &str = "(not (bvult i #x0000000000000004))";
const UNSAFE_GUARD: &str = "(bvult i #x0000000000000004)";

#[derive(Clone, Copy, Debug)]
enum Source {
    Scalar,
    Array,
}

impl Source {
    fn input(self) -> &'static str {
        match self {
            Self::Scalar => NO_ARRAY,
            Self::Array => WITH_ARRAY,
        }
    }

    fn raw_sha256(self) -> &'static str {
        match self {
            Self::Scalar => "bf72af69ed7640a1be265422da43390e14fd336423652c13dba442bb7eef5642",
            Self::Array => "126fa92e04a2aeaf0efabe8d1c4b098e99a28b4989fff3fbc571e8607ec202c9",
        }
    }

    fn argument_sorts(self) -> Vec<ChcSort> {
        let counter = ChcSort::BitVec(64);
        match self {
            Self::Scalar => vec![counter],
            Self::Array => vec![
                ChcSort::Array(Box::new(counter.clone()), Box::new(ChcSort::BitVec(32))),
                counter,
            ],
        }
    }
}

#[derive(Clone, Copy, Debug)]
enum Expected {
    Safe,
    Unsafe,
}

fn config() -> PdrConfig {
    // Exactly EncodeConfig::to_pdr_config with timeout=30s and no lemma hints.
    // solve_pdr_proof itself forces strict_proofs and preserve_original_clauses.
    let mut config = PdrConfig::production(false);
    config.solve_timeout = Some(PHASE_BUDGET);
    config
}

fn assert_source_shape(problem: &ChcProblem, source: Source) {
    assert_eq!(problem.predicates().len(), 3);
    assert_eq!(
        problem.clauses().len(),
        5,
        "four rules and the original query"
    );
    for name in ["head", "body", "error"] {
        let predicate = problem
            .predicates()
            .iter()
            .find(|p| p.name == name)
            .unwrap();
        let expected = if name == "error" {
            Vec::new()
        } else {
            source.argument_sorts()
        };
        assert_eq!(predicate.arg_sorts, expected, "source signature {name}");
    }
    if matches!(source, Source::Array) {
        // Do not replace this with the easier variable-initializer fixture:
        // the actual request has a non-variable constant-array fact argument.
        let fact = problem
            .clauses()
            .iter()
            .find(|c| c.body.predicates.is_empty())
            .unwrap();
        let ClauseHead::Predicate(_, args) = &fact.head else {
            panic!("the source initializer must remain a predicate fact");
        };
        assert!(matches!(
            args.first(),
            Some(ChcExpr::ConstArray(ChcSort::BitVec(64), _))
        ));
    }
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
            _ => panic!("the original clause head changed"),
        }
    }
}

fn assert_safe_model_and_replay(run: &ChcPdrProofRun, original: &ChcProblem, source: Source) {
    let VerifiedChcResult::Safe(invariant) = run.result() else {
        panic!("{source:?}: Safe is required; got {}", run.result());
    };
    let model = invariant.model();
    assert_eq!(model.len(), original.predicates().len());
    for predicate in original.predicates() {
        let interpretation = model
            .get(&predicate.id)
            .expect("every original predicate needs a model");
        let sorts: Vec<_> = interpretation
            .vars
            .iter()
            .map(|var| var.sort.clone())
            .collect();
        assert_eq!(
            sorts, predicate.arg_sorts,
            "model signature {}",
            predicate.name
        );
    }
    let obligations = model
        .replay_obligations(original)
        .expect("all original clauses must render");
    assert_eq!(obligations.len(), original.clauses().len());
    for (index, obligation) in obligations.iter().enumerate() {
        assert_eq!(obligation.clause_index, index);
    }
    drop(obligations);

    eprintln!("R22 {source:?}: full original-model verification (30s)");
    assert!(
        engines::validate_external_invariant_model(original, model, &config())
            .expect("fresh full original-model verification must not error")
    );

    eprintln!("R22 {source:?}: checked certificate replay (30s)");
    let checked = run
        .run_checked_replay(PHASE_BUDGET)
        .expect("Safe must pass checked replay; metadata-only evidence does not pass");
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
}

fn run(source: Source, expected: Expected) {
    let original_bytes = source.input();
    assert_eq!(
        format!("{:x}", Sha256::digest(original_bytes.as_bytes())),
        source.raw_sha256()
    );
    assert_eq!(original_bytes.matches(SAFE_GUARD).count(), 1);
    let input = match expected {
        Expected::Safe => original_bytes.to_owned(),
        Expected::Unsafe => original_bytes.replacen(SAFE_GUARD, UNSAFE_GUARD, 1),
    };
    eprintln!("R22 {source:?}/{expected:?}: parse exact source");
    let original = ChcParser::parse(&input).expect("the exact consumer fixture must parse");
    assert_source_shape(&original, source);
    eprintln!("R22 {source:?}/{expected:?}: strict production PDR (30s)");
    let run = engines::solve_pdr_proof(original.clone(), config())
        .expect("strict production PDR must not error");
    assert_same_problem(&original, run.problem());
    match expected {
        Expected::Safe => assert_safe_model_and_replay(&run, &original, source),
        Expected::Unsafe => assert!(
            matches!(run.result(), VerifiedChcResult::Unsafe(_)),
            "{source:?}: reachable body(0)->error must be Unsafe, not {}",
            run.result()
        ),
    }
    assert!(
        run.accepted_as_proof(),
        "Unknown is not an acceptance-target pass"
    );
    eprintln!("R22 {source:?}/{expected:?}: complete");
}

#[test]
fn scalar_consumer_original_requires_safe_model_and_checked_replay() {
    run(Source::Scalar, Expected::Safe);
}

#[test]
fn array_consumer_original_requires_safe_model_and_checked_replay() {
    run(Source::Array, Expected::Safe);
}

#[test]
fn scalar_reachable_error_neighbor_requires_accepted_unsafe() {
    run(Source::Scalar, Expected::Unsafe);
}

#[test]
fn array_reachable_error_neighbor_requires_accepted_unsafe() {
    run(Source::Array, Expected::Unsafe);
}
