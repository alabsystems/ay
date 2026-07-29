// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guards for the staged shared-native-B&B fixed-prefix frontier.
//!
//! The default `BabSession::check` path remains untouched. These tests opt in
//! explicitly and exercise the proof obligations that matter before NY can
//! replace sixteen cloned sessions: complete partition coverage, one common
//! verdict, fail-closed validation/deadlines, and independently replayable
//! whole-tree evidence.

use std::num::NonZeroUsize;
use std::time::{Duration, Instant};

use ay_milp::{
    BabSession, Col, MilpInfeasibilityCertificate, Model, Outcome, Sense, SolveOpts, TreeNode,
    UnknownReason,
};
use num_rational::BigRational;

fn optimum(outcome: Outcome) -> BigRational {
    match outcome {
        Outcome::Optimal { value, .. } => value,
        other => panic!("expected Optimal, got {other:?}"),
    }
}

fn fractional_triangle() -> (Model, [Col; 3]) {
    // The unique LP point is (1/2, 1/2, 1/2), while every binary
    // assignment is contradictory.
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    let z = model.add_binary_col();
    model.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
    model.add_row(1.0, 1.0, &[(y, 1.0), (z, 1.0)]);
    model.add_row(1.0, 1.0, &[(x, 1.0), (z, 1.0)]);
    (model, [x, y, z])
}

fn proof_first_tree(model: &Model, prefix: &[Col], workers: usize) -> MilpInfeasibilityCertificate {
    let opts = SolveOpts::new()
        .with_tree_cert_leaves(64)
        .with_require_certificates(true);
    let mut session = BabSession::new(model.clone(), &opts).expect("proof-first session");
    match session
        .check_shared_binary_prefix_proof_first(
            prefix,
            NonZeroUsize::new(workers).expect("test worker count is nonzero"),
        )
        .expect("proof-first solve")
    {
        Outcome::Infeasible {
            cert: None,
            tree_cert: Some(tree),
        } => tree,
        other => panic!("expected tree-certified Infeasible, got {other:?}"),
    }
}

#[test]
fn shared_prefix_matches_the_unsplit_native_optimum() {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    let z = model.add_binary_col();
    model.add_row(2.0, f64::INFINITY, &[(x, 1.0), (y, 1.0), (z, 1.0)]);
    model.set_objective(&[(x, 1.0), (y, 2.0), (z, 3.0)], Sense::Minimize);

    let opts = SolveOpts::new().with_tree_cert_leaves(0);
    let mut ordinary = BabSession::new(model.clone(), &opts).expect("ordinary session");
    let ordinary = optimum(ordinary.check().expect("ordinary solve"));

    let mut shared = BabSession::new(model, &opts).expect("shared session");
    let shared = optimum(
        shared
            .check_shared_binary_prefix(&[x, y])
            .expect("shared-prefix solve"),
    );

    assert_eq!(shared, ordinary);
    assert_eq!(shared, BigRational::from_integer(3.into()));
}

#[test]
fn proof_first_prefix_matches_the_unsplit_native_optimum() {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    let z = model.add_binary_col();
    model.add_row(2.0, f64::INFINITY, &[(x, 1.0), (y, 1.0), (z, 1.0)]);
    model.set_objective(&[(x, 1.0), (y, 2.0), (z, 3.0)], Sense::Minimize);

    let opts = SolveOpts::new().with_tree_cert_leaves(0);
    let mut ordinary = BabSession::new(model.clone(), &opts).expect("ordinary session");
    let ordinary = optimum(ordinary.check().expect("ordinary solve"));

    let mut proof_first = BabSession::new(model, &opts).expect("proof-first session");
    let prepared = optimum(
        proof_first
            .check_shared_binary_prefix_proof_first(
                &[x, y],
                NonZeroUsize::new(3).expect("three is nonzero"),
            )
            .expect("proof-first solve"),
    );
    assert_eq!(prepared, ordinary);
    assert_eq!(prepared, BigRational::from_integer(3.into()));
}

#[test]
fn complete_prefix_infeasibility_exports_a_replay_verified_tree() {
    // The unique LP point is (1/2, 1/2, 1/2), so the root relaxation is
    // feasible while every binary assignment is infeasible. This forces the
    // certificate to use the split tree rather than a root Farkas ray.
    let mut model = Model::new();
    let x = model.add_binary_col();
    let y = model.add_binary_col();
    let z = model.add_binary_col();
    model.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
    model.add_row(1.0, 1.0, &[(y, 1.0), (z, 1.0)]);
    model.add_row(1.0, 1.0, &[(x, 1.0), (z, 1.0)]);

    let opts = SolveOpts::new()
        .with_tree_cert_leaves(64)
        .with_require_certificates(true);
    let mut session = BabSession::new(model.clone(), &opts).expect("shared session");
    let outcome = session
        .check_shared_binary_prefix(&[x, y, z])
        .expect("shared-prefix solve");

    match outcome {
        Outcome::Infeasible {
            cert: None,
            tree_cert: Some(tree),
        } => {
            assert!(tree.num_leaves() <= 64);
            tree.verify(&model)
                .expect("shared-prefix tree must replay in caller frame");
        }
        other => panic!("expected tree-certified Infeasible, got {other:?}"),
    }
    assert!(
        session.replay_claims().is_empty(),
        "verified tree evidence must not be replaced by a replay-only claim"
    );
}

#[test]
fn proof_first_tree_is_replayable_deterministic_and_rejects_tampering() {
    let (model, prefix) = fractional_triangle();
    let first = proof_first_tree(&model, &prefix, 3);
    first
        .verify(&model)
        .expect("proof-first tree must independently replay");

    for _ in 0..2 {
        let again = proof_first_tree(&model, &prefix, 3);
        assert_eq!(
            again, first,
            "fixed ranks and worker ownership must yield one canonical tree"
        );
    }

    let mut tampered = first;
    match &mut tampered.root {
        TreeNode::Split { cut, .. } => {
            *cut += BigRational::new(1.into(), 2.into());
        }
        TreeNode::Leaf { .. } => panic!("a complete three-column prefix must begin with a split"),
    }
    assert!(
        tampered.verify(&model).is_err(),
        "a non-integral split destroys coverage and must be rejected"
    );
}

#[test]
fn proof_first_workers_are_not_required_for_authority() {
    let (model, prefix) = fractional_triangle();
    // One byte cannot admit an owned FloatLp clone. The explicit path must
    // retain every canonical node and let the ordinary serial proof close it.
    let opts = SolveOpts::new()
        .with_memory_budget(Some(1))
        .with_tree_cert_leaves(64)
        .with_require_certificates(true);
    let mut session = BabSession::new(model.clone(), &opts).expect("proof-first session");
    let outcome = session
        .check_shared_binary_prefix_proof_first(
            &prefix,
            NonZeroUsize::new(4).expect("four is nonzero"),
        )
        .expect("memory decline is fail-closed, not an API error");
    match outcome {
        Outcome::Infeasible {
            tree_cert: Some(tree),
            ..
        } => tree
            .verify(&model)
            .expect("serial fallback tree must remain independently authoritative"),
        other => panic!("expected certified serial fallback, got {other:?}"),
    }
}

#[test]
fn invalid_prefixes_fail_closed_before_solving() {
    let mut model = Model::new();
    let live = model.add_binary_col();
    let duplicate = live;
    let fixed = model.add_binary_col();
    model.fix_col(fixed, 0.0);
    let continuous = model.add_col(0.0, 1.0);
    let mut foreign = Model::new();
    let stale = (0..100)
        .map(|_| foreign.add_binary_col())
        .last()
        .expect("foreign column");
    let opts = SolveOpts::new();

    let bad: &[&[Col]] = &[&[], &[live, duplicate], &[fixed], &[continuous], &[stale]];
    for &prefix in bad {
        let mut session = BabSession::new(model.clone(), &opts).expect("valid session");
        assert!(
            session.check_shared_binary_prefix(prefix).is_err(),
            "invalid prefix {prefix:?} must not be silently normalized"
        );
        let mut proof_first = BabSession::new(model.clone(), &opts).expect("valid session");
        assert!(
            proof_first
                .check_shared_binary_prefix_proof_first(
                    prefix,
                    NonZeroUsize::new(2).expect("two is nonzero"),
                )
                .is_err(),
            "proof-first invalid prefix {prefix:?} must use the same typed validation"
        );
    }

    let mut too_deep_model = Model::new();
    let cols: Vec<Col> = (0..5).map(|_| too_deep_model.add_binary_col()).collect();
    let mut too_deep = BabSession::new(too_deep_model, &opts).expect("valid five-binary session");
    assert!(too_deep.check_shared_binary_prefix(&cols).is_err());

    let mut continuous_model = Model::new();
    let continuous_only = continuous_model.add_col(0.0, 1.0);
    let mut non_native =
        BabSession::new(continuous_model, &opts).expect("continuous session is valid");
    assert!(
        non_native
            .check_shared_binary_prefix(&[continuous_only])
            .is_err(),
        "the staged frontier must not silently cross into the continuous LP lane"
    );
}

#[test]
fn expired_common_deadline_returns_unknown_not_a_partial_verdict() {
    let mut model = Model::new();
    let cols: Vec<Col> = (0..4).map(|_| model.add_binary_col()).collect();
    model.add_row(
        2.0,
        2.0,
        &cols.iter().copied().map(|c| (c, 1.0)).collect::<Vec<_>>(),
    );
    let expired = Instant::now()
        .checked_sub(Duration::from_secs(1))
        .expect("monotonic clock supports one-second lookback");
    let opts = SolveOpts::new()
        .with_deadline(expired)
        .with_tree_cert_leaves(0);
    let mut session = BabSession::new(model.clone(), &opts).expect("shared session");

    assert!(matches!(
        session
            .check_shared_binary_prefix(&cols)
            .expect("deadline is a verdict, not a hard error"),
        Outcome::Unknown {
            reason: UnknownReason::Timeout
        }
    ));

    let mut proof_first = BabSession::new(model, &opts).expect("proof-first session");
    assert!(matches!(
        proof_first
            .check_shared_binary_prefix_proof_first(
                &cols,
                NonZeroUsize::new(4).expect("four is nonzero"),
            )
            .expect("expired worker deadline is a verdict, not a hard error"),
        Outcome::Unknown {
            reason: UnknownReason::Timeout
        }
    ));
}

#[test]
fn shared_prefix_rejects_external_incumbent_ownership_until_snapshot_replay_exists() {
    let mut model = Model::new();
    let x = model.add_binary_col();
    let mut session = BabSession::new(model, &SolveOpts::new()).expect("session");
    session.seed_incumbent(&[0.0]);

    let error = session
        .check_shared_binary_prefix(&[x])
        .expect_err("mixed ownership must fail closed");
    assert!(
        error.to_string().contains("external incumbent seed"),
        "typed error should identify the unsupported composition: {error}"
    );
}
