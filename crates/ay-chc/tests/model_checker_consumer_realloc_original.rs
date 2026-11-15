// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! R29: the unchanged consumer realloc-grow query must actually be Safe.
//!
//! No query slicing, projection, discharge substitution or expected-Unknown
//! escape is used. The fresh model check receives the original parsed clauses,
//! not a transformed producer problem. One fixed 20-second owner covers source
//! hashing, parsing, configuration, strict production solving, independent
//! original-model validation and cleanup. Public duration APIs receive only
//! that owner's remainder, and its cancellation timer is never renewed.
//!
//! Run this standalone integration binary serially under the shared external
//! process guard with a 4 GiB RSS ceiling. The configuration below is a term
//! memory ceiling, not aggregate RSS enforcement. Opaque operations and worker
//! cleanup remain cooperative; passing is not a hard in-process latency claim.

use ay_chc::{
    engines::{
        validate_external_invariant_model_with_owner, ExternalInvariantValidation,
        ExternalInvariantValidationOwner,
    },
    AdaptiveConfig, AdaptivePortfolio, CancellationToken, ChcParser, PdrConfig, VerifiedChcResult,
};
use ay_core::resource::{current_guard, ChildSpec, DeadlineSource, Guard, NodeLabel};
use ay_core::time::Instant;
use sha2::{Digest, Sha256};
use std::time::Duration;

const ORIGINAL: &str = include_str!("fixtures/model_checker_consumer_realloc_grow_original.smt2");
const ORIGINAL_BYTES: usize = 311_060;
const ORIGINAL_SHA256: &str = "0930146db6fc0c3e308d87dff805d02e20c4959e3b40c7a3c455e1ab636412d7";
const ORIGINAL_BUDGET: Duration = Duration::from_secs(20);
const TERM_MEMORY_BYTES: usize = 4 * 1024 * 1024 * 1024;

fn remaining(owner: &ExternalInvariantValidationOwner, phase: &str) -> Duration {
    assert_eq!(owner.check(), None, "original owner stopped before {phase}");
    let left = owner.deadline().saturating_duration_since(Instant::now());
    assert!(!left.is_zero(), "zero must not become an unlimited {phase}");
    left
}

#[test]
fn unchanged_realloc_grow_is_safe_and_freshly_validates_within_original_20s() {
    let started = Instant::now();
    let deadline = started + ORIGINAL_BUDGET;
    let cancellation = CancellationToken::new();
    let spec = ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Fixed(deadline));
    let guard = current_guard().map_or_else(
        || Guard::root_child(spec.clone()),
        |parent| parent.child(spec.clone()),
    );
    let _guard_scope = guard.enter();
    let mut validation_config = PdrConfig::default()
        .with_strict_proofs(true)
        .with_cancellation_token(Some(cancellation.clone()))
        .with_memory_budget(Some(TERM_MEMORY_BYTES));
    validation_config.solve_timeout = Some(deadline.saturating_duration_since(Instant::now()));
    // This public owner captures the original callback, Guard and ambient lane
    // before reading the source; both phases borrow the SAME retained owner.
    let owner = ExternalInvariantValidationOwner::capture(&guard, &validation_config);
    let timer = cancellation.cancel_after(remaining(&owner, "source admission"));
    let (original, report) = owner
        .with_resources(|| {
            assert_eq!(ORIGINAL.len(), ORIGINAL_BYTES);
            assert_eq!(
                format!("{:x}", Sha256::digest(ORIGINAL.as_bytes())),
                ORIGINAL_SHA256
            );
            let original = ChcParser::parse(ORIGINAL)?;
            let mut config = AdaptiveConfig::with_budget(remaining(&owner, "configuration"), false)
                .with_memory_budget(TERM_MEMORY_BYTES);
            config.strict_proofs = true;
            let portfolio = AdaptivePortfolio::new_for_solve_with_cancellation(
                original.clone(),
                config,
                &cancellation,
            );
            let report = portfolio.solve_proof_run_with_budget_report();
            drop(portfolio);
            Ok((original, report))
        })
        .expect("original strict production route must run without an internal error")
        .expect("production must finish within the original owner");
    validation_config.solve_timeout =
        Some(remaining(&owner, "independent original-model validation"));
    match report.proof_run().result() {
        VerifiedChcResult::Safe(invariant) => {
            let checked = validate_external_invariant_model_with_owner(
                &original,
                invariant.model(),
                &validation_config,
                &owner,
            )
            .expect("fresh original-model verification must run");
            assert_eq!(
                checked,
                ExternalInvariantValidation::Valid,
                "the returned model must independently prove every ORIGINAL clause"
            );
        }
        result => panic!("R29 requires actual strict Safe; Unknown/Unsafe is failure: {result}"),
    }
    drop(report);
    drop(original);
    drop(validation_config);
    drop(timer); // Wake and join the same timer before final publication.
    assert_eq!(owner.check(), None, "original owner stopped during cleanup");
    assert!(
        started.elapsed() < ORIGINAL_BUDGET,
        "the whole case must fit its original 20s"
    );
}
