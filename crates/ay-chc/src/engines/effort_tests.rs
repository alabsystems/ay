// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The proof run's return boundary under an effort (P4a slice 8,
//! guard-tree.md §14).

use super::*;

/// A result decided within B is the count's: the boundary keeps it although
/// the solve deadline has passed and the token is set, where without an
/// effort the same late result is discarded.
#[test]
fn the_return_boundary_keeps_a_result_decided_under_an_effort() {
    let past = ay_core::time::Instant::now()
        .checked_sub(std::time::Duration::from_millis(1))
        .expect("a past instant");
    let token = CancellationToken::new();
    token.cancel();
    let late = || {
        VerifiedChcResult::from_validated(
            ChcEngineResult::Safe(InvariantModel::default()),
            ValidationEvidence::FullVerification,
        )
    };
    let config = PdrConfig::default().with_cancellation_token(Some(token));
    let without = enforce_pdr_proof_return_boundary(late(), &config, Some(past));
    assert!(without.is_unknown(), "{without:?}");
    let with = enforce_pdr_proof_return_boundary(late(), &config.with_effort(Some(10)), Some(past));
    assert!(with.is_safe(), "{with:?}");
}
