// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn external_only_pdr_token_survives_config_drop_and_reaches_replay() {
    let parent = CancellationToken::new();
    let mut config = PdrConfig::default();
    config.external_cancellation_token = Some(parent.child());
    let retained = config.effective_cancellation_token();
    drop(config);
    parent.cancel();
    let original = run();
    let metadata = original.metadata().to_json_value();
    let stopped =
        attach_checked_replay_with_cancellation(original, REPLAY_BUDGET, retained.as_ref());
    assert_eq!(stopped.metadata().to_json_value(), metadata);
    assert!(!stopped.metadata().trust_full_verifier_admissible());
}

#[test]
fn either_pdr_channel_reaches_typed_replay_without_poisoning_the_other() {
    for external_cancels in [false, true] {
        let regular = CancellationToken::new();
        let external = CancellationToken::new();
        let mut config = PdrConfig::default();
        config.cancellation_token = Some(regular.child());
        config.external_cancellation_token = Some(external.child());
        let retained = config.effective_cancellation_token();
        if external_cancels {
            external.cancel();
        } else {
            regular.cancel();
        }
        let original = run();
        let metadata = original.metadata().to_json_value();
        let stopped =
            attach_checked_replay_with_cancellation(original, REPLAY_BUDGET, retained.as_ref());
        assert_eq!(stopped.metadata().to_json_value(), metadata);
        assert_eq!(regular.is_cancelled(), !external_cancels);
        assert_eq!(external.is_cancelled(), external_cancels);
    }
}

#[test]
fn live_bmc_parent_and_absent_token_preserve_original_checked_metadata() {
    let parent = CancellationToken::new();
    let mut config = BmcConfig::default();
    config.base.cancellation_token = Some(parent.child());
    let retained = config.base.cancellation_token.clone();
    drop(config);
    let original = run();
    let expected = attach_checked_replay_with_cancellation(original.clone(), REPLAY_BUDGET, None);
    let actual =
        attach_checked_replay_with_cancellation(original, REPLAY_BUDGET, retained.as_ref());
    assert_eq!(
        actual.metadata().to_json_value(),
        expected.metadata().to_json_value()
    );
    assert!(actual.metadata().trust_full_verifier_admissible());
    assert!(!parent.is_cancelled());
}
