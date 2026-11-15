// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// NEGATIVE CONTROL: the shared runner refuses the pair pinned carcara prints
/// `valid` for only through its `evaluate` defect, for every expected verdict:
/// a guard refusal never satisfies an `invalid` expectation either.
#[test]
fn the_carcara_runner_refuses_a_document_pinned_carcara_misjudges() {
    for expected in ["valid", "holey", "invalid"] {
        let refused = std::panic::catch_unwind(|| {
            assert_carcara_verdict(
                "false_valid_control",
                ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROBLEM,
                ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF,
                expected,
            );
        });
        let message = refused.expect_err("the misjudged pair must be refused");
        let message = message
            .downcast_ref::<String>()
            .map(String::as_str)
            .unwrap_or_default();
        assert!(message.contains("is not evidence"), "{expected}: {message}");
    }
}
