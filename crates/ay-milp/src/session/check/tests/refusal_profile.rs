// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-session first-refusal profiles must not contaminate later sessions.

use super::*;

fn observe_deferral(first_refusal_ms: usize) -> Option<(&'static str, &'static str)> {
    let opts = SolveOpts::new()
        .with_time_limit(Duration::from_secs(5))
        .with_engine(crate::EngineEconomics::new().with_anchor_first_refusal_ms(first_refusal_ms));
    let mut session = BabSession::new(specialized_pb_optimization_model(), &opts)
        .expect("valid specialized-PB session");
    let _ = session.check().expect("specialized-PB solve");
    session.deferred_lane()
}

fn assert_profile_order(order: [usize; 2]) {
    for first_refusal_ms in order {
        let observed = observe_deferral(first_refusal_ms);
        if first_refusal_ms == 0 {
            assert_eq!(observed, None, "zero disables deferral for this session");
        } else {
            assert_eq!(
                observed,
                Some(("specialized-pb", "no-better-than")),
                "a nonzero successor retains its own refusal profile"
            );
        }
    }
}

#[test]
fn zero_first_refusal_does_not_disable_a_later_nonzero_session() {
    assert_profile_order([0, 1_000]);
}

#[test]
fn nonzero_first_refusal_does_not_enable_a_later_zero_session() {
    assert_profile_order([1_000, 0]);
}
