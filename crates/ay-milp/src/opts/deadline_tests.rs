// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#[test]
fn overflowing_relative_limit_means_no_duration_cap() {
    let now = Instant::now();
    assert!(now.checked_add(Duration::MAX).is_none());

    let opts = SolveOpts::new().with_time_limit(Duration::MAX);
    assert_eq!(opts.effective_deadline(now), None);
}

#[test]
fn explicit_deadline_survives_an_overflowing_relative_limit() {
    let now = Instant::now();
    assert!(now.checked_add(Duration::MAX).is_none());
    let deadline = now + Duration::from_secs(1);
    let opts = SolveOpts::new()
        .with_deadline(deadline)
        .with_time_limit(Duration::MAX);

    assert_eq!(opts.effective_deadline(now), Some(deadline));
}

#[test]
fn node_warm_time_limit_defaults_off() {
    assert_eq!(SolveOpts::new().node_warm_time_limit, None);
}

#[test]
fn node_warm_time_limit_builder_normalizes_zero_and_none() {
    let finite = Duration::from_millis(250);
    assert_eq!(
        SolveOpts::new()
            .with_node_warm_time_limit(Some(finite))
            .node_warm_time_limit,
        Some(finite)
    );
    assert_eq!(
        SolveOpts::new()
            .with_node_warm_time_limit(Some(Duration::ZERO))
            .node_warm_time_limit,
        None
    );
    assert_eq!(
        SolveOpts::new()
            .with_node_warm_time_limit(None)
            .node_warm_time_limit,
        None
    );
}
