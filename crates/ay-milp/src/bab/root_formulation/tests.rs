// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for root-formulation budget authority.

use std::time::{Duration, Instant};

use super::bounded_share_deadline;

#[test]
fn root_probe_share_never_extends_its_outer_deadline() {
    let started = Instant::now();
    let limit = started + Duration::from_secs(20);
    assert_eq!(
        bounded_share_deadline(started, limit, Some(0.0), 0.25),
        started
    );
    assert_eq!(
        bounded_share_deadline(started, limit, Some(1.0), 0.25),
        limit
    );
    let fallback = bounded_share_deadline(started, limit, None, 0.25);
    assert_eq!(
        bounded_share_deadline(started, limit, Some(2.0), 0.25),
        fallback
    );
    assert_eq!(
        bounded_share_deadline(started, limit, Some(f64::NAN), 0.25),
        fallback
    );
    assert!(fallback <= limit);
}
