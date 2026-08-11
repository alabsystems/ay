// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn sat_unknown_reason_mapping_is_specific() {
    let mut reason = None;

    Executor::record_sat_unknown_reason(&mut reason, Some(SatUnknownReason::Interrupted));
    assert_eq!(reason, Some(UnknownReason::Interrupted));

    assert_eq!(
        Executor::map_sat_unknown_origin(SatUnknownReason::DeadlineExceeded),
        UnknownOrigin::SolveDeadline
    );
    Executor::record_sat_unknown_reason(&mut reason, Some(SatUnknownReason::DeadlineExceeded));
    assert_eq!(reason, Some(UnknownReason::Timeout));

    Executor::record_sat_unknown_reason(&mut reason, Some(SatUnknownReason::UnsupportedConfig));
    assert_eq!(reason, Some(UnknownReason::Unsupported));

    Executor::record_sat_unknown_reason(&mut reason, Some(SatUnknownReason::EmptyTheoryConflict));
    assert_eq!(reason, Some(UnknownReason::Unknown));
}
