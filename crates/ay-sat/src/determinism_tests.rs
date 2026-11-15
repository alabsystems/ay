// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Counted round overhead lands in the bucket the same wall overhead would:
/// `adaptive_tick_scale` splits at 1, 3 and 8 ms, the compaction bias at 10
/// and 100 ms, and `TICKS_PER_MS` tick equivalents make one millisecond.
#[test]
fn counted_overhead_meets_the_wall_buckets_at_their_boundaries() {
    assert_eq!(overhead_ms_equiv(7_500), 1.0);
    assert!(overhead_ms_equiv(7_499) < 1.0);
    assert_eq!(overhead_ms_equiv(22_500), 3.0);
    assert!(overhead_ms_equiv(22_499) < 3.0);
    assert_eq!(overhead_ms_equiv(60_000), 8.0);
    assert!(overhead_ms_equiv(59_999) < 8.0);
    assert_eq!(overhead_ms_equiv(75_000), 10.0);
    assert!(overhead_ms_equiv(74_999) < 10.0);
    assert_eq!(overhead_ms_equiv(750_000), 100.0);
    assert!(overhead_ms_equiv(750_001) > 100.0);
}

/// A finished round with no counted overhead is the cheapest round, not "no
/// data": the readers treat 0.0 as missing and would pick the most
/// conservative scale.
#[test]
fn a_round_with_no_counted_overhead_still_reads_as_measured() {
    assert!(overhead_ms_equiv(0) > 0.0);
    assert_eq!(overhead_ms_equiv(0), overhead_ms_equiv(1));
}

/// The converted walls read as the walls they replace.
#[test]
fn converted_budgets_are_their_walls_at_the_calibrated_rate() {
    assert_eq!(ROUND_TICK_BUDGET, 2_000 * TICKS_PER_MS);
    assert_eq!(LOOKAHEAD_TICK_BUDGET, 500 * TICKS_PER_MS);
    assert_eq!(GATE_EXTRACT_DET_WORK_BUDGET, 2_000 * TICKS_PER_MS);
}
