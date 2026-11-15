// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The quantified-source clause share is the caller's envelope, never the flat
//! lane's five-second ceiling. Measured before this rule: the nested Vec store
//! consecution and the projected nested-record fact each need about two
//! seconds of finite solving at load 40, and past 2.5 s (the finite half of
//! the old five-second cap) at load 60, where both certificates flipped to
//! Unknown with 20-33 s of their caller's envelope unspent.

use super::*;

#[test]
fn the_last_clause_keeps_the_whole_remaining_envelope() {
    let remaining = Duration::from_secs(33);
    assert_eq!(clause_budget(remaining, 1), remaining);
    assert!(
        clause_budget(remaining, 1) / 2 > Duration::from_millis(2_500),
        "the finite half must exceed the old 2.5 s slice that expired under load"
    );
}

#[test]
fn waiting_clauses_split_the_remaining_envelope_fairly() {
    let remaining = Duration::from_secs(30);
    assert_eq!(clause_budget(remaining, 3), Duration::from_secs(10));
    assert_eq!(clause_budget(remaining, 2), Duration::from_secs(15));
    // A degenerate count never mints more than the remaining envelope.
    assert_eq!(clause_budget(remaining, 0), remaining);
    assert_eq!(clause_budget(Duration::ZERO, 3), Duration::ZERO);
    assert_eq!(
        clause_budget(remaining, usize::MAX),
        remaining / u32::MAX,
        "an absurd count saturates the divisor instead of wrapping"
    );
}
