// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// `originals` unit originals, then `derived` learned rows each resting on
/// the first `hints` originals, the last row empty.
fn wide(originals: u64, derived: u64, hints: u64) -> (OriginalArena, ClauseTrace) {
    let count = usize::try_from(originals).unwrap();
    let arena = OriginalArena {
        literals: vec![x(); count],
        offsets: (0..u32::try_from(originals).unwrap()).collect(),
        ids: (1..=originals).collect(),
    };
    let bytes = arena.retained_bytes().unwrap();
    let mut trace = ClauseTrace::new();
    assert!(trace.begin_original_transfer(OriginalControl::capture(None, None, None).unwrap()));
    for admitted in 1..=count {
        assert!(trace.note_ledger_original(admitted, bytes));
    }
    let resting: Vec<u64> = (1..=hints).collect();
    for id in originals + 1..originals + derived {
        trace.add_clause_with_hint_slices(id, &[x()], false, &resting);
    }
    trace.add_clause_with_hint_slices(originals + derived, &[], false, &[originals + 1]);
    (arena, trace)
}

/// The units the transfer of [`wide`]`(64, 2000, 8)` charges.
fn wide_units() -> u64 {
    let (originals, mut trace) = wide(64, 2_000, 8);
    let mut used = 0;
    assert!(trace.finish_original_transfer(originals, 1, &mut |units| {
        used += units;
        true
    }));
    used
}

/// What the validation of fd4e00f75, which asked the caller once per unit,
/// charged for [`wide`]`(64, 2000, 8)`: counted on that build's callback,
/// and by a model of its walk (128 for the originals, 4,063 for the derived
/// rows, the rest for the events and their hint lookups).
const WIDE_UNITS_ONE_CALL_EACH: u64 = 288_068;

#[test]
fn the_chunks_add_up_to_the_units_a_call_per_unit_charged() {
    assert_eq!(wide_units(), WIDE_UNITS_ONE_CALL_EACH);
}

#[test]
fn the_caller_is_asked_once_a_chunk_not_once_a_unit() {
    let (originals, mut trace) = wide(64, 2_000, 8);
    let (mut used, mut calls) = (0, 0);
    assert!(trace.finish_original_transfer(originals, 1, &mut |units| {
        used += units;
        calls += 1;
        true
    }));
    assert_eq!(used, WIDE_UNITS_ONE_CALL_EACH);
    assert!(used > 16 * validate::CHUNK, "{used} units");
    // A call per chunk, and one where each of the three phases settles.
    assert!(
        calls <= used / validate::CHUNK + 3,
        "{calls} calls for {used} units"
    );
}

#[test]
fn a_wide_transfer_one_unit_short_of_its_grant_is_refused() {
    let used = WIDE_UNITS_ONE_CALL_EACH;
    // Refused in the first chunk, in the middle, on the final settle; and
    // the exact grant, accepted.
    for grant in [validate::CHUNK - 1, used / 2, used - 1, used] {
        let (originals, mut trace) = wide(64, 2_000, 8);
        let mut left = grant;
        let mut handed = 0;
        let mut calls_after_refusal = 0;
        let mut refused = false;
        let accepted = trace.finish_original_transfer(originals, 1, &mut |units| {
            if refused {
                calls_after_refusal += 1;
            }
            handed += units;
            refused |= units > left;
            left = left.saturating_sub(units);
            !refused
        });
        assert_eq!(accepted, grant == used, "grant {grant} of {used}");
        assert_eq!(calls_after_refusal, 0, "grant {grant}");
        // An overdraft is seen at most one chunk late.
        assert!(
            handed <= grant + validate::CHUNK,
            "{handed} handed for {grant}"
        );
    }
}

/// The meter itself, without the captured control's own stickiness: a
/// refusal is final wherever in the walk it falls, and is seen within a
/// chunk of the overdraft.
#[test]
fn a_refusal_by_the_caller_is_final_wherever_it_falls() {
    let (originals, trace) = wide(64, 2_000, 8);
    let used = WIDE_UNITS_ONE_CALL_EACH;
    let mut grants: Vec<u64> = (0..used).step_by(997).collect();
    grants.extend([validate::CHUNK - 1, validate::CHUNK, used - 1, used]);
    for grant in grants {
        let mut left = grant;
        let mut handed = 0;
        let mut calls_after_refusal = 0;
        let mut refused = false;
        let accepted = validate::structure(&trace, &originals, 1, &mut |units| {
            if refused {
                calls_after_refusal += 1;
            }
            handed += units;
            refused |= units > left;
            left = left.saturating_sub(units);
            !refused
        });
        assert_eq!(accepted, grant == used, "grant {grant} of {used}");
        assert_eq!(calls_after_refusal, 0, "grant {grant}");
        assert!(
            handed <= grant + validate::CHUNK,
            "{handed} handed for {grant}"
        );
    }
}

#[test]
fn a_structural_refusal_pays_for_what_it_read() {
    let (originals, mut trace) = wide(64, 2_000, 8);
    // The terminal row's hint names no row: refused at its very last lookup.
    let last = trace.hint_pool.len() - 1;
    trace.hint_pool[last] = 99_999;
    let mut used = 0;
    assert!(!trace.finish_original_transfer(originals, 1, &mut |units| {
        used += units;
        true
    }));
    // Every unit the walk read before it refused, as fd4e00f75's
    // call-per-unit walk charged them (its callback and the model agree).
    assert_eq!(used, 288_067);
}
