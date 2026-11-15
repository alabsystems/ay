// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::test_util::lit as literal;
use std::cell::Cell;

mod errors;

// Frozen bytes from the pre-control binary/text encodings. These fixtures test
// serialization, not a claim that these caller-prevalidated hints form a proof.
const BINARY: &[u8] = &[
    b'a', 8, 2, 129, 1, 128, 128, 1, 0, 3, 4, 0, b'a', 10, 0, 2, 6, 0, b'd', 2, 4, 0, b'a', 12, 0,
    8, 6, 0, b'd', 6, 0,
];
const TEXT: &[u8] = b"4 1 -64 8192 0 -1 2 0\n5 0 1 3 0\n6 d 1 2 0\n7 0 4 3 0\n8 d 3 0\n";

fn records(writer: &mut LratWriter<Vec<u8>>, keep: &dyn Fn() -> bool) -> io::Result<()> {
    let first = writer.reserve_id();
    let second = writer.reserve_id();
    assert_eq!((first, second), (4, 5));
    writer.delete(1)?;
    writer.delete(2)?;
    writer.add_with_id_bounded_prevalidated_rup_with_cancellation(
        first,
        &[literal(0, true), literal(63, false), literal(8191, true)],
        &[-1, 2],
        keep,
    )?;
    writer.add_with_id_bounded_prevalidated_rup_with_cancellation(second, &[], &[1, 3], keep)?;
    let expected = if writer.binary { 6 } else { 7 };
    assert_eq!(
        writer.add_bounded_prevalidated_rup_with_cancellation(&[], &[4, 3], keep)?,
        expected
    );
    writer.delete(3)?;
    writer.flush_with_cancellation(keep)
}

#[test]
fn controlled_and_legacy_encodings_match_frozen_binary_and_text() {
    for binary in [false, true] {
        let mut writer = LratWriter::new(Vec::new(), binary, 3, None, None);
        let polls = Cell::new(0usize);
        records(&mut writer, &|| {
            polls.set(polls.get() + 1);
            true
        })
        .unwrap();
        assert!(polls.get() > 20);
        assert_eq!((writer.added_count(), writer.deleted_count()), (3, 3));
        let expected = if binary { BINARY } else { TEXT };
        assert_eq!(
            writer.into_inner_with_cancellation(&|| true).unwrap(),
            expected
        );

        let mut legacy = LratWriter::new(Vec::new(), binary, 3, None, None);
        let first = legacy.reserve_id();
        let second = legacy.reserve_id();
        legacy.delete(1).unwrap();
        legacy.delete(2).unwrap();
        legacy
            .add_with_id_signed_hints(
                first,
                &[literal(0, true), literal(63, false), literal(8191, true)],
                &[-1, 2],
            )
            .unwrap();
        legacy
            .add_with_id_signed_hints(second, &[], &[1, 3])
            .unwrap();
        legacy.add(&[], &[4, 3]).unwrap();
        legacy.delete(3).unwrap();
        assert_eq!(legacy.into_inner().unwrap(), expected);
    }
}

#[test]
fn every_record_poll_refusal_poisoned_and_never_retried() {
    for binary in [false, true] {
        let polls = Cell::new(0usize);
        let mut accepted = LratWriter::new(Vec::new(), binary, 3, None, None);
        records(&mut accepted, &|| {
            polls.set(polls.get() + 1);
            true
        })
        .unwrap();
        for stop in 1..=polls.get() {
            let mut writer = LratWriter::new(Vec::new(), binary, 3, None, None);
            let visits = Cell::new(0usize);
            let error = records(&mut writer, &|| {
                visits.set(visits.get() + 1);
                visits.get() != stop
            })
            .unwrap_err();
            assert!(
                is_bounded_emission_cancelled(&error),
                "format {binary}, poll {stop}: {error}"
            );
            assert_eq!(error.kind(), io::ErrorKind::Other);
            assert_eq!(visits.get(), stop);
            assert!(writer.has_io_error());
            let bytes = writer.get_ref().clone();
            let error = writer
                .flush_with_cancellation(&|| panic!("latched callback retried"))
                .unwrap_err();
            assert!(is_bounded_emission_cancelled(&error));
            assert!(is_bounded_emission_cancelled(
                &writer.add_bounded_prevalidated_rup(&[], &[1]).unwrap_err()
            ));
            assert_eq!(*writer.get_ref(), bytes);
            assert!(is_bounded_emission_cancelled(
                &writer.into_inner().unwrap_err()
            ));
        }
    }
}

#[test]
fn final_record_poll_can_refuse_complete_bytes_without_publishing_id() {
    let count = Cell::new(0usize);
    let mut accepted = LratWriter::new_binary(Vec::new(), 2);
    accepted
        .add_bounded_prevalidated_rup_with_cancellation(&[], &[1, 2], &|| {
            count.set(count.get() + 1);
            true
        })
        .unwrap();
    let visits = Cell::new(0usize);
    let mut refused = LratWriter::new_binary(Vec::new(), 2);
    let error = refused
        .add_bounded_prevalidated_rup_with_cancellation(&[], &[1, 2], &|| {
            visits.set(visits.get() + 1);
            visits.get() != count.get()
        })
        .unwrap_err();
    assert!(is_bounded_emission_cancelled(&error));
    assert_eq!(refused.get_ref(), accepted.get_ref());
    assert_eq!(refused.added_count(), 0);
    assert_eq!(refused.next_id(), 3);
    assert_eq!(refused.latest_id, 2);
    assert!(refused.into_inner().is_err());
}

#[test]
fn extraction_drains_deletions_and_refuses_every_poll_including_final_admission() {
    for binary in [false, true] {
        let make = || {
            let mut writer = LratWriter::new(Vec::new(), binary, 130, None, None);
            writer.delete(1).unwrap();
            writer.delete(130).unwrap();
            writer
        };
        let polls = Cell::new(0usize);
        let bytes = make()
            .into_inner_with_cancellation(&|| {
                polls.set(polls.get() + 1);
                true
            })
            .unwrap();
        let expected: &[u8] = if binary {
            &[b'd', 2, 132, 2, 0]
        } else {
            b"131 d 1 130 0\n"
        };
        assert_eq!(bytes, expected);
        assert!(polls.get() >= 5);
        for stop in 1..=polls.get() {
            let visits = Cell::new(0usize);
            let error = make()
                .into_inner_with_cancellation(&|| {
                    visits.set(visits.get() + 1);
                    visits.get() != stop
                })
                .unwrap_err();
            assert!(is_bounded_emission_cancelled(&error));
            assert_eq!(visits.get(), stop);
        }
    }
}

#[test]
fn invalid_id_and_overflow_keep_errors_and_poison_without_acceptance() {
    let mut writer = LratWriter::new_binary(Vec::new(), 2);
    let error = writer
        .add_with_id_bounded_prevalidated_rup_with_cancellation(3, &[], &[1], &|| {
            panic!("invalid reserved ID must be checked before polling")
        })
        .unwrap_err();
    assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
    assert!(!is_bounded_emission_cancelled(&error));
    assert!(writer.has_io_error());

    for hint in [u64::MAX, i64::MAX as u64 + 1] {
        let mut writer = LratWriter::new_binary(Vec::new(), 2);
        let error = writer
            .add_bounded_prevalidated_rup_with_cancellation(&[], &[hint], &|| true)
            .unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidInput);
        assert!(!is_bounded_emission_cancelled(&error));
        assert_eq!(writer.added_count(), 0);
        assert!(writer.has_io_error());
        assert!(!writer.get_ref().is_empty());
        assert!(writer.into_inner().is_err());
    }
}
