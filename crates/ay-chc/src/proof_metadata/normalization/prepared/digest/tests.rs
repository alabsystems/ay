// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::prepare_normalized_chc_input_with_work;
use super::*;
use crate::{ChcExpr, ChcSort, ClauseBody, HornClause};
use ay_core::original_query::{FiniteAdmissionGrant, OriginalAdmission, OriginalAdmissionError};
use ay_core::time::Instant;
use sha2::{Digest, Sha256};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};
use std::time::Duration;

mod cleanup;
mod resources;

fn owner_at(
    end: Instant,
    units: u64,
    bytes: usize,
    observer: ay_core::resource::CheckStop,
) -> OriginalAdmission {
    OriginalAdmission::new(FiniteAdmissionGrant::new(units, bytes), end, observer)
}

fn fixture() -> ChcProblem {
    let mut source = ChcProblem::new();
    source.set_fixedpoint_format();
    source.declare_predicate("P\n\"λ\\", vec![ChcSort::BitVec(64), ChcSort::Bool]);
    source.declare_action("step\r\n\t");
    source.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        false,
    ))));
    source
}

fn raw_hex(bytes: &[u8]) -> String {
    // Independent oracle/fixture preparation is not billed as production work.
    let mut accept = |_: usize, _: usize| Ok(());
    let mut work = WorkBudget::with_admission(u64::MAX, &mut accept);
    let digest = hash::run(bytes, &mut Borrowed(&mut work)).unwrap();
    let hex = hexadecimal(&digest, &mut Borrowed(&mut work)).unwrap();
    std::str::from_utf8(&hex).unwrap().to_string()
}

fn consume(
    original: &OriginalAdmission,
    source: &ChcProblem,
) -> Result<(), OriginalAdmissionError> {
    original.with_work(|work| {
        prepare_normalized_chc_input_with_work(source, work)?.with_sha256(
            |actual, bytes, hex, _| {
                assert!(std::ptr::eq(actual, source));
                assert_eq!(hex, format!("{:x}", Sha256::digest(bytes.as_bytes())));
                Ok(())
            },
        )
    })
}

fn totals(source: &ChcProblem) -> (u64, usize) {
    let (mut units, mut bytes) = (0u64, 0usize);
    let mut sink = |work: usize, storage: usize| {
        units = units.checked_add(work as u64).unwrap();
        bytes = bytes.checked_add(storage).unwrap();
        Ok(())
    };
    let mut work = WorkBudget::with_admission(u64::MAX, &mut sink);
    prepare_normalized_chc_input_with_work(source, &mut work)
        .unwrap()
        .with_sha256(|_, _, _, _| Ok(()))
        .unwrap();
    drop(work);
    (units, bytes)
}

#[test]
fn nist_example_vectors_and_empty_digest_match_exact_sha2() {
    // Official example: csrc.nist.gov/.../documents/examples/sha256.pdf.
    let cases: &[(&[u8], &str)] = &[
        (
            b"",
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855",
        ),
        (
            b"abc",
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad",
        ),
        (
            b"abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq",
            "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1",
        ),
    ];
    for (input, expected) in cases {
        assert_eq!(raw_hex(input), *expected);
        assert_eq!(raw_hex(input), format!("{:x}", Sha256::digest(input)));
    }
}

#[test]
fn every_padding_frontier_and_binary_byte_matches_sha2() {
    for length in [
        0, 1, 54, 55, 56, 57, 63, 64, 65, 119, 120, 127, 128, 129, 255, 256, 511,
    ] {
        let bytes: Vec<u8> = (0..length).map(|index| (index % 256) as u8).collect();
        assert_eq!(raw_hex(&bytes), format!("{:x}", Sha256::digest(&bytes)));
    }
}

#[test]
fn exact_canonical_bytes_and_consumer_line_normalizer_have_identical_digest() {
    let source = fixture();
    let original = owner_at(
        Instant::now() + Duration::from_secs(20),
        2_000_000,
        8 * 1024 * 1024,
        Arc::new(|| false),
    );
    original
        .with_work(|work| {
            prepare_normalized_chc_input_with_work(&source, work)?.with_sha256(
                |actual, bytes, hex, _| {
                    assert!(std::ptr::eq(actual, &source));
                    let normalized = consumer_normalize(bytes);
                    assert_eq!(bytes, normalized);
                    assert_eq!(hex, format!("{:x}", Sha256::digest(normalized.as_bytes())));
                    assert_eq!(hex, super::super::super::input_hash(&source));
                    Ok(())
                },
            )
        })
        .unwrap();
}

fn consumer_normalize(input: &str) -> String {
    // Exact current MODEL_CHECKER_CONSUMER evidence.rs normalizer; fixture-only unpriced copy.
    let normalized = input.replace("\r\n", "\n").replace('\r', "\n");
    let mut lines: Vec<&str> = normalized.lines().collect();
    while lines.last().is_some_and(|line| line.trim().is_empty()) {
        lines.pop();
    }
    let mut out = lines
        .into_iter()
        .map(str::trim_end)
        .collect::<Vec<_>>()
        .join("\n");
    out.push('\n');
    out
}

#[test]
fn block_round_offer_totals_match_the_closed_source_recurrence() {
    for length in [0, 1, 55, 56, 63, 64, 65, 120, 128, 256] {
        let input = vec![0u8; length];
        let (mut units, mut storage) = (0usize, 0usize);
        let mut sink = |work: usize, bytes: usize| {
            units += work;
            storage += bytes;
            Ok(())
        };
        let mut work = WorkBudget::with_admission(u64::MAX, &mut sink);
        super::consume(
            &ChcProblem::new(),
            std::str::from_utf8(&input).unwrap(),
            &mut work,
            |_, _, _, _| Ok(()),
        )
        .unwrap();
        drop(work);
        let (full, tail) = (length / 64, length % 64);
        let extra = usize::from(tail >= 56);
        assert_eq!(units, 36_160 + 30_304 * full + 24 * tail + 28_752 * extra);
        assert_eq!(storage, 2528 + 2400 * (full + extra));
    }
}

#[test]
fn oversized_bit_length_refuses_before_any_hash_state_or_payload() {
    if usize::BITS < 64 {
        return;
    }
    let mut checkpoint = || std::ops::ControlFlow::Continue(());
    let mut work = WorkBudget::new(1000, &mut checkpoint);
    let max_bytes = (u64::MAX / 8) as usize;
    assert_eq!(
        hash::bit_length(max_bytes, &mut Borrowed(&mut work)).unwrap(),
        (max_bytes as u64) * 8
    );
    assert_eq!(
        hash::bit_length(max_bytes + 1, &mut Borrowed(&mut work)),
        Err(QueryError::Exhausted)
    );
    assert_eq!(work.charge(0), Err(QueryError::Exhausted));
}
