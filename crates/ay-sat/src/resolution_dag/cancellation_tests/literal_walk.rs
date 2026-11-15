// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::resolution_dag::literal_walk::{append, compare};

fn long_clause() -> Vec<Literal> {
    (0..1_025).map(positive).collect()
}

#[test]
fn copying_a_single_long_clause_polls_within_the_copy_and_preserves_capacity() {
    let source = long_clause();
    every_poll(|control| {
        let mut target = Vec::with_capacity(source.len());
        let capacity = target.capacity();
        let result = append(
            &mut target,
            &source,
            limits().deadline,
            ResolutionProofPhase::Solve,
            control,
        );
        assert_eq!(target.capacity(), capacity);
        assert_eq!(target, source[..target.len()]);
        result.map(|()| target)
    });
    let mut target = Vec::with_capacity(source.len());
    let mut calls = 0;
    assert_eq!(
        append(
            &mut target,
            &source,
            limits().deadline,
            ResolutionProofPhase::Solve,
            &ProofControl::new(&mut || {
                calls += 1;
                calls != 3
            }),
        ),
        Err(ResolutionProofError::Cancelled)
    );
    assert_eq!(target, source[..512]);
    assert_eq!(calls, 3);
}

#[test]
fn original_snapshot_copy_keeps_exact_identity_and_codec_byte_charges() {
    let source = vec![long_clause(), vec![], vec![negative(0)]];
    let expected: Vec<_> = source
        .iter()
        .enumerate()
        .map(|(index, clause)| (index as u64 + 1, clause.clone()))
        .collect();
    every_poll(|control| {
        let limits = limits();
        let mut meter = CodecMeter::new(0, limits.max_codec_bytes, limits.deadline, control)?;
        let copy = clone_originals_bounded(&source, &mut meter, limits.deadline)?;
        let bytes = copy.capacity() * size_of::<(u64, Vec<Literal>)>()
            + copy
                .iter()
                .map(|(_, clause)| clause.capacity() * size_of::<Literal>())
                .sum::<usize>();
        assert_eq!(meter.used, bytes);
        assert_eq!(copy, expected);
        Ok(copy)
    });
}

#[test]
fn original_comparison_polls_inside_a_clause_and_keeps_exact_error_precedence() {
    let source = long_clause();
    every_poll(|control| compare(&source, &source, 7, limits().deadline, control));
    for index in [0, 255, 256, 1_024] {
        let mut changed = source.clone();
        changed[index] = negative(index as u32);
        let mut calls = 0;
        let result = compare(
            &changed,
            &source,
            7,
            limits().deadline,
            &ProofControl::new(&mut || {
                calls += 1;
                calls <= index / 256 + 1
            }),
        );
        assert_eq!(
            result,
            Err(ResolutionProofError::OriginalClauseMismatch { index: 7 })
        );
        assert_eq!(calls, index / 256 + 1, "no new post-error callback");
    }
    let mut calls = 0;
    assert_eq!(
        compare(
            &source,
            &source,
            7,
            limits().deadline,
            &ProofControl::new(&mut || {
                calls += 1;
                calls != 3
            }),
        ),
        Err(ResolutionProofError::Cancelled)
    );
    assert_eq!(calls, 3);
}

#[test]
fn original_literal_walks_keep_the_absolute_deadline_and_refuse_empty_success() {
    let expired = Some(Instant::now());
    let mut target = Vec::with_capacity(1);
    let mut keep_going = || true;
    let live = ProofControl::new(&mut keep_going);
    assert_eq!(
        append(
            &mut target,
            &[positive(0)],
            expired,
            ResolutionProofPhase::Solve,
            &live
        ),
        Err(ResolutionProofError::DeadlineExceeded {
            phase: ResolutionProofPhase::Solve
        })
    );
    assert!(target.is_empty());
    assert_eq!(
        compare(&[], &[], 0, expired, &live),
        Err(ResolutionProofError::DeadlineExceeded {
            phase: ResolutionProofPhase::Parse
        })
    );
    assert_eq!(
        append(
            &mut target,
            &[],
            limits().deadline,
            ResolutionProofPhase::Parse,
            &ProofControl::new(&mut || false),
        ),
        Err(ResolutionProofError::Cancelled)
    );
}
