// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

fn decode(
    bytes: &[u8],
    limits: &ResolutionProofLimits,
    control: &ProofControl<'_>,
) -> Result<ResolutionDag, ResolutionProofError> {
    let clauses = [vec![positive(0)], vec![negative(0)]];
    let mut meter = CodecMeter::new(
        bytes.len(),
        limits.max_codec_bytes,
        limits.deadline,
        control,
    )?;
    meter.charge(
        size_of::<ResolutionDag>(),
        ResolutionProofResource::CodecBytes,
    )?;
    let originals = clone_originals_bounded(&clauses, &mut meter, limits.deadline)?;
    parse_binary_lrat_into_dag(1, originals, bytes, limits, &mut meter)
}

#[test]
fn binary_decode_and_cloning_refuse_every_poll_without_a_partial_dag() {
    // id 3 derives p from original 1; a deletion is deliberately discarded;
    // id 4 derives the empty clause from id 3 and original 2.
    let bytes = [b'a', 6, 2, 0, 2, 0, b'd', 2, 0, b'a', 8, 0, 6, 4, 0];
    let limits = limits();
    every_poll(|control| decode(&bytes, &limits, control));
    let mut progress = || true;
    let dag = decode(&bytes, &limits, &ProofControl::new(&mut progress)).unwrap();
    assert_eq!(
        dag.original_clauses,
        vec![(1, vec![positive(0)]), (2, vec![negative(0)])]
    );
    assert_eq!(
        dag.derived,
        vec![
            RupStep {
                id: 3,
                clause: vec![positive(0)],
                rup_hints: vec![1]
            },
            RupStep {
                id: 4,
                clause: vec![],
                rup_hints: vec![3, 2]
            },
        ]
    );
    assert_eq!(dag.empty_clause_id, 4);
    assert_eq!(dag.validate(), Ok(()));
}

#[test]
fn malformed_binary_errors_keep_exact_payload_while_live() {
    let limits = limits();
    let cases = [
        (
            vec![b'x'],
            ResolutionProofError::MalformedBinaryProof {
                offset: 0,
                detail: "unknown LRAT record marker",
            },
        ),
        (
            vec![b'a'],
            ResolutionProofError::MalformedBinaryProof {
                offset: 1,
                detail: "truncated variable-length integer",
            },
        ),
        (
            vec![b'a', 6, 0, 3, 0],
            ResolutionProofError::RatStepUnsupported,
        ),
        (
            vec![b'a', 6, 2, 0, 2, 0],
            ResolutionProofError::NoEmptyClause,
        ),
    ];
    for (bytes, expected) in cases {
        every_poll(|control| decode(&bytes, &limits, control));
        let mut progress = || true;
        assert_eq!(
            decode(&bytes, &limits, &ProofControl::new(&mut progress)),
            Err(expected)
        );
    }
}

#[test]
fn varint_boundaries_and_codec_refusal_preserve_existing_limits() {
    let limits = limits();
    for bytes in [vec![0], vec![0x80, 1], vec![0xff; 10], vec![0x80]] {
        every_poll(|control| {
            let mut position = 0;
            read_binary_value(&bytes, &mut position, limits.deadline, control)
        });
    }
    let mut progress = || true;
    let control = ProofControl::new(&mut progress);
    assert!(matches!(
        CodecMeter::new(1, 0, limits.deadline, &control),
        Err(ResolutionProofError::LimitExceeded {
            resource: ResolutionProofResource::CodecBytes,
            limit: 0,
            actual: 1
        })
    ));
    let mut cancelled = || false;
    assert!(matches!(
        CodecMeter::new(1, 0, limits.deadline, &ProofControl::new(&mut cancelled)),
        Err(ResolutionProofError::Cancelled)
    ));
}

#[test]
fn original_identity_walk_rejects_reordering_ids_and_literal_mutations() {
    let limits = limits();
    let bytes = [b'a', 6, 0, 2, 4, 0];
    let mut progress = || true;
    let dag = decode(&bytes, &limits, &ProofControl::new(&mut progress)).unwrap();
    let source = vec![vec![positive(0)], vec![negative(0)]];
    every_poll(|control| check_originals_controlled(&dag, &source, limits.deadline, control));
    for mutation in 0..4 {
        let mut changed = dag.clone();
        match mutation {
            0 => {
                changed.original_clauses.pop();
            }
            1 => changed.original_clauses.swap(0, 1),
            2 => changed.original_clauses[0].0 = 7,
            _ => changed.original_clauses[0].1[0] = negative(0),
        }
        every_poll(|control| {
            check_originals_controlled(&changed, &source, limits.deadline, control)
        });
        assert!(matches!(
            check_originals_controlled(
                &changed,
                &source,
                limits.deadline,
                &ProofControl::new(&mut || true)
            ),
            Err(ResolutionProofError::OriginalClauseMismatch { .. })
        ));
    }
}
