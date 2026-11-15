// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::time::Instant;
use std::time::Duration;

fn limits() -> ResolutionProofLimits {
    ResolutionProofLimits {
        deadline: Some(Instant::now() + Duration::from_secs(30)),
        ..ResolutionProofLimits::default()
    }
}

fn literal(dimacs: i32) -> Literal {
    Literal::from_dimacs(dimacs)
}

/// The pass the map-per-clause preflight made, verbatim apart from its
/// clock: the reference every scanned clause must agree with.
fn map_reference(
    num_vars: usize,
    input_bytes: usize,
    limits: &ResolutionProofLimits,
    clause_index: usize,
    clause: &[Literal],
) -> Result<(), ResolutionProofError> {
    let overflow = || ResolutionProofError::AccountingOverflow {
        resource: ResolutionProofResource::InputBytes,
    };
    let requested = input_bytes
        .checked_add(clause.len().checked_mul(32).ok_or_else(overflow)?)
        .ok_or_else(overflow)?;
    enforce_proof_limit(
        ResolutionProofResource::InputBytes,
        requested,
        limits.max_input_bytes,
    )?;
    let mut seen = HashMap::<u32, usize>::new();
    seen.try_reserve(clause.len())
        .map_err(|_| ResolutionProofError::AllocationFailed {
            resource: ResolutionProofResource::InputLiterals,
        })?;
    let peak = input_bytes
        .checked_add(seen.capacity().checked_mul(32).ok_or_else(overflow)?)
        .ok_or_else(overflow)?;
    enforce_proof_limit(
        ResolutionProofResource::InputBytes,
        peak,
        limits.max_input_bytes,
    )?;
    for (literal_index, literal) in clause.iter().enumerate() {
        let var = literal.variable().index();
        if var >= num_vars {
            return Err(ResolutionProofError::InputLiteralOutOfRange {
                clause_index,
                literal_index,
                var,
                num_vars,
            });
        }
        if let Some(first_index) = seen.insert(literal.raw(), literal_index) {
            return Err(ResolutionProofError::DuplicateInputLiteral {
                clause_index,
                literal_index,
                first_index,
            });
        }
    }
    Ok(())
}

fn checked(
    num_vars: usize,
    input_bytes: usize,
    limits: &ResolutionProofLimits,
    clauses: &[Vec<Literal>],
) -> (Vec<Result<(), ResolutionProofError>>, usize, usize) {
    let mut polls = 0;
    let (results, reads) = {
        let mut progress = || {
            polls += 1;
            true
        };
        let control = ProofControl::new(&mut progress);
        let mut pass = ClauseLiterals::new(num_vars, input_bytes, limits, &control);
        let results = clauses
            .iter()
            .enumerate()
            .map(|(index, clause)| pass.check(index, clause))
            .collect();
        (results, pass.clock_reads)
    };
    (results, polls, reads)
}

/// Clauses on both sides of the scan's length bound, with a repeat (same
/// sign or both signs of one variable) at every position pair, and without.
fn clauses_around_the_scan_bound() -> Vec<Vec<Literal>> {
    let mut clauses = Vec::new();
    for len in 0..=SCANNED_LITERALS + 8 {
        let distinct: Vec<Literal> = (1..=i32::try_from(len).unwrap()).map(literal).collect();
        clauses.push(distinct.clone());
        let mut flipped = distinct.clone();
        if let Some(last) = flipped.last_mut() {
            *last = last.negated();
        }
        clauses.push(flipped);
        for first in 0..len {
            for repeat in first + 1..len {
                // Both signs of one variable are not a repeat.
                let mut complementary = distinct.clone();
                complementary[repeat] = complementary[first].negated();
                clauses.push(complementary);
                let mut repeated = distinct.clone();
                repeated[repeat] = repeated[first];
                clauses.push(repeated.clone());
                // A later repeat of an earlier literal does not hide the first.
                if repeat + 1 < len {
                    repeated[repeat + 1] = repeated[first];
                    clauses.push(repeated);
                }
            }
        }
    }
    clauses
}

#[test]
fn every_clause_is_refused_or_admitted_exactly_as_the_map_did() {
    let limits = limits();
    let clauses = clauses_around_the_scan_bound();
    let num_vars = SCANNED_LITERALS + 8;
    let (results, _, _) = checked(num_vars, 4096, &limits, &clauses);
    let mut refused = [0usize; 2];
    for (index, (clause, result)) in clauses.iter().zip(&results).enumerate() {
        let expected = map_reference(num_vars, 4096, &limits, index, clause);
        assert_eq!(result, &expected, "clause {index}: {clause:?}");
        refused[usize::from(clause.len() > SCANNED_LITERALS)] += usize::from(result.is_err());
    }
    assert!(
        refused.iter().all(|&n| n > 0),
        "both the scan and the map refuse repeats: {refused:?}"
    );
    // A literal out of range is refused before its repeat is looked for.
    let (results, _, _) = checked(2, 4096, &limits, &[vec![literal(1), literal(3)]]);
    assert_eq!(
        results[0],
        Err(ResolutionProofError::InputLiteralOutOfRange {
            clause_index: 0,
            literal_index: 1,
            var: 2,
            num_vars: 2,
        })
    );
}

/// The scratch a scanned clause is charged for is a fresh map's capacity for
/// its length: an input that fits it is admitted and one byte less refused,
/// at every length, as with the map.
#[test]
fn a_scanned_clause_is_charged_a_fresh_maps_scratch() {
    let input_bytes = 4096;
    for len in 0..=SCANNED_LITERALS + 4 {
        let mut map = HashMap::<u32, usize>::new();
        map.try_reserve(len).expect("small reservation");
        let fits = input_bytes + map.capacity() * SLOT_BYTES;
        let clause: Vec<Literal> = (1..=i32::try_from(len).unwrap()).map(literal).collect();
        for (max_input_bytes, admitted) in [(fits, true), (fits - 1, false)] {
            let limits = ResolutionProofLimits {
                max_input_bytes,
                ..limits()
            };
            // The second clause of a length is charged from the pass's
            // memo, and must be charged exactly as the first.
            let twice = [clause.clone(), clause.clone()];
            let (results, _, _) = checked(len, input_bytes, &limits, &twice);
            for (index, result) in results.iter().enumerate() {
                let expected = map_reference(len, input_bytes, &limits, index, &clause);
                assert_eq!(
                    result, &expected,
                    "len {len}, limit {max_input_bytes}, clause {index}"
                );
                assert_eq!(
                    result.is_ok(),
                    admitted,
                    "len {len}, clause {index}: {result:?}"
                );
            }
        }
    }
}

/// REGRESSION (qb44). The clock is read once per 1,024 clauses and once per
/// 1,024 literals of the whole input, and every poll is where it was: two
/// per clause and one per literal. The map-per-clause pass read the clock at
/// every clause's first literal: 8,200 reads here, not 24.
#[test]
fn the_clock_is_read_per_1024_literals_of_the_input_not_per_clause() {
    let limits = limits();
    let clauses: Vec<Vec<Literal>> = (0..8192)
        .map(|index| vec![literal(index % 64 + 1), literal(-(index % 64 + 65))])
        .collect();
    let (results, polls, reads) = checked(128, 4096, &limits, &clauses);
    assert!(results.iter().all(Result::is_ok));
    assert_eq!(polls, 2 * 8192 + 2 * 8192);
    assert_eq!(reads, 8192 / 1024 + 2 * 8192 / 1024);
}

/// REGRESSION (qb44). A clause of at most `SCANNED_LITERALS` literals builds
/// no map of its own: a pass builds one per short length it meets, to read
/// its capacity, and one per longer clause. The map-per-clause pass built
/// one for every clause: 4,099 here, not 4.
#[test]
fn short_clauses_build_one_map_per_length_not_one_per_clause() {
    let limits = limits();
    let long: Vec<Literal> = (1..=i32::try_from(SCANNED_LITERALS + 1).unwrap())
        .map(literal)
        .collect();
    let mut clauses: Vec<Vec<Literal>> = (0..4096)
        .map(|index| vec![literal(index % 8 + 1), literal(-(index % 8 + 9))])
        .collect();
    clauses.push(vec![literal(1)]);
    clauses.push(long.clone());
    clauses.push(long);
    let mut progress = || true;
    let control = ProofControl::new(&mut progress);
    let mut pass = ClauseLiterals::new(SCANNED_LITERALS + 1, 4096, &limits, &control);
    for (index, clause) in clauses.iter().enumerate() {
        assert_eq!(pass.check(index, clause), Ok(()), "clause {index}");
    }
    assert_eq!(
        pass.maps_built,
        2 + 2,
        "two short lengths, two long clauses"
    );
}

/// A deadline that has passed stops the pass at its first clause, and one
/// that passes inside a long clause is seen within 1,024 of its literals.
#[test]
fn a_passed_deadline_still_stops_the_pass() {
    let passed = ResolutionProofLimits {
        deadline: Some(Instant::now()),
        ..limits()
    };
    let (results, polls, reads) = checked(4, 4096, &passed, &[vec![literal(1)]]);
    let deadline = Err(ResolutionProofError::DeadlineExceeded {
        phase: ResolutionProofPhase::Preflight,
    });
    assert_eq!(results[0], deadline);
    assert_eq!((polls, reads), (1, 1), "refused at the first read");
    let long: Vec<Literal> = (1..=3000).map(literal).collect();
    let mut progress = || true;
    let control = ProofControl::new(&mut progress);
    let mut pass = ClauseLiterals::new(3000, 4096, &passed, &control);
    pass.walked = 1;
    let refused = pass.check(1, &long);
    let read_at = pass.walked;
    assert_eq!(refused, deadline);
    assert_eq!(read_at, 1024, "seen at the 1,024th literal of the input");
}
