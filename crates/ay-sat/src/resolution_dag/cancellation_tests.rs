// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use crate::literal::Variable;
use std::time::Duration;

mod codec;
mod finalization;
mod literal_walk;
mod producer;
mod replay;

fn limits() -> ResolutionProofLimits {
    ResolutionProofLimits {
        deadline: Some(Instant::now() + Duration::from_secs(30)),
        ..ResolutionProofLimits::default()
    }
}

fn positive(index: u32) -> Literal {
    Literal::positive(Variable::new(index))
}
fn negative(index: u32) -> Literal {
    Literal::negative(Variable::new(index))
}

fn every_poll<T: std::fmt::Debug + PartialEq>(
    mut operation: impl FnMut(&ProofControl<'_>) -> Result<T, ResolutionProofError>,
) {
    let mut total = 0;
    let expected = {
        let mut progress = || {
            total += 1;
            true
        };
        ProofControl::new(&mut progress).run(&mut operation)
    };
    assert!(
        total > 0 && total < 20_000,
        "bounded fixture callback count: {total}"
    );
    for stop in 1..=total {
        let mut calls = 0;
        let actual = {
            let mut progress = || {
                calls += 1;
                calls != stop
            };
            ProofControl::new(&mut progress).run(&mut operation)
        };
        assert_eq!(
            actual,
            Err(ResolutionProofError::Cancelled),
            "callback {stop}/{total}"
        );
        assert_eq!(calls, stop, "a refused callback must never be retried");
    }
    let mut progress = || true;
    assert_eq!(ProofControl::new(&mut progress).run(operation), expected);
}

#[test]
fn input_walks_poll_duplicate_edges_and_preserve_exact_source_errors() {
    let limits = limits();
    for clauses in [
        vec![vec![positive(0), negative(0)]; 12],
        vec![vec![positive(0), positive(0)]],
        vec![vec![positive(2)]],
    ] {
        let expected = preflight_input(2, &clauses, &limits);
        every_poll(|control| {
            let result = preflight_input_controlled(2, &clauses, &limits, control);
            if !matches!(result, Err(ResolutionProofError::Cancelled)) {
                assert_eq!(result, expected);
            }
            result
        });
    }
}

#[test]
fn source_byte_censuses_share_control_without_changing_accounting() {
    let limits = limits();
    let clauses = vec![vec![positive(0), negative(1)]; 16];
    let logical_expected = clauses.len() * size_of::<Vec<Literal>>() + 32 * size_of::<Literal>();
    let codec_expected = size_of::<ResolutionDag>()
        + clauses.len() * size_of::<(u64, Vec<Literal>)>()
        + 32 * size_of::<Literal>();
    every_poll(|control| logical_input_bytes(&clauses, limits.deadline, control));
    every_poll(|control| original_codec_reservation(&clauses, limits.deadline, control));
    let mut progress = || true;
    let control = ProofControl::new(&mut progress);
    assert_eq!(
        logical_input_bytes(&clauses, limits.deadline, &control),
        Ok(logical_expected)
    );
    assert_eq!(
        original_codec_reservation(&clauses, limits.deadline, &control),
        Ok(codec_expected)
    );
}
