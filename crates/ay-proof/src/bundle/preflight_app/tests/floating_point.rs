// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod arithmetic;
mod conversions;
mod ownership;

fn rounding() -> Sort {
    Sort::Uninterpreted("RoundingMode".into())
}

fn fp_entries() -> Vec<(TermData, Sort)> {
    [
        rounding(),
        Sort::FloatingPoint(8, 24),
        Sort::FloatingPoint(11, 53),
        Sort::Bool,
        Sort::Int,
        Sort::Real,
        bv(32),
        bv(8),
        Sort::Uninterpreted("NotRoundingMode".into()),
    ]
    .into_iter()
    .enumerate()
    .map(|(index, sort)| (TermData::Var(format!("fp_arg_{index}"), index as u32), sort))
    .collect()
}

fn ids(indices: &[u32]) -> Vec<TermId> {
    indices.iter().copied().map(TermId).collect()
}

fn positive(symbol: Symbol, args: &[u32], result: Sort) {
    run(&fp_entries(), &symbol, &ids(args), &result).expect("valid native FP signature");
}

fn negative(symbol: Symbol, args: &[u32], result: Sort) {
    assert!(
        matches!(
            run(&fp_entries(), &symbol, &ids(args), &result),
            Err(ProofCheckError::MalformedProofBundle { .. })
        ),
        "malformed {symbol:?}, {args:?}, {result:?}"
    );
}
