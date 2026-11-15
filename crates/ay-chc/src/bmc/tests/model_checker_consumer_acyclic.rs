// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source-bound, exact-path coverage for MODEL_CHECKER_CONSUMER's retained `dyn_struct` reducer.

#![cfg(test)]

use super::*;
use crate::pdr::Counterexample;
use num_bigint::BigUint;

mod fixtures;
mod replay;

use fixtures::{high_half_source, run_exact, ORIGINAL, WORD};

#[test]
fn retained_dyn_struct_keeps_array_and_wide_word_in_the_original_fact() {
    let problem = ChcParser::parse(ORIGINAL).expect("retained source parses");
    problem.validate().expect("retained source is well typed");
    assert!(!problem.has_cycles());
    assert_eq!(problem.predicates().len(), 2);
    assert_eq!(problem.clauses().len(), 3);
    let fact = &problem.clauses()[0];
    assert!(fact.body.predicates.is_empty());
    assert_eq!(fact.vars().len(), 3);
    let variables = fact.vars();
    let array_sort = ChcSort::Array(Box::new(ChcSort::BitVec(32)), Box::new(ChcSort::Bool));
    for name in ["obj_valid", "obj_valid__out"] {
        assert!(variables
            .iter()
            .any(|var| var.name == name && var.sort == array_sort));
    }
    assert!(variables
        .iter()
        .any(|var| var.name == WORD && var.sort == ChcSort::BitVec(256)));
    assert_eq!(problem.clauses()[1].body.predicates.len(), 1);
    assert_eq!(problem.clauses()[2].body.predicates.len(), 1);
    assert!(problem.clauses()[2].head.is_query());
}

#[test]
#[timeout(30_000)]
fn retained_dyn_struct_exact_bmc_replays_original_array_and_bv256_witness() {
    let (problem, counterexample) = run_exact(ORIGINAL);
    replay::check_original_and_mutations(ORIGINAL, &problem, &counterexample, &BigUint::from(1_u8));
}

#[test]
#[timeout(30_000)]
fn metamorphic_dyn_struct_high_half_cannot_be_truncated_to_u128() {
    // This is an intentional source mutation, NOT a claim that the retained
    // upstream reducer has a nonzero high half.
    let source = high_half_source();
    let expected = (BigUint::from(1_u8) << 128_u32) + 1_u8;
    let (problem, counterexample) = run_exact(&source);
    replay::check_original_and_mutations(&source, &problem, &counterexample, &expected);
}
