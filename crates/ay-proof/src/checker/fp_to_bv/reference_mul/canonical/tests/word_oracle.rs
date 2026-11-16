// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Finite independent regression oracles, never production semantic authority.

use super::*;
use ay_core::original_query::{QueryError, StopReason};

#[derive(Clone, Copy)]
enum Outcome {
    Unsatisfiable,
    Satisfiable,
}

#[derive(Clone, Copy)]
enum OracleValue {
    Word(u64),
    Boolean(bool),
}

impl OracleValue {
    fn changed(self) -> Self {
        match self {
            Self::Word(value) => Self::Word(value ^ 1),
            Self::Boolean(value) => Self::Boolean(!value),
        }
    }
}

fn request(end: Instant) -> ResolutionProofLimits {
    let mut limits = ResolutionProofLimits {
        deadline: Some(end),
        max_num_vars: 512,
        max_input_clauses: 4096,
        max_input_literals: 12_288,
        max_input_clause_literals: 16,
        max_input_bytes: 1_048_576,
        max_conflicts: Some(4096),
        max_decisions: Some(8192),
        solver_clause_db_reduction_threshold_bytes: 1_048_576,
        max_proof_output_bytes: 1_048_576,
        max_derived_steps: 4096,
        max_derived_literals: 12_288,
        max_hints: 32_768,
        max_pending_deletions: 4096,
        max_codec_bytes: 1_048_576,
        max_backward_reconstruction_bytes: 1_048_576,
        ..ResolutionProofLimits::default()
    };
    limits.validation.deadline = Some(end);
    limits.validation.max_original_clauses = 4096;
    limits.validation.max_original_literals = 12_288;
    limits.validation.max_derived_steps = 4096;
    limits.validation.max_derived_literals = 12_288;
    limits.validation.max_hints = 32_768;
    limits.validation.max_work = 100_000;
    limits.validation.max_bytes = 1_048_576;
    limits
}

fn check_query(terms: &TermStore, roots: &[TermId], outcome: Outcome) {
    let end = Instant::now() + Duration::from_secs(30);
    let limits = request(end);
    let mut remaining_work = 2_000_000u64;
    let mut remaining_bytes = 16_777_216usize;
    let mut stopped = None;
    let mut admission = |units: usize, bytes: usize| {
        if let Some(error) = stopped {
            return Err(error);
        }
        // Prelatch before owner observations; no caught refusal/panic can retry.
        stopped = Some(QueryError::Exhausted);
        if Instant::now() >= end {
            let error = QueryError::Interrupted(StopReason::Deadline);
            stopped = Some(error);
            return Err(error);
        }
        let units = u64::try_from(units).map_err(|_| QueryError::Exhausted)?;
        let next_work = remaining_work
            .checked_sub(units)
            .ok_or(QueryError::Exhausted)?;
        let next_bytes = remaining_bytes
            .checked_sub(bytes)
            .ok_or(QueryError::Exhausted)?;
        remaining_work = next_work;
        remaining_bytes = next_bytes;
        stopped = None;
        Ok(())
    };
    let mut work = WorkBudget::with_admission(2_000_000, &mut admission);
    match outcome {
        Outcome::Unsatisfiable => {
            let mut proof = capture(terms, roots, &limits, &mut work)
                .expect("independent expected value must refute its negation");
            proof
                .replay()
                .expect("same original owner rederives every CNF row");
        }
        Outcome::Satisfiable => {
            assert!(
                matches!(
                    capture(terms, roots, &limits, &mut work),
                    Err(Error::Search(ay_sat::ResolutionProofError::Satisfiable))
                ),
                "a changed independent value must not gain a refutation"
            );
        }
    }
}

fn check_pair(name: &str, a: u64, b: u64, value: OracleValue) {
    for (expected, outcome) in [
        (value, Outcome::Unsatisfiable),
        (value.changed(), Outcome::Satisfiable),
    ] {
        let mut terms = TermStore::new();
        let a = literal(&mut terms, a, 3);
        let b = literal(&mut terms, b, 3);
        let (sort, expected) = match expected {
            OracleValue::Word(word) => (Sort::bitvec(3), literal(&mut terms, word, 3)),
            OracleValue::Boolean(value) => (Sort::Bool, terms.mk_bool(value)),
        };
        // mk_app preserves the unsimplified source operation; no producer eval.
        let actual = app(&mut terms, name, &[a, b], sort);
        let root = opposite_equal(&mut terms, actual, expected);
        check_query(&terms, &[root], outcome);
    }
}

#[test]
fn modular_add_sub_mul_match_all_three_bit_constant_pairs() {
    for a in 0u64..8 {
        for b in 0u64..8 {
            for (name, expected) in [
                ("bvadd", (a + b) & 7),
                ("bvsub", a.wrapping_sub(b) & 7),
                ("bvmul", (a * b) & 7),
            ] {
                check_pair(name, a, b, OracleValue::Word(expected));
            }
        }
    }
}

#[test]
fn bitwise_and_or_xor_match_all_three_bit_constant_pairs() {
    for a in 0u64..8 {
        for b in 0u64..8 {
            for (name, expected) in [("bvand", a & b), ("bvor", a | b), ("bvxor", a ^ b)] {
                check_pair(name, a, b, OracleValue::Word(expected));
            }
        }
    }
}

#[test]
fn unsigned_less_matches_all_three_bit_constant_pairs() {
    for a in 0u64..8 {
        for b in 0u64..8 {
            check_pair("bvult", a, b, OracleValue::Boolean(a < b));
        }
    }
}

#[test]
fn logical_shifts_match_all_three_bit_values_and_saturate_at_width() {
    for a in 0u64..8 {
        for shift in 0u64..8 {
            let left = if shift >= 3 { 0 } else { (a << shift) & 7 };
            let right = if shift >= 3 { 0 } else { a >> shift };
            check_pair("bvshl", a, shift, OracleValue::Word(left));
            check_pair("bvlshr", a, shift, OracleValue::Word(right));
        }
    }
}

fn rebuild_word(terms: &mut TermStore, word: TermId) -> (TermId, TermId) {
    let high = terms.mk_app(
        Symbol::indexed("extract", vec![3, 2]),
        [word],
        Sort::bitvec(2),
    );
    let low = terms.mk_app(
        Symbol::indexed("extract", vec![1, 0]),
        [word],
        Sort::bitvec(2),
    );
    (high, low)
}

#[test]
fn nonreflexive_extract_concat_to_fp_preserves_the_actual_raw_word() {
    let mut terms = TermStore::new();
    let word = terms.mk_var("original_word", Sort::bitvec(4));
    let (high, low) = rebuild_word(&mut terms, word);
    let joined = app(&mut terms, "concat", &[high, low], Sort::bitvec(4));
    assert_ne!(joined, word, "different actual source occurrences");
    let original = raw(&mut terms, word, 2, 2);
    let rebuilt = raw(&mut terms, joined, 2, 2);
    assert_ne!(original, rebuilt, "not a reflexive equality shortcut");
    let root = opposite_equal(&mut terms, original, rebuilt);
    check_query(&terms, &[root], Outcome::Unsatisfiable);
}

#[test]
fn changed_extract_concat_to_fp_is_satisfiable_at_the_original_zero_word() {
    let mut terms = TermStore::new();
    let word = terms.mk_var("original_word", Sort::bitvec(4));
    let (high, low) = rebuild_word(&mut terms, word);
    let one = literal(&mut terms, 1, 2);
    let changed = app(&mut terms, "bvxor", &[low, one], Sort::bitvec(2));
    let joined = app(&mut terms, "concat", &[high, changed], Sort::bitvec(4));
    let original = raw(&mut terms, word, 2, 2);
    let rebuilt = raw(&mut terms, joined, 2, 2);
    let zero = literal(&mut terms, 0, 4);
    let pin_original = app(&mut terms, "=", &[word, zero], Sort::Bool);
    let unequal = opposite_equal(&mut terms, original, rebuilt);
    // Source bits 0000 and 0001 are +zero and a subnormal, not two NaNs.
    check_query(&terms, &[pin_original, unequal], Outcome::Satisfiable);
}
