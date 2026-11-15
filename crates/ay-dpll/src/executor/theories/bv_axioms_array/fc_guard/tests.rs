// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use ay_core::{Sort, Symbol, TermStore};
use num_bigint::BigInt;

mod oracle;

fn fixture() -> (TermStore, Vec<(TermId, TermId)>) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(4));
    let y = terms.mk_var("y", Sort::bitvec(4));
    let zero = terms.mk_bitvec(BigInt::from(0), 4);
    let alias = terms.mk_app(Symbol::named("bvadd"), [zero, zero], Sort::bitvec(4));
    let low_x = terms.mk_var("low-x", Sort::bitvec(2));
    let low_y = terms.mk_var("low-y", Sort::bitvec(2));
    let high_zero = terms.mk_bitvec(BigInt::from(0), 2);
    let padded_x = terms.mk_app(Symbol::named("concat"), [high_zero, low_x], Sort::bitvec(4));
    let padded_y = terms.mk_app(Symbol::named("concat"), [high_zero, low_y], Sort::bitvec(4));
    let negated = terms.mk_app(Symbol::named("bvnot"), [x], Sort::bitvec(4));
    (
        terms,
        vec![(x, y), (padded_x, padded_y), (zero, alias), (x, negated)],
    )
}

fn materialize<'a>(terms: &'a TermStore, pairs: &[(TermId, TermId)]) -> BvSolver<'a> {
    let mut bv = BvSolver::new(terms);
    for &(left, right) in pairs {
        assert!(bv.ensure_term_bits(left).is_some());
        assert!(bv.ensure_term_bits(right).is_some());
    }
    bv
}

fn result() -> ArrayAxiomResult {
    ArrayAxiomResult {
        clauses: vec![CnfClause::new(vec![7, -11])],
        // Guard emission never owns the producer's final aggregate accounting.
        num_vars: 77,
    }
}

#[test]
fn first_miss_matches_frozen_guard_emission_and_reverse_hit_adds_nothing() {
    let (terms, pairs) = fixture();
    let bv = materialize(&terms, &pairs);
    for &(left, right) in &pairs {
        for pair in [(left, right), (right, left)] {
            for offset in [0, 7] {
                let mut cache = IndexEqualityGuards::new(usize::MAX);
                let mut actual = result();
                let mut expected = result();
                let mut next = bv.num_vars() + offset + 19;
                let mut expected_next = next;
                let bits = (
                    bv.get_term_bits(pair.0).unwrap(),
                    bv.get_term_bits(pair.1).unwrap(),
                );
                let guard = cache.get_or_emit(pair, bits, &bv, offset, &mut next, &mut actual);
                let old = oracle::emit(bits, &bv, offset, &mut expected_next, &mut expected);
                assert_eq!(guard, old);
                assert_eq!(actual.clauses, expected.clauses);
                assert_eq!(next, expected_next);
                assert_eq!(actual.num_vars, expected.num_vars);
                assert_eq!(cache.completed.len(), 1);
                let hit = cache.get_or_emit(
                    (pair.1, pair.0),
                    (bits.1, bits.0),
                    &bv,
                    offset,
                    &mut next,
                    &mut actual,
                );
                assert_eq!(hit, guard);
                assert_eq!(actual.clauses, expected.clauses);
                assert_eq!(next, expected_next);
            }
        }
    }
}

#[test]
fn full_or_zero_retention_emits_uncached_definitions_without_losing_old_hits() {
    let (terms, pairs) = fixture();
    let bv = materialize(&terms, &pairs);
    for limit in [0, 1] {
        let mut cache = IndexEqualityGuards::new(limit);
        let mut actual = result();
        let mut expected = result();
        let mut next = bv.num_vars() + 19;
        let mut expected_next = next;
        let mut first_guard = None;
        for pair in [pairs[0], pairs[2], (pairs[0].1, pairs[0].0), pairs[2]] {
            let bits = (
                bv.get_term_bits(pair.0).unwrap(),
                bv.get_term_bits(pair.1).unwrap(),
            );
            let guard = cache.get_or_emit(pair, bits, &bv, 0, &mut next, &mut actual);
            if pair == (pairs[0].1, pairs[0].0) && limit == 1 {
                assert_eq!(Some(guard), first_guard);
            } else {
                assert_eq!(
                    guard,
                    oracle::emit(bits, &bv, 0, &mut expected_next, &mut expected)
                );
            }
            if pair == pairs[0] {
                first_guard = Some(guard);
            }
            assert_eq!(actual.clauses, expected.clauses);
            assert_eq!(next, expected_next);
            assert!(cache.completed.len() <= limit);
        }
    }
}

#[test]
fn distinct_exact_pairs_get_separate_completed_definitions() {
    let (terms, pairs) = fixture();
    let bv = materialize(&terms, &pairs);
    let mut cache = IndexEqualityGuards::new(pairs.len());
    let mut actual = result();
    let mut expected = result();
    let mut next = bv.num_vars() + 19;
    let mut expected_next = next;
    for (count, &pair) in pairs.iter().enumerate() {
        let bits = (
            bv.get_term_bits(pair.0).unwrap(),
            bv.get_term_bits(pair.1).unwrap(),
        );
        let guard = cache.get_or_emit(pair, bits, &bv, 0, &mut next, &mut actual);
        assert_eq!(
            guard,
            oracle::emit(bits, &bv, 0, &mut expected_next, &mut expected)
        );
        assert_eq!(cache.completed.len(), count + 1);
        assert_eq!(actual.clauses, expected.clauses);
        assert_eq!(next, expected_next);
    }
}
