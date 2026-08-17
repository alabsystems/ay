// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;

use super::discharge_trust_clause;

struct SeqCarrierFixture {
    terms: TermStore,
    assertions: Vec<TermId>,
    range_units: Vec<TermId>,
    left_conflict: Vec<TermId>,
    right_conflict: Vec<TermId>,
}

fn seq_carrier_fixture(width: u32) -> SeqCarrierFixture {
    let mut terms = TermStore::new();
    let len_a = terms.mk_var("source_replay_len_a", Sort::Int);
    let len_b = terms.mk_var("source_replay_len_b", Sort::Int);
    let idx_a = terms.mk_var("source_replay_idx_a", Sort::bitvec(width));
    let idx_b = terms.mk_var("source_replay_idx_b", Sort::bitvec(width));
    let nat_a = terms.mk_bv2nat(idx_a);
    let nat_b = terms.mk_bv2nat(idx_b);
    let zero = terms.mk_int(BigInt::from(0_u8));
    let max = terms.mk_int((BigInt::from(1_u8) << width) - BigInt::from(1_u8));

    let len_a_lower = terms.mk_le(zero, len_a);
    let len_b_lower = terms.mk_le(zero, len_b);
    let nat_a_lower = terms.mk_le(zero, nat_a);
    let nat_b_lower = terms.mk_le(zero, nat_b);
    let nat_a_upper = terms.mk_le(nat_a, max);
    let nat_b_upper = terms.mk_le(nat_b, max);
    let len_a_upper = terms.mk_le(len_a, max);
    let len_b_upper = terms.mk_le(len_b, max);
    let not_len_a_lower = terms.mk_not_raw(len_a_lower);
    let not_len_b_lower = terms.mk_not_raw(len_b_lower);
    let pin_a_eq = terms.mk_eq(len_a, nat_a);
    let pin_b_eq = terms.mk_eq(len_b, nat_b);
    let pin_a = terms.mk_or(vec![pin_a_eq, not_len_a_lower]);
    let pin_b = terms.mk_or(vec![pin_b_eq, not_len_b_lower]);
    let not_len_a_upper = terms.mk_not_raw(len_a_upper);
    let not_len_b_upper = terms.mk_not_raw(len_b_upper);
    let out_of_range_a = terms.mk_or(vec![not_len_a_lower, not_len_a_upper]);
    let out_of_range_b = terms.mk_or(vec![not_len_b_lower, not_len_b_upper]);
    let truth = terms.mk_bool(true);
    let not_nat_a_lower = terms.mk_not_raw(nat_a_lower);
    let not_nat_b_lower = terms.mk_not_raw(nat_b_lower);
    let not_truth = terms.mk_not_raw(truth);
    let not_nat_a_upper = terms.mk_not_raw(nat_a_upper);
    let not_nat_b_upper = terms.mk_not_raw(nat_b_upper);
    let not_out_of_range_a = terms.mk_not_raw(out_of_range_a);
    let not_out_of_range_b = terms.mk_not_raw(out_of_range_b);

    SeqCarrierFixture {
        terms,
        assertions: vec![len_a_lower, len_b_lower, pin_a, pin_b],
        range_units: vec![nat_a_lower, nat_b_lower, nat_a_upper, nat_b_upper],
        left_conflict: vec![
            not_nat_a_lower,
            not_nat_b_lower,
            not_truth,
            not_nat_a_upper,
            not_nat_b_upper,
            not_out_of_range_a,
        ],
        right_conflict: vec![
            not_nat_a_lower,
            not_nat_b_lower,
            not_truth,
            not_nat_a_upper,
            not_nat_b_upper,
            not_out_of_range_b,
        ],
    }
}

#[test]
fn exact_seq_carrier_range_and_context_clauses_replay_for_both_operands() {
    for width in [8, 64] {
        let mut fixture = seq_carrier_fixture(width);
        for &unit in &fixture.range_units {
            assert!(
                discharge_trust_clause(&fixture.terms, &[unit], &fixture.assertions).is_some(),
                "width-{width} bv2nat range unit must replay as a standalone theorem"
            );
        }
        let left_out_of_range = match fixture.terms.get(fixture.left_conflict[5]) {
            ay_core::TermData::Not(root) => *root,
            _ => unreachable!(),
        };
        fixture.assertions.push(left_out_of_range);
        assert!(
            discharge_trust_clause(&fixture.terms, &fixture.left_conflict, &fixture.assertions,)
                .is_some(),
            "left width-{width} conflict must replay only under its authored context"
        );
        fixture.assertions.pop();
        let right_out_of_range = match fixture.terms.get(fixture.right_conflict[5]) {
            ay_core::TermData::Not(root) => *root,
            _ => unreachable!(),
        };
        fixture.assertions.push(right_out_of_range);
        assert!(
            discharge_trust_clause(&fixture.terms, &fixture.right_conflict, &fixture.assertions,)
                .is_some(),
            "right width-{width} conflict must replay only under its authored context"
        );
    }
}

#[test]
fn bv2nat_source_replay_rejects_falsifiable_near_misses() {
    let mut fixture = seq_carrier_fixture(8);
    let idx = fixture
        .terms
        .mk_var("source_replay_near_miss_idx", Sort::bitvec(8));
    let nat = fixture.terms.mk_bv2nat(idx);
    let too_tight = fixture.terms.mk_int(BigInt::from(254_u16));
    let falsifiable_unit = fixture.terms.mk_le(nat, too_tight);
    assert!(
        discharge_trust_clause(&fixture.terms, &[falsifiable_unit], &[]).is_none(),
        "a bound below the carrier maximum is not a standalone theorem"
    );
    let unrelated_len = fixture
        .terms
        .mk_var("source_replay_unrelated_len", Sort::Int);
    let zero = fixture.terms.mk_int(BigInt::from(0_u8));
    let max = fixture.terms.mk_int(BigInt::from(255_u16));
    let unrelated_lower = fixture.terms.mk_le(zero, unrelated_len);
    let unrelated_upper = fixture.terms.mk_le(unrelated_len, max);
    let not_unrelated_lower = fixture.terms.mk_not_raw(unrelated_lower);
    let not_unrelated_upper = fixture.terms.mk_not_raw(unrelated_upper);
    let unrelated_out_of_range = fixture
        .terms
        .mk_or(vec![not_unrelated_lower, not_unrelated_upper]);
    let not_unrelated_out_of_range = fixture.terms.mk_not_raw(unrelated_out_of_range);
    fixture.left_conflict[5] = not_unrelated_out_of_range;
    assert!(
        discharge_trust_clause(&fixture.terms, &fixture.left_conflict, &fixture.assertions)
            .is_none(),
        "a conflict clause must not borrow a pin for a different integer"
    );
}
