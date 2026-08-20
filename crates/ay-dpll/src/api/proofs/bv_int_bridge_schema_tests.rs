// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Acceptance and NARROWNESS pins for the closed-form BV<->Int bridge lane.
//!
//! Every acceptance test is paired with a near miss that must still be refused:
//! recovering a proof is the goal, but a lane that recovers indiscriminately is
//! a hole.

use ay_core::{Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;

use super::discharge_bv_int_bridge_schema;
use crate::api::proofs::discharge_trust_clause;

/// The exact clause set collected by `discharge_trust_steps_for_certification`
/// for the deductive-checks `i = i + 1usize` loop-counter overflow obligation, rebuilt
/// term for term from the `--probe-cert-reject` dump.
struct LoopCounterFixture {
    terms: TermStore,
    /// `i`, the loop-body counter.
    i: TermId,
    /// `n`, the loop bound.
    n: TermId,
    /// `(bvadd i 1)`.
    i_plus_one: TermId,
    /// The authored assertions the certification lane passes in.
    assertions: Vec<TermId>,
    /// `(<= (bv2nat n) 2^w - 1)`.
    t0: TermId,
    /// `(< (bv2nat i) (bv2nat n))`.
    t1: TermId,
    /// `(<= 0 (bv2nat (bvadd i 1)))`.
    t2: TermId,
    /// `(< (bv2nat (bvadd i 1)) (bv2nat i))`.
    t3: TermId,
    /// The modular residue disjunction for `(bvadd i 1)`.
    t4: TermId,
}

fn bv_op(terms: &mut TermStore, name: &str, args: Vec<TermId>, width: u32) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::bitvec(width))
}

fn bv_pred(terms: &mut TermStore, name: &str, args: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::Bool)
}

fn loop_counter_fixture(width: u32) -> LoopCounterFixture {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i__loopbody_0", Sort::bitvec(width));
    let n = terms.mk_var("n", Sort::bitvec(width));
    let one_bv = terms.mk_bitvec(BigInt::from(1_u8), width);
    let i_plus_one = bv_op(&mut terms, "bvadd", vec![i, one_bv], width);

    let nat_i = terms.mk_bv2nat(i);
    let nat_n = terms.mk_bv2nat(n);
    let nat_next = terms.mk_bv2nat(i_plus_one);

    let zero = terms.mk_int(BigInt::from(0_u8));
    let max = terms.mk_int((BigInt::from(1_u8) << width) - BigInt::from(1_u8));
    let modulus = terms.mk_int(BigInt::from(1_u8) << width);
    let one_int = terms.mk_int(BigInt::from(1_u8));

    let t0 = terms.mk_le(nat_n, max);
    let t1 = terms.mk_lt(nat_i, nat_n);
    let t2 = terms.mk_le(zero, nat_next);
    let t3 = terms.mk_lt(nat_next, nat_i);
    let base = terms.mk_add(vec![nat_i, one_int]);
    let wrapped = terms.mk_sub(vec![base, modulus]);
    let eq_base = terms.mk_eq(nat_next, base);
    let eq_wrapped = terms.mk_eq(nat_next, wrapped);
    let t4 = terms.mk_or(vec![eq_base, eq_wrapped]);

    // `(and (bvult i n) (not (bvule i (bvadd i 1))))` — the loop guard
    // conjoined with the negated no-overflow goal, exactly as authored.
    let bvult = bv_pred(&mut terms, "bvult", vec![i, n]);
    let bvule = bv_pred(&mut terms, "bvule", vec![i, i_plus_one]);
    let not_bvule = terms.mk_not(bvule);
    let guard = terms.mk_and(vec![bvult, not_bvule]);

    LoopCounterFixture {
        terms,
        i,
        n,
        i_plus_one,
        assertions: vec![guard],
        t0,
        t1,
        t2,
        t3,
        t4,
    }
}

// ---------------------------------------------------------------------------
// Acceptance: the real production path
// ---------------------------------------------------------------------------

#[test]
fn loop_counter_overflow_trust_clauses_all_discharge_through_the_gate() {
    for width in [8_u32, 16, 32, 64] {
        let fixture = loop_counter_fixture(width);
        for (name, clause) in [
            ("t0", fixture.t0),
            ("t1", fixture.t1),
            ("t2", fixture.t2),
            ("t3", fixture.t3),
            ("t4", fixture.t4),
        ] {
            assert!(
                discharge_trust_clause(&fixture.terms, &[clause], &fixture.assertions).is_some(),
                "width-{width} {name} must discharge through the certification gate"
            );
        }
    }
}

#[test]
fn modular_residue_and_order_schemas_need_no_solver_at_every_width() {
    // The point of this lane: no enumeration, so 64-bit is no harder than 8.
    for width in [8_u32, 16, 32, 64] {
        let fixture = loop_counter_fixture(width);
        for (name, clause) in [("t1", fixture.t1), ("t3", fixture.t3), ("t4", fixture.t4)] {
            assert!(
                discharge_bv_int_bridge_schema(&fixture.terms, &[clause], &fixture.assertions),
                "width-{width} {name} must be recognised by the closed-form lane"
            );
        }
    }
}

#[test]
fn bvsub_modular_residue_wraps_upward() {
    let width = 64_u32;
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(width));
    let b = terms.mk_var("b", Sort::bitvec(width));
    let diff_bv = bv_op(&mut terms, "bvsub", vec![a, b], width);
    let nat_a = terms.mk_bv2nat(a);
    let nat_b = terms.mk_bv2nat(b);
    let nat_diff = terms.mk_bv2nat(diff_bv);
    let modulus = terms.mk_int(BigInt::from(1_u8) << width);
    let base = terms.mk_sub(vec![nat_a, nat_b]);
    let wrapped = terms.mk_add(vec![base, modulus]);
    let eq_base = terms.mk_eq(nat_diff, base);
    let eq_wrapped = terms.mk_eq(nat_diff, wrapped);
    let clause = terms.mk_or(vec![eq_base, eq_wrapped]);
    assert!(discharge_bv_int_bridge_schema(&terms, &[clause], &[]));
}

// ---------------------------------------------------------------------------
// NARROWNESS PINS — each of these is FALSE and must stay refused
// ---------------------------------------------------------------------------

#[test]
fn residue_with_the_wrong_modulus_is_refused() {
    // `2^w - 1` instead of `2^w`: falsifiable at i = 2^w - 1, where the true
    // residue is 0 but this claims 0 or 1.
    let width = 64_u32;
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(width));
    let one_bv = terms.mk_bitvec(BigInt::from(1_u8), width);
    let next = bv_op(&mut terms, "bvadd", vec![i, one_bv], width);
    let nat_i = terms.mk_bv2nat(i);
    let nat_next = terms.mk_bv2nat(next);
    let one_int = terms.mk_int(BigInt::from(1_u8));
    let off_by_one = terms.mk_int((BigInt::from(1_u8) << width) - BigInt::from(1_u8));
    let base = terms.mk_add(vec![nat_i, one_int]);
    let wrapped = terms.mk_sub(vec![base, off_by_one]);
    let eq_base = terms.mk_eq(nat_next, base);
    let eq_wrapped = terms.mk_eq(nat_next, wrapped);
    let clause = terms.mk_or(vec![eq_base, eq_wrapped]);
    assert!(
        !discharge_bv_int_bridge_schema(&terms, &[clause], &[]),
        "an off-by-one modulus is not the residue theorem"
    );
}

#[test]
fn residue_over_a_different_operand_is_refused() {
    // `bv2nat(bvadd i 1) = bv2nat(i) + bv2nat(i)` — right shape, wrong operand.
    let width = 64_u32;
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(width));
    let j = terms.mk_var("j", Sort::bitvec(width));
    let next = bv_op(&mut terms, "bvadd", vec![i, j], width);
    let nat_i = terms.mk_bv2nat(i);
    let nat_next = terms.mk_bv2nat(next);
    let modulus = terms.mk_int(BigInt::from(1_u8) << width);
    let base = terms.mk_add(vec![nat_i, nat_i]);
    let wrapped = terms.mk_sub(vec![base, modulus]);
    let eq_base = terms.mk_eq(nat_next, base);
    let eq_wrapped = terms.mk_eq(nat_next, wrapped);
    let clause = terms.mk_or(vec![eq_base, eq_wrapped]);
    assert!(
        !discharge_bv_int_bridge_schema(&terms, &[clause], &[]),
        "the residue must be over the operands of the bvadd itself"
    );
}

#[test]
fn residue_with_a_narrower_operand_is_refused() {
    // A zero-extended operand does not carry the result width, so the two-case
    // residue derivation does not apply as written.
    let mut terms = TermStore::new();
    let wide = terms.mk_var("wide", Sort::bitvec(64));
    let narrow = terms.mk_var("narrow", Sort::bitvec(32));
    let sum = terms.mk_app(Symbol::named("bvadd"), vec![wide, narrow], Sort::bitvec(64));
    let nat_wide = terms.mk_bv2nat(wide);
    let nat_narrow = terms.mk_bv2nat(narrow);
    let nat_sum = terms.mk_bv2nat(sum);
    let modulus = terms.mk_int(BigInt::from(1_u8) << 64_u32);
    let base = terms.mk_add(vec![nat_wide, nat_narrow]);
    let wrapped = terms.mk_sub(vec![base, modulus]);
    let eq_base = terms.mk_eq(nat_sum, base);
    let eq_wrapped = terms.mk_eq(nat_sum, wrapped);
    let clause = terms.mk_or(vec![eq_base, eq_wrapped]);
    assert!(!discharge_bv_int_bridge_schema(&terms, &[clause], &[]));
}

#[test]
fn residue_using_the_bvsub_wrap_direction_for_bvadd_is_refused() {
    // `bvadd` wraps DOWN. Claiming `+ 2^w` is false whenever the sum wraps.
    let width = 64_u32;
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(width));
    let b = terms.mk_var("b", Sort::bitvec(width));
    let sum_bv = bv_op(&mut terms, "bvadd", vec![a, b], width);
    let nat_a = terms.mk_bv2nat(a);
    let nat_b = terms.mk_bv2nat(b);
    let nat_sum = terms.mk_bv2nat(sum_bv);
    let modulus = terms.mk_int(BigInt::from(1_u8) << width);
    let base = terms.mk_add(vec![nat_a, nat_b]);
    let wrapped = terms.mk_add(vec![base, modulus]);
    let eq_base = terms.mk_eq(nat_sum, base);
    let eq_wrapped = terms.mk_eq(nat_sum, wrapped);
    let clause = terms.mk_or(vec![eq_base, eq_wrapped]);
    assert!(!discharge_bv_int_bridge_schema(&terms, &[clause], &[]));
}

#[test]
fn order_goal_without_an_authored_premise_is_refused() {
    // `bv2nat(i) < bv2nat(n)` is plainly falsifiable with no premise.
    let fixture = loop_counter_fixture(64);
    assert!(
        !discharge_bv_int_bridge_schema(&fixture.terms, &[fixture.t1], &[]),
        "the order bridge may only fire from an authored premise"
    );
}

#[test]
fn order_goal_is_refused_when_the_premise_is_only_a_disjunct() {
    // `(or (bvult i n) X)` does NOT assert `bvult i n`.
    let mut fixture = loop_counter_fixture(64);
    let bvult = bv_pred(&mut fixture.terms, "bvult", vec![fixture.i, fixture.n]);
    let other = bv_pred(
        &mut fixture.terms,
        "bvult",
        vec![fixture.n, fixture.i_plus_one],
    );
    let disjunction = fixture.terms.mk_or(vec![bvult, other]);
    assert!(
        !discharge_bv_int_bridge_schema(&fixture.terms, &[fixture.t1], &[disjunction]),
        "a disjunct is not an asserted premise"
    );
}

#[test]
fn order_goal_is_refused_when_the_premise_is_negated_as_a_whole() {
    // `(not (and (bvult i n) ...))` asserts neither conjunct.
    let mut fixture = loop_counter_fixture(64);
    let conjunction = fixture.assertions[0];
    let negated = fixture.terms.mk_not(conjunction);
    assert!(
        !discharge_bv_int_bridge_schema(&fixture.terms, &[fixture.t1], &[negated]),
        "a negated conjunction asserts no conjunct"
    );
}

#[test]
fn order_goal_with_the_operands_swapped_is_refused() {
    // Premise `bvult i n`; goal `bv2nat(n) < bv2nat(i)` — the converse.
    let mut fixture = loop_counter_fixture(64);
    let nat_i = fixture.terms.mk_bv2nat(fixture.i);
    let nat_n = fixture.terms.mk_bv2nat(fixture.n);
    let reversed = fixture.terms.mk_lt(nat_n, nat_i);
    assert!(!discharge_bv_int_bridge_schema(
        &fixture.terms,
        &[reversed],
        &fixture.assertions
    ));
}

#[test]
fn a_weak_premise_does_not_discharge_a_strict_goal() {
    // `bvule a b` gives `<=`, never `<`.
    let width = 64_u32;
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(width));
    let b = terms.mk_var("b", Sort::bitvec(width));
    let bvule = bv_pred(&mut terms, "bvule", vec![a, b]);
    let nat_a = terms.mk_bv2nat(a);
    let nat_b = terms.mk_bv2nat(b);
    let strict_goal = terms.mk_lt(nat_a, nat_b);
    let weak_goal = terms.mk_le(nat_a, nat_b);
    assert!(
        !discharge_bv_int_bridge_schema(&terms, &[strict_goal], &[bvule]),
        "`<=` must not discharge `<`"
    );
    assert!(
        discharge_bv_int_bridge_schema(&terms, &[weak_goal], &[bvule]),
        "`<=` must discharge `<=`"
    );
}

#[test]
fn a_signed_premise_never_discharges_an_unsigned_order_goal() {
    // `bvslt` ranges over the two's-complement value, not `bv2nat`.
    let width = 64_u32;
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(width));
    let b = terms.mk_var("b", Sort::bitvec(width));
    let bvslt = bv_pred(&mut terms, "bvslt", vec![a, b]);
    let nat_a = terms.mk_bv2nat(a);
    let nat_b = terms.mk_bv2nat(b);
    let goal = terms.mk_lt(nat_a, nat_b);
    assert!(
        !discharge_bv_int_bridge_schema(&terms, &[goal], &[bvslt]),
        "signed comparison is not an unsigned order premise"
    );
}

#[test]
fn multi_literal_clauses_are_never_recognised() {
    let fixture = loop_counter_fixture(64);
    assert!(!discharge_bv_int_bridge_schema(
        &fixture.terms,
        &[fixture.t1, fixture.t3],
        &fixture.assertions
    ));
    assert!(!discharge_bv_int_bridge_schema(
        &fixture.terms,
        &[],
        &fixture.assertions
    ));
}

#[test]
fn a_bitvec_literal_outside_unsigned_range_declines_the_lane() {
    // A payload that is not the canonical residue must never be imported as
    // the operand's `bv2nat` value.
    let width = 8_u32;
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::bitvec(width));
    let bad = terms.mk_bitvec(BigInt::from(-1_i8), width);
    let sum_bv = bv_op(&mut terms, "bvadd", vec![i, bad], width);
    let nat_i = terms.mk_bv2nat(i);
    let nat_sum = terms.mk_bv2nat(sum_bv);
    let modulus = terms.mk_int(BigInt::from(1_u8) << width);
    let minus_one = terms.mk_int(BigInt::from(-1_i8));
    let base = terms.mk_add(vec![nat_i, minus_one]);
    let wrapped = terms.mk_sub(vec![base, modulus]);
    let eq_base = terms.mk_eq(nat_sum, base);
    let eq_wrapped = terms.mk_eq(nat_sum, wrapped);
    let clause = terms.mk_or(vec![eq_base, eq_wrapped]);
    assert!(!discharge_bv_int_bridge_schema(&terms, &[clause], &[]));
}
