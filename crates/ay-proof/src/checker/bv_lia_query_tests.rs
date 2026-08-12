// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Focused tests for the source-bound BV/LIA authenticator.

use ay_core::{Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;
use num_traits::{One, Zero};

use crate::{check_proof_strict, validate_reachable_assumes_in_problem_scope};

use super::{
    authenticate_bv_lia_unsat_query, validate_bv_lia_tautology, BvLiaUnsatAuthenticationError,
};

#[test]
fn bounded_bv_to_nat_query_authenticates_and_rejects_sat_near_miss() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("bridge_x", Sort::bitvec(4));
    let nat = terms.mk_bv2nat(x);
    let five = terms.mk_int(5.into());
    let three_bv = terms.mk_bitvec(BigInt::from(3_u8), 4);
    let above_five = terms.mk_gt(nat, five);
    let below_three = terms.mk_bvult(x, three_bv);
    let roots = [above_five, below_three];
    let evidence = authenticate_bv_lia_unsat_query(&terms, &roots, None)
        .expect("finite BV enumeration proves the bridge contradiction");
    assert!(evidence.is_current_for(&terms, &roots));

    let ten_bv = terms.mk_bitvec(BigInt::from(10_u8), 4);
    let below_ten = terms.mk_bvult(x, ten_bv);
    let sat_roots = [above_five, below_ten];
    let error = authenticate_bv_lia_unsat_query(&terms, &sat_roots, None)
        .expect_err("x=6 witnesses the near-miss query");
    assert!(matches!(error, BvLiaUnsatAuthenticationError::Satisfiable));
}

#[test]
fn bv2nat_pin_decides_signed_msb_without_wide_enumeration() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("signed_pin_x", Sort::bitvec(32));
    let nat = terms.mk_bv2nat(x);
    let ten = terms.mk_int(10.into());
    let pin = terms.mk_eq(nat, ten);
    let zero = terms.mk_bitvec(BigInt::zero(), 32);
    let negative = terms.mk_bvslt(x, zero);
    let unrelated = terms.mk_var("signed_pin_unrelated", Sort::bitvec(64));
    let unrelated_nat = terms.mk_bv2nat(unrelated);
    let three = terms.mk_int(3.into());
    let unrelated_pin = terms.mk_eq(unrelated_nat, three);

    authenticate_bv_lia_unsat_query(&terms, &[unrelated_pin, pin, negative], None)
        .expect("the exact bv2nat pin fixes the sign bit without 2^32 enumeration");

    let sign_bit = terms.mk_int(BigInt::one() << 31_u32);
    let negative_pin = terms.mk_eq(sign_bit, nat);
    let error = authenticate_bv_lia_unsat_query(&terms, &[negative_pin, negative], None)
        .expect_err("the sign-bit value is a satisfying negative witness");
    assert!(matches!(error, BvLiaUnsatAuthenticationError::Satisfiable));
}

#[test]
fn wide_bv_constant_pin_propagates_before_finite_domain_sizing() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("bridge_wide_x", Sort::bitvec(16));
    let result = terms.mk_var("bridge_wide_result", Sort::bitvec(16));
    let forty_thousand = terms.mk_bitvec(BigInt::from(40_000_u32), 16);
    // Put the alias first so the checker must revisit it after learning the
    // constant pin. Neither variable may be counted as a free 2^16 domain.
    let alias = terms.mk_eq(result, x);
    let pin = terms.mk_eq(x, forty_thousand);
    let nat = terms.mk_bv2nat(x);
    let two = terms.mk_int(BigInt::from(2_u8));
    let doubled = terms.mk_mul(vec![nat, two]);
    let u16_max = terms.mk_int(BigInt::from(65_535_u32));
    let impossible = terms.mk_le(doubled, u16_max);
    let roots = [alias, pin, impossible];

    authenticate_bv_lia_unsat_query(&terms, &roots, None)
        .expect("a source-pinned BV16 value must authenticate without enumeration");
}

#[test]
fn wide_bv_constant_pin_sat_near_miss_is_not_authenticated() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("bridge_wide_sat_x", Sort::bitvec(16));
    let forty_thousand = terms.mk_bitvec(BigInt::from(40_000_u32), 16);
    let pin = terms.mk_eq(forty_thousand, x);
    let nat = terms.mk_bv2nat(x);
    let two = terms.mk_int(BigInt::from(2_u8));
    let doubled = terms.mk_mul(vec![nat, two]);
    let eighty_thousand = terms.mk_int(BigInt::from(80_000_u32));
    let attainable = terms.mk_le(doubled, eighty_thousand);
    let roots = [pin, attainable];

    let error = authenticate_bv_lia_unsat_query(&terms, &roots, None)
        .expect_err("x=40000 satisfies the boundary near-miss");
    assert!(matches!(error, BvLiaUnsatAuthenticationError::Satisfiable));
}

#[test]
fn base_environment_assignments_are_removed_from_dimensions() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("base_dimension_x", Sort::bitvec(16));
    let alias = terms.mk_var("base_dimension_alias", Sort::bitvec(16));
    let forty_thousand = terms.mk_bitvec(BigInt::from(40_000_u32), 16);
    let alias_definition = terms.mk_eq(alias, x);
    let pin = terms.mk_eq(x, forty_thousand);
    let choice = terms.mk_var("base_dimension_choice", Sort::Bool);
    let not_choice = terms.mk_not_raw(choice);
    let impossible = terms.mk_eq(choice, not_choice);

    authenticate_bv_lia_unsat_query(&terms, &[alias_definition, pin, impossible], None)
        .expect("only the free Boolean dimension remains after exact base propagation");
}

#[test]
fn contradictory_bv2nat_pins_are_authenticated_without_enumeration() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("conflicting_pin_x", Sort::bitvec(64));
    let nat = terms.mk_bv2nat(x);
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let first = terms.mk_eq(nat, one);
    let second = terms.mk_eq(two, nat);

    authenticate_bv_lia_unsat_query(&terms, &[first, second], None)
        .expect("conflicting exact pins refute even a 64-bit source");
}

#[test]
fn out_of_range_bv2nat_pin_is_an_immediate_contradiction() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("range_pin_x", Sort::bitvec(8));
    let nat = terms.mk_bv2nat(x);
    let out_of_range = terms.mk_int(256.into());
    let impossible = terms.mk_eq(nat, out_of_range);

    authenticate_bv_lia_unsat_query(&terms, &[impossible], None)
        .expect("an eight-bit unsigned value cannot equal 256");
}

#[test]
fn bv_lia_tautology_rule_replays_exact_negated_roots_and_rejects_forgery() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("bridge_rule_x", Sort::bitvec(16));
    let forty_thousand = terms.mk_bitvec(BigInt::from(40_000_u32), 16);
    let pin = terms.mk_eq(x, forty_thousand);
    let nat = terms.mk_bv2nat(x);
    let two = terms.mk_int(BigInt::from(2_u8));
    let doubled = terms.mk_mul(vec![nat, two]);
    let u16_max = terms.mk_int(BigInt::from(65_535_u32));
    let impossible = terms.mk_le(doubled, u16_max);
    let clause = [terms.mk_not_raw(pin), terms.mk_not_raw(impossible)];

    validate_bv_lia_tautology(&terms, ProofId(7), &clause, false, false)
        .expect("negations of an independently UNSAT source conjunction form a tautology");

    let forged_sat_bound = terms.mk_int(BigInt::from(80_000_u32));
    let attainable = terms.mk_le(doubled, forged_sat_bound);
    let forged = [terms.mk_not_raw(pin), terms.mk_not_raw(attainable)];
    validate_bv_lia_tautology(&terms, ProofId(8), &forged, false, false)
        .expect_err("a satisfiable source conjunction must not become a certified lemma");

    validate_bv_lia_tautology(&terms, ProofId(9), &[pin], false, false)
        .expect_err("a positive clause literal must not be reinterpreted as a source root");
    validate_bv_lia_tautology(&terms, ProofId(10), &clause, true, false)
        .expect_err("unrelated arithmetic annotations must fail closed");
}

#[test]
fn bv_lia_tautology_proof_cannot_borrow_a_foreign_source_assumption() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("bridge_scope_x", Sort::bitvec(16));
    let forty_thousand = terms.mk_bitvec(BigInt::from(40_000_u32), 16);
    let pin = terms.mk_eq(x, forty_thousand);
    let nat = terms.mk_bv2nat(x);
    let two = terms.mk_int(BigInt::from(2_u8));
    let doubled = terms.mk_mul(vec![nat, two]);
    let u16_max = terms.mk_int(BigInt::from(65_535_u32));
    let impossible = terms.mk_le(doubled, u16_max);
    let not_pin = terms.mk_not_raw(pin);
    let not_impossible = terms.mk_not_raw(impossible);

    let mut proof = Proof::new();
    let pin_assume = proof.add_assume(pin, None);
    let impossible_assume = proof.add_assume(impossible, None);
    let lemma = proof.add_step(ProofStep::TheoryLemma {
        theory: "BV_LIA".to_string(),
        clause: vec![not_pin, not_impossible],
        farkas: None,
        kind: TheoryLemmaKind::BvLiaTautology,
        lia: None,
    });
    let residual = proof.add_resolution(vec![not_impossible], pin, lemma, pin_assume);
    proof.add_resolution(Vec::new(), impossible, residual, impossible_assume);

    check_proof_strict(&proof, &terms)
        .expect("the semantic proof itself must replay independently");
    validate_reachable_assumes_in_problem_scope(&proof, &[pin, impossible])
        .expect("both exact authored roots authorize the proof");
    validate_reachable_assumes_in_problem_scope(&proof, &[pin])
        .expect_err("the semantic theorem cannot lend authority to a foreign assume");
}

#[test]
fn genuinely_free_wide_bv_still_declines_bounded_authentication() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("bridge_free_wide_x", Sort::bitvec(17));
    let nat = terms.mk_bv2nat(x);
    let one = terms.mk_int(BigInt::from(1_u8));
    let possibly_true = terms.mk_ge(nat, one);

    let error = authenticate_bv_lia_unsat_query(&terms, &[possibly_true], None)
        .expect_err("an unpinned BV17 domain must remain outside the finite cap");
    assert!(matches!(
        error,
        BvLiaUnsatAuthenticationError::UnsupportedFragment { .. }
    ));
}

#[test]
fn malformed_bv2nat_pin_sorts_fail_closed() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("malformed_pin_x", Sort::bitvec(8));
    let nat = terms.mk_bv2nat(x);
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());

    let non_boolean_first = terms.mk_app(Symbol::named("="), [nat, one], Sort::Int);
    let non_boolean_second = terms.mk_app(Symbol::named("="), [nat, two], Sort::Int);
    let error =
        authenticate_bv_lia_unsat_query(&terms, &[non_boolean_first, non_boolean_second], None)
            .expect_err("a non-Boolean equality is not an authenticated assertion");
    assert!(matches!(
        error,
        BvLiaUnsatAuthenticationError::UnsupportedFragment { .. }
    ));

    let valid_first = terms.mk_eq(nat, one);
    let valid_second = terms.mk_eq(nat, two);
    let malformed_and = terms.mk_app(Symbol::named("and"), [valid_first, valid_second], Sort::Int);
    let error = authenticate_bv_lia_unsat_query(&terms, &[malformed_and], None)
        .expect_err("a non-Boolean and-node cannot hide contradictory Boolean children");
    assert!(matches!(
        error,
        BvLiaUnsatAuthenticationError::UnsupportedFragment { .. }
    ));

    let malformed_nat = terms.mk_app(Symbol::named("bv2nat"), [x], Sort::Bool);
    let mismatched_first = terms.mk_app(Symbol::named("="), [malformed_nat, one], Sort::Bool);
    let mismatched_second = terms.mk_app(Symbol::named("="), [malformed_nat, two], Sort::Bool);
    let error =
        authenticate_bv_lia_unsat_query(&terms, &[mismatched_first, mismatched_second], None)
            .expect_err("a non-Int bv2nat node cannot pin a bit-vector");
    assert!(matches!(
        error,
        BvLiaUnsatAuthenticationError::UnsupportedFragment { .. }
    ));

    let out_of_range = terms.mk_int(256.into());
    let malformed_range = terms.mk_app(
        Symbol::named("="),
        [malformed_nat, out_of_range],
        Sort::Bool,
    );
    let error = authenticate_bv_lia_unsat_query(&terms, &[malformed_range], None)
        .expect_err("an ill-sorted bv2nat cannot use the structural range shortcut");
    assert!(matches!(
        error,
        BvLiaUnsatAuthenticationError::UnsupportedFragment { .. }
    ));
}

#[test]
fn many_bv2nat_pins_seed_one_reused_environment() {
    const PINNED: usize = 2_048;

    let mut terms = TermStore::new();
    let free = terms.mk_var("many_pins_free", Sort::bitvec(12));
    let zero_bv = terms.mk_bitvec(BigInt::zero(), 12);
    let impossible = terms.mk_bvult(free, zero_bv);
    let mut conjuncts = Vec::with_capacity(PINNED + 1);
    conjuncts.push(impossible);
    for index in 0..PINNED {
        let pinned = terms.mk_var(format!("many_pins_{index}"), Sort::bitvec(16));
        let nat = terms.mk_bv2nat(pinned);
        let value = terms.mk_int(BigInt::from(index));
        conjuncts.push(terms.mk_eq(nat, value));
    }
    let root = terms.mk_app(Symbol::named("and"), conjuncts, Sort::Bool);

    authenticate_bv_lia_unsat_query(&terms, &[root], None)
        .expect("fixed pins are seeded once while the free dimension is enumerated");
}

#[test]
fn reused_environment_clears_propagated_integer_assignments() {
    let mut terms = TermStore::new();
    let choice = terms.mk_var("pin_env_choice", Sort::Bool);
    let value = terms.mk_var("pin_env_value", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let selected = terms.mk_ite(choice, one, zero);
    let definition = terms.mk_eq(value, selected);
    let value_is_one = terms.mk_eq(value, one);
    let guarded = terms.mk_app(Symbol::named("or"), [choice, value_is_one], Sort::Bool);

    let error = authenticate_bv_lia_unsat_query(&terms, &[definition, guarded], None)
        .expect_err("the true ordinal must not inherit value=0 from the refuted false ordinal");
    assert!(matches!(error, BvLiaUnsatAuthenticationError::Satisfiable));
}

#[test]
fn repeated_integer_squaring_declines_before_bigint_expansion() {
    let mut terms = TermStore::new();
    let mut power = terms.mk_int(3.into());
    for _ in 0..32 {
        power = terms.mk_app(Symbol::named("*"), [power, power], Sort::Int);
    }
    let zero = terms.mk_int(0.into());
    let impossible = terms.mk_eq(power, zero);

    let error = authenticate_bv_lia_unsat_query(&terms, &[impossible], None)
        .expect_err("compact multiplication DAGs must not create unbounded checker integers");
    assert!(matches!(
        error,
        BvLiaUnsatAuthenticationError::ResourceLimit {
            resource: "integer magnitude"
        }
    ));
}

#[test]
fn malformed_equality_cannot_persist_a_value_in_the_wrong_environment_map() {
    let mut terms = TermStore::new();
    let integer = terms.mk_var("wrong_map_integer", Sort::Int);
    let bits = terms.mk_var("wrong_map_bits", Sort::bitvec(1));
    let malformed = terms.mk_app(Symbol::named("="), [integer, bits], Sort::Bool);
    let zero = terms.mk_bitvec(BigInt::zero(), 1);
    let positive = terms.mk_bvugt(bits, zero);

    let error = authenticate_bv_lia_unsat_query(&terms, &[malformed, positive], None)
        .expect_err("an Int variable cannot receive a bit-vector value");
    assert!(matches!(
        error,
        BvLiaUnsatAuthenticationError::UnsupportedFragment { .. }
    ));
}

#[test]
fn universal_bv2nat_range_rejects_unbounded_source_violation() {
    let mut terms = TermStore::new();
    let source = terms.mk_var("bridge_e", Sort::Int);
    let bv = terms.mk_int2bv(8, source);
    let nat = terms.mk_bv2nat(bv);
    let max = terms.mk_int(255.into());
    let impossible = terms.mk_gt(nat, max);
    authenticate_bv_lia_unsat_query(&terms, &[impossible], None)
        .expect("bv2nat is universally bounded by its width");
}

#[test]
fn in_range_int2bv_residue_identity_is_symbolically_checked() {
    let mut terms = TermStore::new();
    let source = terms.mk_var("bridge_source", Sort::Int);
    let zero = terms.mk_int(0.into());
    let modulus = terms.mk_int((1_i64 << 32).into());
    let nonnegative = terms.mk_ge(source, zero);
    let below_modulus = terms.mk_lt(source, modulus);
    let bv = terms.mk_int2bv(32, source);
    let nat = terms.mk_bv2nat(bv);
    let impossible = terms.mk_gt(nat, source);
    authenticate_bv_lia_unsat_query(&terms, &[nonnegative, below_modulus, impossible], None)
        .expect("in-range int2bv/bv2nat is the identity");
}

#[test]
fn evidence_retires_after_term_snapshot_change() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("bridge_stale_x", Sort::bitvec(2));
    let zero = terms.mk_bitvec(BigInt::from(0_u8), 2);
    let lt_zero = terms.mk_app(Symbol::named("bvult"), [x, zero], Sort::Bool);
    let evidence = authenticate_bv_lia_unsat_query(&terms, &[lt_zero], None)
        .expect("unsigned value cannot be below zero");
    let _late = terms.mk_var("bridge_stale_late", Sort::Bool);
    assert!(!evidence.term_snapshot_is_current(&terms));
}

#[test]
fn malformed_or_oversized_bv_widths_fail_closed() {
    let mut terms = TermStore::new();
    let zero_width = terms.mk_bitvec(BigInt::from(0_u8), 0);
    let signed_lt = terms.mk_app(Symbol::named("bvslt"), [zero_width, zero_width], Sort::Bool);
    let zero_error = authenticate_bv_lia_unsat_query(&terms, &[signed_lt], None)
        .expect_err("zero-width signed arithmetic is outside the checked fragment");
    assert!(matches!(
        zero_error,
        BvLiaUnsatAuthenticationError::UnsupportedFragment { .. }
    ));

    let source = terms.mk_var("bridge_huge_width_source", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0_u8));
    let one = terms.mk_int(BigInt::from(1_u8));
    let lower = terms.mk_ge(source, zero);
    let upper = terms.mk_le(source, one);
    let huge_bv = terms.mk_int2bv(u32::MAX, source);
    let huge_nat = terms.mk_bv2nat(huge_bv);
    let impossible = terms.mk_gt(huge_nat, source);
    let huge_error = authenticate_bv_lia_unsat_query(&terms, &[lower, upper, impossible], None)
        .expect_err("oversized int2bv width must not allocate or certify");
    assert!(matches!(
        huge_error,
        BvLiaUnsatAuthenticationError::UnsupportedFragment { .. }
    ));
}

#[test]
fn dangling_child_term_id_fails_closed_before_sort_lookup() {
    let mut terms = TermStore::new();
    let dangling = TermId::new(u32::MAX);
    let root = terms.mk_app(Symbol::named("not"), [dangling], Sort::Bool);

    let error = authenticate_bv_lia_unsat_query(&terms, &[root], None)
        .expect_err("a dangling native term handle must never reach an unchecked lookup");
    assert!(matches!(
        error,
        BvLiaUnsatAuthenticationError::UnsupportedFragment { .. }
    ));
}

#[test]
fn cyclic_conjunction_fails_closed_during_flattening() {
    let mut terms = TermStore::new();
    let predicted_root = TermId::new(terms.len() as u32);
    let root = terms.mk_app(Symbol::named("and"), [predicted_root], Sort::Bool);
    assert_eq!(root, predicted_root);

    let error = authenticate_bv_lia_unsat_query(&terms, &[root], None)
        .expect_err("a cyclic native term graph must not consume the full work budget");
    assert!(matches!(
        error,
        BvLiaUnsatAuthenticationError::UnsupportedFragment { .. }
    ));
}

#[test]
fn long_integer_equality_chain_uses_bounded_stack() {
    const VARIABLES: usize = 20_000;

    let mut terms = TermStore::new();
    let vars: Vec<_> = (0..VARIABLES)
        .map(|index| terms.mk_var(format!("bridge_chain_{index}"), Sort::Int))
        .collect();
    let mut conjuncts = Vec::with_capacity(VARIABLES + 1);
    // This orientation deliberately creates the deepest tree for the
    // union policy before the final class walk compresses it.
    for index in 1..VARIABLES {
        conjuncts.push(terms.mk_eq(vars[index], vars[index - 1]));
    }
    let zero = terms.mk_int(BigInt::from(0_u8));
    let one = terms.mk_int(BigInt::from(1_u8));
    conjuncts.push(terms.mk_eq(vars[0], zero));
    conjuncts.push(terms.mk_eq(vars[VARIABLES - 1], one));
    let root = terms.mk_app(Symbol::named("and"), conjuncts, Sort::Bool);

    authenticate_bv_lia_unsat_query(&terms, &[root], None)
        .expect("the long equality chain is contradictory without recursive find");
}
