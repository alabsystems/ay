// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the width-independent interval refutation lane.
//!
//! The pins here come in pairs on purpose. Each accepting case is shadowed by a
//! near miss that is genuinely satisfiable and differs from it by one constant
//! or one dropped premise, so a widening of the lane fails the suite instead of
//! passing it.

use ay_core::{Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::super::{authenticate_bv_lia_unsat_query, BvLiaUnsatAuthenticationError};
use super::MAX_RESIDUE_SCHEMAS;

/// The measured `deductive-checks` length-companion obligation at carrier width `width`
/// with the Int-side upper limit `limit`.
///
/// ```text
/// A:  0 <= len                                        (length non-negativity)
/// B:  (len + 1) = bv2nat(index)  OR  not (0 <= len+1) (guarded carrier bridge)
/// C:  not (0 <= len+1)  OR  not (len+1 <= limit)      (negated goal)
/// ```
///
/// `A` forces the guard true, so `B` pins the successor length onto the carrier
/// and `C` excludes it. The conjunction is UNSAT exactly when
/// `limit >= 2^width - 1`.
fn length_companion_roots(
    terms: &mut TermStore,
    tag: &str,
    width: u32,
    limit: BigInt,
) -> Vec<TermId> {
    let len = terms.mk_var(format!("{tag}_len"), Sort::Int);
    let index = terms.mk_var(format!("{tag}_index"), Sort::bitvec(width));
    let nat = terms.mk_bv2nat(index);
    let zero = terms.mk_int(BigInt::zero());
    let one = terms.mk_int(BigInt::one());

    let lower = terms.mk_le(zero, len);
    let successor = terms.mk_add(vec![len, one]);
    let successor_lower = terms.mk_le(zero, successor);
    let not_successor_lower = terms.mk_not_raw(successor_lower);

    let pin = terms.mk_eq(successor, nat);
    let guarded_pin = terms.mk_or(vec![pin, not_successor_lower]);

    let limit = terms.mk_int(limit);
    let upper = terms.mk_le(successor, limit);
    let not_upper = terms.mk_not_raw(upper);
    let negated_goal = terms.mk_or(vec![not_successor_lower, not_upper]);

    vec![lower, guarded_pin, negated_goal]
}

/// THE TARGET. A 64-bit carrier is structurally beyond the finite enumerator
/// (`a free 64-bit BV variable exceeds finite enumeration`), so this shape can
/// only be authenticated by a derivation whose cost is the size of the formula.
#[test]
fn length_companion_bound_authenticates_at_every_carrier_width() {
    for width in [8_u32, 16, 32, 64] {
        let mut terms = TermStore::new();
        let limit = (BigInt::one() << width) - BigInt::one();
        let roots = length_companion_roots(&mut terms, &format!("companion_{width}"), width, limit);
        authenticate_bv_lia_unsat_query(&terms, &roots, None).unwrap_or_else(|error| {
            panic!("width-{width} length-companion bound must authenticate: {error}")
        });
    }
}

/// NARROWNESS PIN. One below the carrier maximum the query is SATISFIABLE
/// (`len = 2^w - 2`, `index = 2^w - 1`), and must not be authenticated.
#[test]
fn length_companion_bound_one_below_the_carrier_maximum_is_satisfiable() {
    for width in [8_u32, 64] {
        let mut terms = TermStore::new();
        let limit = (BigInt::one() << width) - BigInt::from(2_u8);
        let roots = length_companion_roots(&mut terms, &format!("near_miss_{width}"), width, limit);
        let error = authenticate_bv_lia_unsat_query(&terms, &roots, None).unwrap_err();
        assert!(
            error.is_capability_decline()
                || matches!(error, BvLiaUnsatAuthenticationError::Satisfiable),
            "width-{width} near miss must not be authenticated, got {error}"
        );
    }
}

/// NARROWNESS PIN. Without the length non-negativity premise the guard cannot
/// be discharged and the query is satisfiable (`len = -5`), so the pin and the
/// exclusion are both vacuously true.
#[test]
fn length_companion_bound_without_its_guard_premise_is_not_authenticated() {
    let mut terms = TermStore::new();
    let limit = (BigInt::one() << 64_u32) - BigInt::one();
    let roots = length_companion_roots(&mut terms, "unguarded", 64, limit);
    let error = authenticate_bv_lia_unsat_query(&terms, &roots[1..], None)
        .expect_err("a negative length satisfies both guarded clauses");
    assert!(error.is_capability_decline());
}

/// The first source-derived residue target. `0 <= n < 2^w-1` puts `n+1`
/// exactly in the no-wrap interval, so `1 <= int2bv_w(n+1)` in unsigned order.
/// The Int range is far beyond finite enumeration at both production widths.
#[test]
fn affine_int2bv_unsigned_order_authenticates_at_32_and_64_bits() {
    for width in [32_u32, 64] {
        let mut terms = TermStore::new();
        let n = terms.mk_var(format!("affine_no_wrap_{width}"), Sort::Int);
        let zero = terms.mk_int(BigInt::zero());
        let one = terms.mk_int(BigInt::one());
        let maximum = terms.mk_int((BigInt::one() << width) - BigInt::one());
        let nonnegative = terms.mk_le(zero, n);
        let below_maximum = terms.mk_lt(n, maximum);
        let successor = terms.mk_add(vec![n, one]);
        let converted = terms.mk_int2bv(width, successor);
        let one_bv = terms.mk_bitvec(BigInt::one(), width);
        let ordered = terms.mk_app(Symbol::named("bvule"), [one_bv, converted], Sort::Bool);
        let negated_order = terms.mk_not_raw(ordered);

        authenticate_bv_lia_unsat_query(&terms, &[nonnegative, below_maximum, negated_order], None)
            .unwrap_or_else(|error| {
                panic!("width-{width} affine no-wrap order must authenticate: {error}")
            });
    }
}

/// UPPER-WRAP CANARY. At `n = 2^w-1`, `n+1` converts to zero, so the negated
/// `1 <=u int2bv(n+1)` goal is satisfiable. Omitting the upper guard from the
/// generated round-trip would forge UNSAT here.
#[test]
fn affine_int2bv_upper_wrap_is_satisfiable_at_32_and_64_bits() {
    for width in [32_u32, 64] {
        let mut terms = TermStore::new();
        let n = terms.mk_var(format!("affine_upper_wrap_{width}"), Sort::Int);
        let maximum_value = (BigInt::one() << width) - BigInt::one();
        let maximum = terms.mk_int(maximum_value);
        let pin = terms.mk_eq(n, maximum);
        let one = terms.mk_int(BigInt::one());
        let successor = terms.mk_add(vec![n, one]);
        let converted = terms.mk_int2bv(width, successor);
        let one_bv = terms.mk_bitvec(BigInt::one(), width);
        let ordered = terms.mk_app(Symbol::named("bvule"), [one_bv, converted], Sort::Bool);
        let negated_order = terms.mk_not_raw(ordered);

        let error = authenticate_bv_lia_unsat_query(&terms, &[pin, negated_order], None)
            .expect_err("the upper-wrap value maps to zero and satisfies the negated order");
        assert!(
            error.is_capability_decline()
                || matches!(error, BvLiaUnsatAuthenticationError::Satisfiable),
            "width-{width} upper-wrap canary was unexpectedly authenticated: {error}"
        );
    }
}

/// LOWER-WRAP CANARY. At `n = -2`, `n+1 = -1` converts to all ones, so it is
/// not below one. Omitting the lower guard would identify its unsigned value
/// with `-1` and manufacture a contradiction.
#[test]
fn affine_int2bv_lower_wrap_is_satisfiable_at_32_and_64_bits() {
    for width in [32_u32, 64] {
        let mut terms = TermStore::new();
        let n = terms.mk_var(format!("affine_lower_wrap_{width}"), Sort::Int);
        let minus_two = terms.mk_int(BigInt::from(-2_i8));
        let pin = terms.mk_eq(n, minus_two);
        let one = terms.mk_int(BigInt::one());
        let successor = terms.mk_add(vec![n, one]);
        let converted = terms.mk_int2bv(width, successor);
        let one_bv = terms.mk_bitvec(BigInt::one(), width);
        let below_one = terms.mk_app(Symbol::named("bvult"), [converted, one_bv], Sort::Bool);
        let not_below_one = terms.mk_not_raw(below_one);

        let error = authenticate_bv_lia_unsat_query(&terms, &[pin, not_below_one], None)
            .expect_err("minus one converts to all ones and is not below one unsigned");
        assert!(
            error.is_capability_decline()
                || matches!(error, BvLiaUnsatAuthenticationError::Satisfiable),
            "width-{width} lower-wrap canary was unexpectedly authenticated: {error}"
        );
    }
}

/// Strict/non-strict and polarity table, kept as RAW applications so TermStore
/// reflexivity folding cannot hide an off-by-one error in the interval reader.
#[test]
fn unsigned_order_polarities_preserve_reflexive_boundaries() {
    for (name, polarity, unsatisfiable) in [
        ("bvult", true, true),
        ("bvult", false, false),
        ("bvule", true, false),
        ("bvule", false, true),
    ] {
        let mut terms = TermStore::new();
        let value = terms.mk_var(format!("{name}_{polarity}"), Sort::bitvec(64));
        let comparison = terms.mk_app(Symbol::named(name), [value, value], Sort::Bool);
        let root = if polarity {
            comparison
        } else {
            terms.mk_not_raw(comparison)
        };
        let result = authenticate_bv_lia_unsat_query(&terms, &[root], None);
        if unsatisfiable {
            result.unwrap_or_else(|error| {
                panic!("{name} polarity {polarity} reflexive contradiction: {error}")
            });
        } else {
            let error = result.expect_err("a reflexive unsigned-order truth is satisfiable");
            assert!(
                error.is_capability_decline()
                    || matches!(error, BvLiaUnsatAuthenticationError::Satisfiable),
                "{name} polarity {polarity} truth was unexpectedly authenticated: {error}"
            );
        }
    }
}

/// Exercise both orientations of strict unsigned order on a converted affine
/// term. Reflexive boundary pins above catch the polarity table's off-by-one,
/// while these cases require the guarded no-wrap equality to connect the BV
/// view back to authored Int bounds.
#[test]
fn affine_int2bv_strict_unsigned_order_authenticates_in_both_orientations() {
    for width in [32_u32, 64] {
        let mut terms = TermStore::new();
        let n = terms.mk_var(format!("strict_no_wrap_{width}"), Sort::Int);
        let zero = terms.mk_int(BigInt::zero());
        let one = terms.mk_int(BigInt::one());
        let maximum = terms.mk_int((BigInt::one() << width) - BigInt::one());
        let nonnegative = terms.mk_le(zero, n);
        let below_maximum = terms.mk_lt(n, maximum);
        let successor = terms.mk_add(vec![n, one]);
        let converted = terms.mk_int2bv(width, successor);
        let zero_bv = terms.mk_bitvec(BigInt::zero(), width);
        let one_bv = terms.mk_bitvec(BigInt::one(), width);

        let below_one = terms.mk_app(Symbol::named("bvult"), [converted, one_bv], Sort::Bool);
        authenticate_bv_lia_unsat_query(&terms, &[nonnegative, below_maximum, below_one], None)
            .unwrap_or_else(|error| {
                panic!("width-{width} converted successor cannot be below one: {error}")
            });

        let zero_below = terms.mk_app(Symbol::named("bvult"), [zero_bv, converted], Sort::Bool);
        let not_zero_below = terms.mk_not_raw(zero_below);
        authenticate_bv_lia_unsat_query(
            &terms,
            &[nonnegative, below_maximum, not_zero_below],
            None,
        )
        .unwrap_or_else(|error| {
            panic!("width-{width} zero must be below the converted successor: {error}")
        });
    }
}

/// A no-wrap-looking bound inside a satisfiable disjunction is not an
/// unconditional premise. Here `flag = true` and `e = 2^w` satisfy the bound
/// clause while `int2bv_w(e)` wraps to zero and satisfies the negated goal.
#[test]
fn disjunctive_pseudo_bound_does_not_authorize_no_wrap() {
    for width in [32_u32, 64] {
        let mut terms = TermStore::new();
        let source = terms.mk_var(format!("pseudo_bound_source_{width}"), Sort::Int);
        let flag = terms.mk_var(format!("pseudo_bound_flag_{width}"), Sort::Bool);
        let modulus_value = BigInt::one() << width;
        let modulus = terms.mk_int(modulus_value);
        let source_pin = terms.mk_eq(source, modulus);
        let below_modulus = terms.mk_lt(source, modulus);
        let pseudo_bound = terms.mk_or(vec![below_modulus, flag]);
        let converted = terms.mk_int2bv(width, source);
        let one_bv = terms.mk_bitvec(BigInt::one(), width);
        let ordered = terms.mk_app(Symbol::named("bvule"), [one_bv, converted], Sort::Bool);
        let negated_order = terms.mk_not_raw(ordered);

        let error = authenticate_bv_lia_unsat_query(
            &terms,
            &[source_pin, pseudo_bound, negated_order],
            None,
        )
        .expect_err("the flag makes the pseudo-bound clause true at the wrapping source value");
        assert!(
            error.is_capability_decline()
                || matches!(error, BvLiaUnsatAuthenticationError::Satisfiable),
            "width-{width} disjunctive pseudo-bound was unexpectedly authenticated: {error}"
        );
    }
}

/// The generated-theorem cap is a fail-closed lane boundary. Packing one more
/// relevant `int2bv` view into a single authored conjunction stays below the
/// public root/node caps, but must decline before any generated prefix reaches
/// propagation.
#[test]
fn residue_schema_cap_declines_before_propagation() {
    let mut terms = TermStore::new();
    let zero_bv = terms.mk_bitvec(BigInt::zero(), 32);
    let mut comparisons = Vec::with_capacity(MAX_RESIDUE_SCHEMAS + 1);
    for index in 0..=MAX_RESIDUE_SCHEMAS {
        let source = terms.mk_var(format!("schema_cap_source_{index}"), Sort::Int);
        let converted = terms.mk_int2bv(32, source);
        comparisons.push(terms.mk_app(Symbol::named("bvule"), [zero_bv, converted], Sort::Bool));
    }
    let root = terms.mk_and(comparisons);
    let error = authenticate_bv_lia_unsat_query(&terms, &[root], None)
        .expect_err("crossing the generated residue-schema cap must decline");
    assert!(error.is_capability_decline(), "unexpected result: {error}");
}

/// Signed order denotes the two's-complement value, not the unsigned view.
/// `x <s 0` is satisfiable for a 64-bit value with its sign bit set; treating
/// it as `bvult x 0` would unsoundly authenticate this query.
#[test]
fn signed_order_stays_outside_the_unsigned_interval_bridge() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("signed_order_value", Sort::bitvec(64));
    let zero = terms.mk_bitvec(BigInt::zero(), 64);
    let signed_negative = terms.mk_app(Symbol::named("bvslt"), [value, zero], Sort::Bool);
    let error = authenticate_bv_lia_unsat_query(&terms, &[signed_negative], None)
        .expect_err("a negative two's-complement witness satisfies signed x < 0");
    assert!(error.is_capability_decline());
}

/// Scalar projection of the byte-exact DEDUCTIVE_CHECKS length-frame shape: three
/// pushes derive length three, contradicting the negated `1 <=u int2bv(len)`
/// precondition at both target widths. The adjacent length-one/threshold-five
/// query is the captured satisfiable control.
#[test]
fn deductive_checks_length_chain_crosses_int2bv_unsigned_order() {
    for width in [32_u32, 64] {
        let mut terms = TermStore::new();
        let len2 = terms.mk_var(format!("fixture_len2_{width}"), Sort::Int);
        let len3 = terms.mk_var(format!("fixture_len3_{width}"), Sort::Int);
        let len4 = terms.mk_var(format!("fixture_len4_{width}"), Sort::Int);
        let one = terms.mk_int(BigInt::one());
        let len2_pin = terms.mk_eq(len2, one);
        let len2_successor = terms.mk_add(vec![len2, one]);
        let len3_pin = terms.mk_eq(len3, len2_successor);
        let len3_successor = terms.mk_add(vec![len3, one]);
        let len4_pin = terms.mk_eq(len4, len3_successor);
        let converted = terms.mk_int2bv(width, len4);
        let one_bv = terms.mk_bitvec(BigInt::one(), width);
        let required = terms.mk_app(Symbol::named("bvule"), [one_bv, converted], Sort::Bool);
        let negated_required = terms.mk_not_raw(required);

        authenticate_bv_lia_unsat_query(
            &terms,
            &[len2_pin, len3_pin, len4_pin, negated_required],
            None,
        )
        .unwrap_or_else(|error| {
            panic!("width-{width} DEDUCTIVE_CHECKS scalar length chain must authenticate: {error}")
        });

        let mut sat_terms = TermStore::new();
        let len = sat_terms.mk_var(format!("fixture_sat_len_{width}"), Sort::Int);
        let one = sat_terms.mk_int(BigInt::one());
        let pin = sat_terms.mk_eq(len, one);
        let converted = sat_terms.mk_int2bv(width, len);
        let five_bv = sat_terms.mk_bitvec(BigInt::from(5_u8), width);
        let five_at_most_len =
            sat_terms.mk_app(Symbol::named("bvule"), [five_bv, converted], Sort::Bool);
        let negated = sat_terms.mk_not_raw(five_at_most_len);
        let error = authenticate_bv_lia_unsat_query(&sat_terms, &[pin, negated], None)
            .expect_err("length one satisfies the captured negated five-at-most-length goal");
        assert!(
            error.is_capability_decline()
                || matches!(error, BvLiaUnsatAuthenticationError::Satisfiable),
            "width-{width} DEDUCTIVE_CHECKS satisfiable control was authenticated: {error}"
        );
    }
}

/// Positive coefficients tighten through FLOOR division: `3n <= 7` gives
/// `n <= 2`, which refutes `n >= 3`. The carrier is 64-bit so the enumerator
/// cannot reach it.
#[test]
fn positive_coefficient_bound_uses_floor_division() {
    let mut terms = TermStore::new();
    let index = terms.mk_var("floor_index", Sort::bitvec(64));
    let nat = terms.mk_bv2nat(index);
    let three = terms.mk_int(BigInt::from(3_u8));
    let seven = terms.mk_int(BigInt::from(7_u8));
    let tripled = terms.mk_mul(vec![three, nat]);
    let upper = terms.mk_le(tripled, seven);
    let lower = terms.mk_ge(nat, three);

    authenticate_bv_lia_unsat_query(&terms, &[upper, lower], None)
        .expect("3n <= 7 forces n <= 2 over the integers");

    // One larger on the right and `n = 3` is a witness: 9 <= 9.
    let nine = terms.mk_int(BigInt::from(9_u8));
    let attainable = terms.mk_le(tripled, nine);
    let error = authenticate_bv_lia_unsat_query(&terms, &[attainable, lower], None)
        .expect_err("n = 3 satisfies 3n <= 9");
    assert!(
        error.is_capability_decline()
            || matches!(error, BvLiaUnsatAuthenticationError::Satisfiable)
    );
}

/// Negative coefficients tighten through CEILING division: `-3v <= -7` gives
/// `v >= 3`, which refutes `v <= 2`. A floor here would wrongly derive
/// `v >= 2` and miss the contradiction; a truncating divide would derive
/// `v >= 2` as well.
#[test]
fn negative_coefficient_bound_uses_ceiling_division() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("ceiling_value", Sort::Int);
    let minus_three = terms.mk_int(BigInt::from(-3_i8));
    let minus_seven = terms.mk_int(BigInt::from(-7_i8));
    let scaled = terms.mk_mul(vec![minus_three, value]);
    let lower = terms.mk_le(scaled, minus_seven);
    let two = terms.mk_int(BigInt::from(2_u8));
    let upper = terms.mk_le(value, two);
    // A finite Int domain so the NEAR MISS is decided outright as satisfiable
    // rather than merely declined.
    let zero = terms.mk_int(BigInt::zero());
    let nonnegative = terms.mk_le(zero, value);

    authenticate_bv_lia_unsat_query(&terms, &[lower, upper, nonnegative], None)
        .expect("-3v <= -7 forces v >= 3 over the integers");

    // `v = 2` satisfies `-3v <= -6`, so the adjacent bound must not close.
    let minus_six = terms.mk_int(BigInt::from(-6_i8));
    let attainable = terms.mk_le(scaled, minus_six);
    let error = authenticate_bv_lia_unsat_query(&terms, &[attainable, upper, nonnegative], None)
        .expect_err("v = 2 satisfies -3v <= -6");
    assert!(matches!(error, BvLiaUnsatAuthenticationError::Satisfiable));
}

/// An implication is read as a clause, and an opaque Boolean literal still
/// participates in unit propagation.
#[test]
fn boolean_structure_drives_unit_propagation() {
    let mut terms = TermStore::new();
    let flag = terms.mk_var("propagation_flag", Sort::Bool);
    let index = terms.mk_var("propagation_index", Sort::bitvec(64));
    let nat = terms.mk_bv2nat(index);
    let modulus = terms.mk_int(BigInt::one() << 64_u32);
    let too_large = terms.mk_ge(nat, modulus);

    // flag, flag => nat >= 2^64. The consequent contradicts the carrier range.
    let implication = terms.mk_implies(flag, too_large);
    authenticate_bv_lia_unsat_query(&terms, &[flag, implication], None)
        .expect("the entailed consequent exceeds the 64-bit carrier maximum");

    // Without asserting the antecedent the implication is satisfied by
    // `flag = false`, so nothing may be derived from it.
    let error = authenticate_bv_lia_unsat_query(&terms, &[implication], None)
        .expect_err("flag = false satisfies the implication alone");
    assert!(error.is_capability_decline());
}

/// The carrier range is a property of the WIDTH, not of a variable, so it holds
/// for a computed operand too.
#[test]
fn carrier_range_applies_to_a_computed_bit_vector_operand() {
    let mut terms = TermStore::new();
    let left = terms.mk_var("computed_left", Sort::bitvec(64));
    let right = terms.mk_var("computed_right", Sort::bitvec(64));
    let sum = terms.mk_bvadd(vec![left, right]);
    let nat = terms.mk_bv2nat(sum);
    let modulus = terms.mk_int(BigInt::one() << 64_u32);
    let impossible = terms.mk_ge(nat, modulus);

    authenticate_bv_lia_unsat_query(&terms, &[impossible], None)
        .expect("bv2nat of a 64-bit sum is below 2^64");

    let maximum = terms.mk_int((BigInt::one() << 64_u32) - BigInt::one());
    let attainable = terms.mk_ge(nat, maximum);
    let error = authenticate_bv_lia_unsat_query(&terms, &[attainable], None)
        .expect_err("the carrier maximum itself is attainable");
    assert!(error.is_capability_decline());
}

/// `a mod d` for a positive literal divisor is confined to `[0, d-1]`, and the
/// adjacent value is not.
#[test]
fn positive_literal_modulus_bounds_its_residue() {
    let mut terms = TermStore::new();
    let source = terms.mk_var("residue_source", Sort::Int);
    let ten = terms.mk_int(BigInt::from(10_u8));
    let residue = terms.mk_mod(source, ten);
    let impossible = terms.mk_ge(residue, ten);
    authenticate_bv_lia_unsat_query(&terms, &[impossible], None)
        .expect("an integer residue modulo ten is at most nine");

    let nine = terms.mk_int(BigInt::from(9_u8));
    let attainable = terms.mk_ge(residue, nine);
    let error = authenticate_bv_lia_unsat_query(&terms, &[attainable], None)
        .expect_err("a residue of nine is attainable");
    assert!(
        error.is_capability_decline()
            || matches!(error, BvLiaUnsatAuthenticationError::Satisfiable)
    );
}

/// A non-linear product is kept as an opaque atom rather than mis-normalised,
/// so nothing is derived from it.
#[test]
fn non_linear_product_stays_opaque() {
    let mut terms = TermStore::new();
    let value = terms.mk_var("product_value", Sort::Int);
    let square = terms.mk_mul(vec![value, value]);
    let minus_one = terms.mk_int(BigInt::from(-1_i8));
    // `v * v <= -1` is unsatisfiable over the integers, but only a
    // multiplicative argument shows it. The interval lane must decline.
    let impossible = terms.mk_le(square, minus_one);
    let error = authenticate_bv_lia_unsat_query(&terms, &[impossible], None)
        .expect_err("the interval lane must not invent a sign argument");
    assert!(
        error.is_capability_decline()
            || matches!(error, BvLiaUnsatAuthenticationError::Satisfiable)
    );
}

// ---------------------------------------------------------------------------
// SIZE-AXIS PINS
//
// Every pin above varies a CONSTANT or a PREMISE, and none of them catches a
// clause harvest that ran out of budget: the failure is not in what the lane
// derives, it is in what it READ. Dropping a disjunct while flattening a
// clause makes the clause STRONGER than the source, so a satisfiable query can
// present itself as "every literal refuted" and be authenticated as UNSAT.
//
// These pins therefore vary the CLAUSE WIDTH and the NESTING DEPTH across the
// harvest's caps. Each comes with a control just inside the cap, so a fix that
// merely enlarges a constant moves the forging threshold instead of removing
// it and still fails here.
// ---------------------------------------------------------------------------

/// `(or (<= n -1) ... (<= n -k) (<= n 100))` over `n = bv2nat(idx)`, a 64-bit
/// carrier. Every `(<= n -i)` is refuted by the shape bound `n >= 0`; the final
/// `(<= n 100)` is satisfied by `n = 0`. SATISFIABLE for every `k`.
fn wide_satisfiable_clause(terms: &mut TermStore, tag: &str, width: usize) -> TermId {
    let index = terms.mk_var(format!("{tag}_idx"), Sort::bitvec(64));
    let nat = terms.mk_bv2nat(index);
    let mut disjuncts = Vec::with_capacity(width + 1);
    for i in 1..=width {
        let bound = terms.mk_int(-BigInt::from(i));
        disjuncts.push(terms.mk_le(nat, bound));
    }
    let hundred = terms.mk_int(BigInt::from(100_u8));
    disjuncts.push(terms.mk_le(nat, hundred));
    terms.mk_or(disjuncts)
}

/// WIDTH AXIS. `MAX_CLAUSE_LITERALS` is 4096; the satisfying disjunct is the
/// last one, so at 4096 refuted siblings it is exactly what a truncating
/// harvest drops. The control at 4090 keeps the same shape one literal-count
/// under the cap.
#[test]
fn a_clause_wider_than_the_literal_cap_is_never_authenticated() {
    for width in [8_usize, 4_090, 4_095, 4_096, 4_097, 6_000] {
        let mut terms = TermStore::new();
        let clause = wide_satisfiable_clause(&mut terms, &format!("wide_{width}"), width);
        let Err(error) = authenticate_bv_lia_unsat_query(&terms, &[clause], None) else {
            panic!("width-{width} satisfiable clause was AUTHENTICATED as UNSAT");
        };
        assert!(
            error.is_capability_decline()
                || matches!(error, BvLiaUnsatAuthenticationError::Satisfiable),
            "width-{width} clause must decline or be found satisfiable, got {error}"
        );
    }
}

/// `C_0 = (<= n 100)`, `C_i = C_{i-1} or (<= n -i)`, returned as the full chain
/// plus one anchor every `segment` rungs.
///
/// Two details are load-bearing.
///
/// * The disjunction is spelled by de Morgan rather than with `mk_or`, which
///   FLATTENS nested disjunctions and would collapse the chain into the width
///   axis above.
/// * The chain side carries a `not not` SPACER so it advances five levels per
///   rung while the literal side advances three. Without it the rung that
///   trips the harvest's depth cap is also the rung deep enough for
///   `linear_form` to give up on the comparison's constant, which leaves one
///   UNKNOWN literal in the clause and hides the forgery behind a (still
///   unsound) unit propagation.
///
/// The anchors do not strengthen the query — every `C_i` contains `C_0` as a
/// disjunct, so `n = 0` satisfies all of them and the conjunction is
/// SATISFIABLE. What they change is the SORT VALIDATOR's view: it walks the
/// DAG and `continue`s on an already-seen node, and roots are popped
/// last-first, so the shallowest anchor is expanded first and no validated
/// path exceeds `5 * segment` while the harvest still walks `5 * rungs`.
fn deep_satisfiable_chain(
    terms: &mut TermStore,
    tag: &str,
    rungs: usize,
    segment: usize,
) -> Vec<TermId> {
    let index = terms.mk_var(format!("{tag}_idx"), Sort::bitvec(64));
    let nat = terms.mk_bv2nat(index);
    let hundred = terms.mk_int(BigInt::from(100_u8));
    let mut current = terms.mk_le(nat, hundred);

    let mut anchors = Vec::new();
    for i in 1..=rungs {
        let bound = terms.mk_int(-BigInt::from(i));
        let refuted = terms.mk_le(nat, bound);
        let negated = terms.mk_not_raw(current);
        let spacer = terms.mk_not_raw(negated);
        let not_chain = terms.mk_not_raw(spacer);
        let not_refuted = terms.mk_not_raw(refuted);
        let conjunction = terms.mk_and(vec![not_chain, not_refuted]);
        current = terms.mk_not_raw(conjunction);
        if i % segment == 0 && i != rungs {
            anchors.push(current);
        }
    }
    let mut roots = vec![current];
    anchors.reverse();
    roots.extend(anchors);
    roots
}

/// DEPTH AXIS. The harvest recurses on the TREE with no dedup while the sort
/// validator that gates it walks the DAG, so a shared subterm can present the
/// harvest a walk past `MAX_TERM_DEPTH` that validation never sees. The
/// harvest advances five levels per rung from depth two, so it passes the cap
/// after rung 51: 51 rungs must behave like 45, and 52 must not start
/// authenticating.
#[test]
fn a_clause_deeper_than_the_term_depth_cap_is_never_authenticated() {
    for rungs in [45_usize, 50, 51, 52, 55, 80, 120] {
        let mut terms = TermStore::new();
        let roots = deep_satisfiable_chain(&mut terms, &format!("deep_{rungs}"), rungs, 40);
        let Err(error) = authenticate_bv_lia_unsat_query(&terms, &roots, None) else {
            panic!("{rungs}-rung satisfiable chain was AUTHENTICATED as UNSAT");
        };
        assert!(
            error.is_capability_decline()
                || matches!(error, BvLiaUnsatAuthenticationError::Satisfiable),
            "{rungs}-rung chain must decline or be found satisfiable, got {error}"
        );
    }
}
