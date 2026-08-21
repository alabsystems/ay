// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the width-independent interval refutation lane.
//!
//! The pins here come in pairs on purpose. Each accepting case is shadowed by a
//! near miss that is genuinely satisfiable and differs from it by one constant
//! or one dropped premise, so a widening of the lane fails the suite instead of
//! passing it.

use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::super::{authenticate_bv_lia_unsat_query, BvLiaUnsatAuthenticationError};

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
