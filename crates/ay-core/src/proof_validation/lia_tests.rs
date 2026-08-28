// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;

use super::lia::{
    lia_divisibility_equality_witness, validate_lia_theory_lemma, LiaValidationError,
};
use crate::{
    CuttingPlaneAnnotation, FarkasAnnotation, LiaAnnotation, ProofId, Sort, TermId, TermStore,
};

#[test]
fn test_bounds_gap_simple_contradiction() {
    // x <= 5 AND x >= 10 is contradictory
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);

    // Blocking clause: {NOT(x <= 5), NOT(x >= 10)}
    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_x_ge_10 = terms.mk_not(x_ge_10);
    let clause = vec![not_x_le_5, not_x_ge_10];

    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let lia = LiaAnnotation::BoundsGap;

    let result = validate_lia_theory_lemma(&terms, ProofId(0), &clause, Some(&farkas), &lia);
    assert!(result.is_ok(), "bounds gap should validate: {result:?}");
}

#[test]
fn test_bounds_gap_missing_farkas_returns_error() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let x_le_5 = terms.mk_le(x, five);
    let not_x_le_5 = terms.mk_not(x_le_5);
    let clause = vec![not_x_le_5];

    let lia = LiaAnnotation::BoundsGap;
    let result = validate_lia_theory_lemma(&terms, ProofId(0), &clause, None, &lia);
    assert!(
        matches!(
            result,
            Err(LiaValidationError::MissingFarkas { shape: "BoundsGap" })
        ),
        "expected MissingFarkas error, got: {result:?}"
    );
}

#[test]
fn rounded_integer_bounds_gap_accepts_strict_successor_conflict() {
    // Over Int, 0 < m rounds to m >= 1 while m - 1 < 0 rounds to m <= 0.
    // Their rational relaxations overlap on 0 < m < 1, so this must exercise
    // the integer BoundsGap validator rather than Farkas.
    let mut terms = TermStore::new();
    let m = terms.mk_var("m", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let positive = terms.mk_lt(zero, m);
    let predecessor = terms.mk_sub(vec![m, one]);
    let predecessor_negative = terms.mk_lt(predecessor, zero);
    let not_positive = terms.mk_not(positive);
    let not_predecessor_negative = terms.mk_not(predecessor_negative);
    let clause = vec![not_positive, not_predecessor_negative];

    assert!(super::lia::recognize_lia_bounds_gap(&terms, &clause));
    assert!(validate_lia_theory_lemma(
        &terms,
        ProofId(0),
        &clause,
        None,
        &LiaAnnotation::BoundsGap,
    )
    .is_ok());
}

#[test]
fn rounded_integer_bounds_gap_rejects_satisfiable_adjacent_interval() {
    // 0 <= m and m < 1 has the integer solution m=0. Rounded endpoints are
    // both zero, so accepting this pair would be a meta-false-PROVE.
    let mut terms = TermStore::new();
    let m = terms.mk_var("m", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let lower = terms.mk_le(zero, m);
    let upper = terms.mk_lt(m, one);
    let not_lower = terms.mk_not(lower);
    let not_upper = terms.mk_not(upper);
    let clause = vec![not_lower, not_upper];

    assert!(!super::lia::recognize_lia_bounds_gap(&terms, &clause));
    assert!(validate_lia_theory_lemma(
        &terms,
        ProofId(0),
        &clause,
        None,
        &LiaAnnotation::BoundsGap,
    )
    .is_err());
}

#[test]
fn rounded_integer_bounds_gap_rejects_real_relaxation() {
    // The exact TrustVC shape is satisfiable over Real at m=1/2. The sort gate
    // in the audited linear normalizer must therefore reject it.
    let mut terms = TermStore::new();
    let m = terms.mk_var("m", Sort::Real);
    let zero = terms.mk_rational(num_rational::BigRational::from(BigInt::from(0)));
    let one = terms.mk_rational(num_rational::BigRational::from(BigInt::from(1)));
    let positive = terms.mk_lt(zero, m);
    let predecessor = terms.mk_sub(vec![m, one]);
    let predecessor_negative = terms.mk_lt(predecessor, zero);
    let not_positive = terms.mk_not(positive);
    let not_predecessor_negative = terms.mk_not(predecessor_negative);
    let clause = vec![not_positive, not_predecessor_negative];

    assert!(!super::lia::recognize_lia_bounds_gap(&terms, &clause));
    assert!(validate_lia_theory_lemma(
        &terms,
        ProofId(0),
        &clause,
        None,
        &LiaAnnotation::BoundsGap,
    )
    .is_err());
}

#[test]
fn exact_integer_split_schemas_accept_producer_order_only() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let y_minus_one = terms.mk_sub(vec![y, one]);
    let y_plus_one = terms.mk_add(vec![y, one]);
    let upper = terms.mk_le(x, y_minus_one);
    let lower = terms.mk_le(y_plus_one, x);
    let equality = terms.mk_eq(x, y);

    // Without the equality guard these two branches deliberately exclude
    // x=y, so the two-literal cover is not itself a tautology.
    assert!(!super::lia::recognize_int_bounds_tautology(
        &terms,
        &[upper, lower]
    ));
    let not_upper = terms.mk_not(upper);
    let not_lower = terms.mk_not(lower);
    assert!(super::lia::recognize_int_bounds_tautology(
        &terms,
        &[not_upper, not_lower]
    ));
    assert!(super::lia::recognize_arith_disequality_split(
        &terms,
        &[upper, lower, equality]
    ));
    assert!(!super::lia::recognize_arith_disequality_split(
        &terms,
        &[lower, upper, equality]
    ));
}

#[test]
fn exact_real_disequality_split_rejects_branch_permutation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let forward = terms.mk_lt(x, y);
    let reverse = terms.mk_lt(y, x);
    let equality = terms.mk_eq(x, y);

    assert!(super::lia::recognize_arith_disequality_split(
        &terms,
        &[forward, reverse, equality]
    ));
    assert!(!super::lia::recognize_arith_disequality_split(
        &terms,
        &[reverse, forward, equality]
    ));
}

#[test]
fn test_divisibility_rejects_unverified_clause_fail_closed() {
    // META-FALSE-PROVE regression: a Divisibility lemma carries no Farkas
    // certificate, and the GCD reasoning is not implemented. The clause here is
    // `{not(x<=3)}` == `x>3` -- a SINGLE literal that is NOT a tautology. The old
    // checker accepted any non-empty Divisibility clause, so a forged
    // `TheoryLemma{Divisibility, clause:[not p]}` could resolve to the empty
    // clause and make check_proof_strict return UNSAT on a SAT formula. STRICT
    // mode now FAILS CLOSED: such a lemma is rejected.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let x_le_3 = terms.mk_le(x, three);
    let not_x_le_3 = terms.mk_not(x_le_3);

    let lia = LiaAnnotation::Divisibility;
    let result = validate_lia_theory_lemma(&terms, ProofId(0), &[not_x_le_3], None, &lia);
    assert!(
        matches!(
            result,
            Err(LiaValidationError::IntegerReasoningUnverified {
                shape: "Divisibility"
            })
        ),
        "divisibility must be rejected fail-closed (no verified GCD reasoning): {result:?}"
    );
}

#[test]
fn test_cutting_plane_forged_noncontradiction_rejected() {
    // META-FALSE-PROVE regression: a CuttingPlane lemma whose Farkas coefficients
    // are well-SHAPED (non-negative, right count) but do NOT combine to a
    // contradiction must be rejected. Old code shape-checked only and accepted it.
    // Clause `{not(x<=3)}` == `x>3` with coeff [1] is not a contradiction.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let x_le_3 = terms.mk_le(x, three);
    let not_x_le_3 = terms.mk_not(x_le_3);

    let cp = CuttingPlaneAnnotation {
        farkas: FarkasAnnotation::from_ints(&[1]),
        divisor: 2,
    };
    let lia = LiaAnnotation::CuttingPlane(cp);
    let result = validate_lia_theory_lemma(&terms, ProofId(0), &[not_x_le_3], None, &lia);
    assert!(
        result.is_err(),
        "cutting plane over a non-contradictory clause must be rejected: {result:?}"
    );
}

#[test]
fn test_divisibility_rejects_empty_clause() {
    let terms = TermStore::new();
    let lia = LiaAnnotation::Divisibility;
    let result = validate_lia_theory_lemma(&terms, ProofId(0), &[], None, &lia);
    assert!(result.is_err(), "divisibility should reject empty clause");
}

#[test]
fn test_cutting_plane_valid_divisor() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);
    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_x_ge_10 = terms.mk_not(x_ge_10);
    let clause = vec![not_x_le_5, not_x_ge_10];

    let cp = CuttingPlaneAnnotation {
        farkas: FarkasAnnotation::from_ints(&[1, 1]),
        divisor: 2,
    };
    let lia = LiaAnnotation::CuttingPlane(cp);

    let result = validate_lia_theory_lemma(&terms, ProofId(0), &clause, None, &lia);
    assert!(
        result.is_ok(),
        "cutting plane with valid divisor should pass: {result:?}"
    );
}

#[test]
fn test_cutting_plane_zero_divisor_rejected() {
    let terms = TermStore::new();
    let cp = CuttingPlaneAnnotation {
        farkas: FarkasAnnotation::from_ints(&[]),
        divisor: 0,
    };
    let lia = LiaAnnotation::CuttingPlane(cp);

    let result = validate_lia_theory_lemma(&terms, ProofId(0), &[], None, &lia);
    assert!(
        matches!(
            result,
            Err(LiaValidationError::InvalidDivisor { divisor: 0 })
        ),
        "expected InvalidDivisor, got: {result:?}"
    );
}

#[test]
fn test_cutting_plane_negative_divisor_rejected() {
    let terms = TermStore::new();
    let cp = CuttingPlaneAnnotation {
        farkas: FarkasAnnotation::from_ints(&[]),
        divisor: -3,
    };
    let lia = LiaAnnotation::CuttingPlane(cp);

    let result = validate_lia_theory_lemma(&terms, ProofId(0), &[], None, &lia);
    assert!(
        matches!(
            result,
            Err(LiaValidationError::InvalidDivisor { divisor: -3 })
        ),
        "expected InvalidDivisor, got: {result:?}"
    );
}

// ───────────────── Divisibility GCD validator: soundness tests ─────────────────
// `validate_divisibility` now performs the REAL GCD check. These tests pin down
// that it ACCEPTS exactly the integer-infeasible single negated equalities and
// REJECTS every non-tautology — the meta-false-PROVE guard.

fn div_lemma(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> Vec<TermId> {
    let eq = terms.mk_eq(lhs, rhs);
    vec![terms.mk_not(eq)]
}
fn check_div(terms: &TermStore, clause: &[TermId]) -> Result<(), LiaValidationError> {
    validate_lia_theory_lemma(
        terms,
        ProofId(0),
        clause,
        None,
        &LiaAnnotation::Divisibility,
    )
}

#[test]
fn divisibility_accepts_2y_eq_7() {
    // 2y = 7: gcd(2) = 2 ∤ 7 → no integer solution → tautology, ACCEPT.
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let seven = terms.mk_int(BigInt::from(7));
    let two_y = terms.mk_mul(vec![two, y]);
    let clause = div_lemma(&mut terms, two_y, seven);
    assert!(
        check_div(&terms, &clause).is_ok(),
        "2y=7 is integer-infeasible"
    );
}

#[test]
fn divisibility_witness_recovers_exact_adjacent_lattice_values() {
    // `mk_eq` canonically orders this equality as `7 = 3x + 6y`, so the
    // checked difference ranges over residue class 1 (mod 3), whose values
    // adjacent to zero are -2 and 1. The wire lowering must recover these
    // exact values from the same checked clause, not approximate a bound.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let six = terms.mk_int(BigInt::from(6));
    let seven = terms.mk_int(BigInt::from(7));
    let three_x = terms.mk_mul(vec![three, x]);
    let six_y = terms.mk_mul(vec![six, y]);
    let lhs = terms.mk_add(vec![three_x, six_y]);
    let clause = div_lemma(&mut terms, lhs, seven);

    let witness = lia_divisibility_equality_witness(&terms, &clause)
        .expect("the validated unit divisibility lemma has a lattice witness");
    assert_eq!(witness.lhs, seven);
    assert_eq!(witness.rhs, lhs);
    assert_eq!(witness.lower, BigInt::from(-2));
    assert_eq!(witness.upper, BigInt::from(1));
}

#[test]
fn divisibility_witness_declines_non_unit_and_satisfiable_shapes() {
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let eight = terms.mk_int(BigInt::from(8));
    let two_y = terms.mk_mul(vec![two, y]);
    let satisfiable = div_lemma(&mut terms, two_y, eight);
    assert!(lia_divisibility_equality_witness(&terms, &satisfiable).is_none());

    let seven = terms.mk_int(BigInt::from(7));
    let mut non_unit = div_lemma(&mut terms, two_y, seven);
    let z = terms.mk_var("z", Sort::Int);
    let z_eq_two = terms.mk_eq(z, two);
    non_unit.push(terms.mk_not(z_eq_two));
    assert!(lia_divisibility_equality_witness(&terms, &non_unit).is_none());
}

#[test]
fn divisibility_rejects_satisfiable_2y_eq_8() {
    // 2y = 8: gcd(2) | 8 (y = 4) → SATISFIABLE → must REJECT (else false-UNSAT).
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let eight = terms.mk_int(BigInt::from(8));
    let two_y = terms.mk_mul(vec![two, y]);
    let clause = div_lemma(&mut terms, two_y, eight);
    assert!(
        check_div(&terms, &clause).is_err(),
        "2y=8 is satisfiable (y=4)"
    );
}

#[test]
fn divisibility_rejects_real_variable() {
    // 2y = 7 with y : Real is RATIONALLY solvable (y = 3.5) → must REJECT.
    // (The integer-sort guard is the key false-UNSAT prevention.) The coefficient
    // is a Real `2.0` so the product is well-sorted.
    use num_rational::BigRational;
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Real);
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let seven = terms.mk_rational(BigRational::from(BigInt::from(7)));
    let two_y = terms.mk_mul(vec![two, y]);
    let clause = div_lemma(&mut terms, two_y, seven);
    assert!(
        check_div(&terms, &clause).is_err(),
        "real y makes 2y=7 solvable"
    );
}

#[test]
fn divisibility_rejects_nonlinear_term() {
    // (* x y) = 7 : the product is an opaque atom (coeff 1 → gcd 1 | 7) → REJECT.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let seven = terms.mk_int(BigInt::from(7));
    let xy = terms.mk_mul(vec![x, y]);
    let clause = div_lemma(&mut terms, xy, seven);
    assert!(
        check_div(&terms, &clause).is_err(),
        "nonlinear factor must not certify"
    );
}

#[test]
fn divisibility_accepts_3x_plus_6y_eq_7() {
    // 3x + 6y = 7: gcd(3,6) = 3 ∤ 7 → tautology, ACCEPT.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let six = terms.mk_int(BigInt::from(6));
    let seven = terms.mk_int(BigInt::from(7));
    let tx = terms.mk_mul(vec![three, x]);
    let sy = terms.mk_mul(vec![six, y]);
    let sum = terms.mk_add(vec![tx, sy]);
    let clause = div_lemma(&mut terms, sum, seven);
    assert!(check_div(&terms, &clause).is_ok(), "gcd(3,6)=3 ∤ 7");
}

#[test]
fn divisibility_rejects_satisfiable_2x_plus_4y_eq_6() {
    // 2x + 4y = 6: gcd(2,4) = 2 | 6 (x=3,y=0) → SATISFIABLE → REJECT.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let four = terms.mk_int(BigInt::from(4));
    let six = terms.mk_int(BigInt::from(6));
    let tx = terms.mk_mul(vec![two, x]);
    let fy = terms.mk_mul(vec![four, y]);
    let sum = terms.mk_add(vec![tx, fy]);
    let clause = div_lemma(&mut terms, sum, six);
    assert!(
        check_div(&terms, &clause).is_err(),
        "2x+4y=6 is satisfiable"
    );
}

// (The all-constant case `7 ≠ 8` cannot be constructed as a test: `mk_eq` folds a
// constant equality to a Boolean literal, so the solver never emits it as a
// Divisibility lemma. The no-variable branch in the validator is defensive.)

#[test]
fn divisibility_rejects_equal_constants() {
    // 7 = 7 is TRUE, so (not (= 7 7)) is NOT a tautology → REJECT.
    let mut terms = TermStore::new();
    let seven = terms.mk_int(BigInt::from(7));
    let seven2 = terms.mk_int(BigInt::from(7));
    let clause = div_lemma(&mut terms, seven, seven2);
    assert!(check_div(&terms, &clause).is_err(), "7=7 holds");
}

#[test]
fn divisibility_rejects_multi_literal_clause() {
    // A divisibility tautology is a SINGLE negated equality; a 2-literal clause
    // (which could be a real disjunction) must not be certified by gcd alone.
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let seven = terms.mk_int(BigInt::from(7));
    let two_y = terms.mk_mul(vec![two, y]);
    let mut clause = div_lemma(&mut terms, two_y, seven);
    let z = terms.mk_var("z", Sort::Int);
    let ze = terms.mk_eq(z, two);
    clause.push(terms.mk_not(ze));
    assert!(
        check_div(&terms, &clause).is_err(),
        "multi-literal must reject"
    );
}

#[test]
fn divisibility_rejects_positive_equality() {
    // A positive equality (not a negated one) is not a divisibility tautology.
    let mut terms = TermStore::new();
    let y = terms.mk_var("y", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let seven = terms.mk_int(BigInt::from(7));
    let two_y = terms.mk_mul(vec![two, y]);
    let eq = terms.mk_eq(two_y, seven);
    assert!(
        check_div(&terms, &[eq]).is_err(),
        "positive equality must reject"
    );
}

// ─────────── Bounded-gcd CUT validator (Divisibility, 2-bound form) ───────────
// `kl ≤ L ≤ ku` with L over multiples of gcd(coeffs): infeasible iff no multiple
// of g in [kl,ku]. These pin down that it ACCEPTS exactly the genuine integer
// cuts and REJECTS every feasible/ill-formed case (the meta-false-PROVE guard).

fn cut_lemma(terms: &mut TermStore, l: TermId, lo: i64, hi: i64) -> Vec<TermId> {
    let klo = terms.mk_int(BigInt::from(lo));
    let khi = terms.mk_int(BigInt::from(hi));
    let le = terms.mk_le(l, khi); // L ≤ hi
    let ge = terms.mk_ge(l, klo); // L ≥ lo
    vec![terms.mk_not(le), terms.mk_not(ge)]
}

#[test]
fn cut_accepts_3x_in_1_2() {
    // 3x ∈ [1,2]: no multiple of 3 in [1,2] → integer-infeasible, ACCEPT.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let tx = terms.mk_mul(vec![three, x]);
    let clause = cut_lemma(&mut terms, tx, 1, 2);
    assert!(
        check_div(&terms, &clause).is_ok(),
        "no multiple of 3 in [1,2]"
    );
}

#[test]
fn cut_accepts_3x_in_4_5() {
    // 3x ∈ [4,5]: multiples of 3 are 3,6 — none in [4,5] → ACCEPT.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let tx = terms.mk_mul(vec![three, x]);
    let clause = cut_lemma(&mut terms, tx, 4, 5);
    assert!(
        check_div(&terms, &clause).is_ok(),
        "no multiple of 3 in [4,5]"
    );
}

#[test]
fn cut_rejects_feasible_3x_in_1_3() {
    // 3x ∈ [1,3]: x=1 ⟹ 3x=3 ∈ [1,3] → FEASIBLE → must REJECT (else false-UNSAT).
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let tx = terms.mk_mul(vec![three, x]);
    let clause = cut_lemma(&mut terms, tx, 1, 3);
    assert!(
        check_div(&terms, &clause).is_err(),
        "x=1 gives 3x=3 ∈ [1,3]"
    );
}

#[test]
fn cut_rejects_feasible_3x_in_4_6() {
    // 3x ∈ [4,6]: x=2 ⟹ 3x=6 ∈ [4,6] → FEASIBLE → REJECT.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let tx = terms.mk_mul(vec![three, x]);
    let clause = cut_lemma(&mut terms, tx, 4, 6);
    assert!(
        check_div(&terms, &clause).is_err(),
        "x=2 gives 3x=6 ∈ [4,6]"
    );
}

#[test]
fn cut_rejects_real_variable() {
    // 3x ∈ [1,2] with x : Real is rationally solvable (x=1/2) → REJECT (sort guard).
    use num_rational::BigRational;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let tx = terms.mk_mul(vec![three, x]);
    // Bounds must be Real-sorted to match `tx` (mk_le asserts same sort).
    let lo = terms.mk_rational(BigRational::from(BigInt::from(1)));
    let hi = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let le = terms.mk_le(tx, hi);
    let ge = terms.mk_ge(tx, lo);
    let clause = vec![terms.mk_not(le), terms.mk_not(ge)];
    assert!(
        check_div(&terms, &clause).is_err(),
        "real x makes 3x∈[1,2] solvable"
    );
}

#[test]
fn cut_rejects_empty_range_bounds_gap() {
    // 3x ∈ [3,2] (lo > hi): an EMPTY range (plain bounds gap), left to the Farkas
    // path — the cut validator restricts to non-empty ranges, so REJECT here.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let tx = terms.mk_mul(vec![three, x]);
    let clause = cut_lemma(&mut terms, tx, 3, 2);
    assert!(
        check_div(&terms, &clause).is_err(),
        "empty range is a bounds gap, not a cut"
    );
}

#[test]
fn cut_rejects_two_upper_bounds() {
    // Two UPPER bounds (no lower) — not a bounded range → REJECT.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let two = terms.mk_int(BigInt::from(2));
    let one = terms.mk_int(BigInt::from(1));
    let tx = terms.mk_mul(vec![three, x]);
    let le1 = terms.mk_le(tx, two);
    let le2 = terms.mk_le(tx, one);
    let clause = vec![terms.mk_not(le1), terms.mk_not(le2)];
    assert!(
        check_div(&terms, &clause).is_err(),
        "two uppers is not a cut"
    );
}

#[test]
fn cut_accepts_multivar_2x_2y_in_1_1() {
    // 2x+2y ∈ [1,1] (= 2(x+y)=1): gcd 2 ∤ 1 → ACCEPT.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let tx = terms.mk_mul(vec![two, x]);
    let ty = terms.mk_mul(vec![two, y]);
    let sum = terms.mk_add(vec![tx, ty]);
    let clause = cut_lemma(&mut terms, sum, 1, 1);
    assert!(check_div(&terms, &clause).is_ok(), "2(x+y)=1 infeasible");
}

#[test]
fn cut_rejects_feasible_multivar_2x_2y_in_1_2() {
    // 2x+2y ∈ [1,2]: x+y=1 ⟹ 2(x+y)=2 ∈ [1,2] → FEASIBLE → REJECT.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let tx = terms.mk_mul(vec![two, x]);
    let ty = terms.mk_mul(vec![two, y]);
    let sum = terms.mk_add(vec![tx, ty]);
    let clause = cut_lemma(&mut terms, sum, 1, 2);
    assert!(
        check_div(&terms, &clause).is_err(),
        "2(x+y)=2 ∈ [1,2] feasible"
    );
}

// ---- LinearIdentity (positive equality tautology) validation ----

/// Build a RAW `(= L R)` clause (via `mk_app`, no folding) and validate it as a
/// `LinearIdentity` lemma.
fn check_identity(terms: &TermStore, eq: TermId) -> Result<(), LiaValidationError> {
    validate_lia_theory_lemma(
        terms,
        ProofId(0),
        &[eq],
        None,
        &LiaAnnotation::LinearIdentity,
    )
}

/// Raw `(op a b)` application — bypasses the simplifying `mk_*` builders so the
/// validator sees the surface structure (as the reconstruction emits it).
fn raw2(terms: &mut TermStore, op: &str, a: TermId, b: TermId, sort: Sort) -> TermId {
    terms.mk_app(crate::Symbol::named(op), vec![a, b], sort)
}

#[test]
fn linear_identity_accepts_mul_zero_and_mul_one() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    // (= (* x 0) 0) — identically zero on both sides.
    let mul0 = raw2(&mut terms, "*", x, zero, Sort::Int);
    let eq0 = raw2(&mut terms, "=", mul0, zero, Sort::Bool);
    assert!(
        check_identity(&terms, eq0).is_ok(),
        "(* x 0) = 0 is an identity"
    );
    // (= (* x 1) x) — multiply by one.
    let mul1 = raw2(&mut terms, "*", x, one, Sort::Int);
    let eq1 = raw2(&mut terms, "=", mul1, x, Sort::Bool);
    assert!(
        check_identity(&terms, eq1).is_ok(),
        "(* x 1) = x is an identity"
    );
}

#[test]
fn linear_identity_rejects_nonidentities() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let two = terms.mk_int(BigInt::from(2));
    let five = terms.mk_int(BigInt::from(5));
    // (= (* x y) 0): false unless x=0 or y=0 — nonlinear atom, surviving coeff 1.
    let mulxy = raw2(&mut terms, "*", x, y, Sort::Int);
    let bad0 = raw2(&mut terms, "=", mulxy, zero, Sort::Bool);
    assert!(
        check_identity(&terms, bad0).is_err(),
        "(* x y) = 0 is NOT an identity"
    );
    // (= (* x 2) x): false unless x=0 — difference `x`.
    let mulx2 = raw2(&mut terms, "*", x, two, Sort::Int);
    let bad1 = raw2(&mut terms, "=", mulx2, x, Sort::Bool);
    assert!(
        check_identity(&terms, bad1).is_err(),
        "2x = x is NOT an identity"
    );
    // (= x 5): not a tautology — difference `x - 5`.
    let bad2 = raw2(&mut terms, "=", x, five, Sort::Bool);
    assert!(
        check_identity(&terms, bad2).is_err(),
        "x = 5 is NOT an identity"
    );
}

// ---- Euclidean `mod` constant-range validation ----

fn mod_range_clause(
    terms: &mut TermStore,
    dividend: TermId,
    divisor: TermId,
    remainder: TermId,
) -> Vec<TermId> {
    let modulus = raw2(terms, "mod", dividend, divisor, Sort::Int);
    let equality = raw2(terms, "=", modulus, remainder, Sort::Bool);
    vec![terms.mk_not_raw(equality)]
}

#[test]
fn mod_range_accepts_exact_out_of_range_constants() {
    use super::lia::validate_lia_mod_range;

    let mut terms = TermStore::new();
    let x = terms.mk_var("mod-x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let neg_three = terms.mk_int(BigInt::from(-3));
    let four = terms.mk_int(BigInt::from(4));
    let neg_one = terms.mk_int(BigInt::from(-1));

    let above = mod_range_clause(&mut terms, x, three, four);
    assert!(
        validate_lia_mod_range(&terms, &above).is_ok(),
        "(mod x 3) cannot equal 4"
    );
    let below = mod_range_clause(&mut terms, x, neg_three, neg_one);
    assert!(
        validate_lia_mod_range(&terms, &below).is_ok(),
        "Euclidean (mod x -3) cannot equal -1"
    );
}

#[test]
fn mod_range_rejects_every_non_theorem_shape() {
    use super::lia::validate_lia_mod_range;

    let mut terms = TermStore::new();
    let x = terms.mk_var("mod-x", Sort::Int);
    let d = terms.mk_var("mod-d", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));

    let in_range = mod_range_clause(&mut terms, x, three, two);
    assert!(
        validate_lia_mod_range(&terms, &in_range).is_err(),
        "(mod x 3) = 2 is satisfiable"
    );
    let zero_divisor = mod_range_clause(&mut terms, x, zero, two);
    assert!(
        validate_lia_mod_range(&terms, &zero_divisor).is_err(),
        "mod by zero has no Euclidean range certificate"
    );
    let variable_divisor = mod_range_clause(&mut terms, x, d, three);
    assert!(
        validate_lia_mod_range(&terms, &variable_divisor).is_err(),
        "a variable divisor is outside the certified lane"
    );

    let modulus = raw2(&mut terms, "mod", x, three, Sort::Int);
    let positive_equality = raw2(&mut terms, "=", modulus, two, Sort::Bool);
    assert!(
        validate_lia_mod_range(&terms, &[positive_equality]).is_err(),
        "the theorem must have negated-equality polarity"
    );
}

// ─── Guarded disequality split: the POSITIVE-INTEGER-SCALED guard ───────────
//
// `recognize_arith_disequality_split` historically required the guard's
// canonical linear form to be IDENTICAL to the branch form (`k = 1`). The
// producer in `split_incremental` emits the guard as the asserted
// disequality's own equality, which on the div/mod-elimination route is scaled
// — `q <= -1 ∨ q >= 1 ∨ 2q+1 = 4q+1`. These tests pin the extension AND the
// exact boundary it must not cross.

/// Build `(op a b)` with no builder-side simplification, so the tested clause
/// is byte-for-byte the shape the producer emits.
fn split_atom(terms: &mut TermStore, op: &str, a: TermId, b: TermId, sort: Sort) -> TermId {
    terms.mk_app(crate::Symbol::named(op), vec![a, b], sort)
}

/// `(+ (* v coeff) constant)`, unsimplified.
fn affine(terms: &mut TermStore, v: TermId, coeff: i64, constant: i64) -> TermId {
    let c = terms.mk_int(BigInt::from(coeff));
    let k = terms.mk_int(BigInt::from(constant));
    let scaled = split_atom(terms, "*", v, c, Sort::Int);
    split_atom(terms, "+", scaled, k, Sort::Int)
}

/// `(cl (<= v upper) (<= lower v) (= (+ (* v gc) ge) (+ (* v gf) gg)))`.
fn scaled_split_clause(
    terms: &mut TermStore,
    v: TermId,
    bounds: (i64, i64),
    guard: (i64, i64, i64, i64),
) -> Vec<TermId> {
    let (upper, lower) = bounds;
    let (gc, ge, gf, gg) = guard;
    let upper_const = terms.mk_int(BigInt::from(upper));
    let lower_const = terms.mk_int(BigInt::from(lower));
    let first = split_atom(terms, "<=", v, upper_const, Sort::Bool);
    let second = split_atom(terms, "<=", lower_const, v, Sort::Bool);
    let lhs = affine(terms, v, gc, ge);
    let rhs = affine(terms, v, gf, gg);
    let guard = split_atom(terms, "=", lhs, rhs, Sort::Bool);
    vec![first, second, guard]
}

#[test]
fn scaled_guard_accepts_the_benchmark_clause_and_reports_its_multiplier() {
    // The exact dillig12_m clause: `q <= -1 ∨ q >= 1 ∨ 2q+1 = 4q+1`.
    // Branch form `(q, T=0)`; the guard canonicalizes to `2q = 0`, so `k = 2`
    // and `T_g = 2·0`. Affine on BOTH sides — the constant is absorbed into
    // the canonical TARGET, which is exactly why `T_g = k·T_b` IS the whole
    // constant-scaling requirement.
    let mut terms = TermStore::new();
    let q = terms.mk_var("_mod_q_0", Sort::Int);
    let clause = scaled_split_clause(&mut terms, q, (-1, 1), (2, 1, 4, 1));
    assert!(super::lia::recognize_arith_disequality_split(
        &terms, &clause
    ));
    assert_eq!(
        super::lia::arith_disequality_split_guard_multiplier(&terms, &clause),
        Some(BigInt::from(2))
    );
    // The emission-side narrowing: a scaled guard is NOT primitive, so the
    // Alethe printer must not lower it through the guard's own operands.
    assert!(!super::lia::arith_disequality_split_has_primitive_guard(
        &terms, &clause
    ));
}

#[test]
fn scaled_guard_accepts_primitive_control_unchanged() {
    // The `k = 1` control from the same probe: `q <= -1 ∨ q >= 1 ∨ q = 0`.
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let minus_one = terms.mk_int(BigInt::from(-1));
    let one = terms.mk_int(BigInt::from(1));
    let first = split_atom(&mut terms, "<=", q, minus_one, Sort::Bool);
    let second = split_atom(&mut terms, "<=", one, q, Sort::Bool);
    let guard = split_atom(&mut terms, "=", q, zero, Sort::Bool);
    let clause = vec![first, second, guard];
    assert_eq!(
        super::lia::arith_disequality_split_guard_multiplier(&terms, &clause),
        Some(BigInt::from(1))
    );
    assert!(super::lia::arith_disequality_split_has_primitive_guard(
        &terms, &clause
    ));
}

#[test]
fn scaled_guard_accepts_a_nonzero_branch_target() {
    // `q <= 0 ∨ q >= 2 ∨ 3q + 1 = 4` — branch target `T_b = 1`, guard
    // canonical `3q = 3 = 3·T_b`. The constant MUST scale with the
    // coefficients; this is the case a homogeneous-only implementation would
    // pass for the wrong reason.
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let clause = scaled_split_clause(&mut terms, q, (0, 2), (3, 1, 0, 4));
    assert_eq!(
        super::lia::arith_disequality_split_guard_multiplier(&terms, &clause),
        Some(BigInt::from(3))
    );
}

#[test]
fn scaled_guard_rejects_a_target_that_does_not_scale() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    // ADVERSARIAL: guard scaled by 2, target left at `T_b = 1`.
    // `q <= 0 ∨ q >= 2 ∨ 2q = 1` is FALSE at q = 1.
    let guard_scaled_only = scaled_split_clause(&mut terms, q, (0, 2), (2, 0, 0, 1));
    assert!(!super::lia::recognize_arith_disequality_split(
        &terms,
        &guard_scaled_only
    ));
    // ADVERSARIAL: target scaled by 2, coefficients left at `k = 1`.
    // `q <= 0 ∨ q >= 2 ∨ q = 2` is FALSE at q = 1.
    let target_scaled_only = scaled_split_clause(&mut terms, q, (0, 2), (1, 0, 0, 2));
    assert!(!super::lia::recognize_arith_disequality_split(
        &terms,
        &target_scaled_only
    ));
    // ADVERSARIAL: `2q = 1` against branch target 0.
    // `q <= -1 ∨ q >= 1 ∨ 2q = 1` is FALSE at q = 0.
    let unsolvable_guard = scaled_split_clause(&mut terms, q, (-1, 1), (2, 0, 0, 1));
    assert!(!super::lia::recognize_arith_disequality_split(
        &terms,
        &unsolvable_guard
    ));
}

#[test]
fn scaled_guard_rejects_zero_and_non_integer_multipliers() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    // ADVERSARIAL k = 0: the guard's canonical form collapses to `0 = 0`, so
    // it carries no relation to the branches at all. Rejected — accepting it
    // would make the multiplier search unable to tell a degenerate guard from
    // a genuinely scaled one.
    let zero_scale = scaled_split_clause(&mut terms, q, (-1, 1), (0, 0, 0, 0));
    assert!(!super::lia::recognize_arith_disequality_split(
        &terms,
        &zero_scale
    ));
    // ADVERSARIAL non-integer k: branches on `2q`, guard on `3q` (`k = 3/2`).
    // Fail-closed — this clause happens to be valid and is simply not
    // certified by this rule.
    let two = terms.mk_int(BigInt::from(2));
    let minus_one = terms.mk_int(BigInt::from(-1));
    let one = terms.mk_int(BigInt::from(1));
    let two_q = split_atom(&mut terms, "*", q, two, Sort::Int);
    let first = split_atom(&mut terms, "<=", two_q, minus_one, Sort::Bool);
    let second = split_atom(&mut terms, "<=", one, two_q, Sort::Bool);
    let three = terms.mk_int(BigInt::from(3));
    let zero = terms.mk_int(BigInt::from(0));
    let three_q = split_atom(&mut terms, "*", q, three, Sort::Int);
    let guard = split_atom(&mut terms, "=", three_q, zero, Sort::Bool);
    assert!(!super::lia::recognize_arith_disequality_split(
        &terms,
        &[first, second, guard]
    ));
}

#[test]
fn scaled_guard_rejects_mismatched_variables() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let minus_one = terms.mk_int(BigInt::from(-1));
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));
    let two = terms.mk_int(BigInt::from(2));
    let first = split_atom(&mut terms, "<=", q, minus_one, Sort::Bool);
    let second = split_atom(&mut terms, "<=", one, q, Sort::Bool);
    // ADVERSARIAL: the guard scales a DIFFERENT variable.
    // `q <= -1 ∨ q >= 1 ∨ 2r = 0` is FALSE at q = 0, r = 1.
    let two_r = split_atom(&mut terms, "*", r, two, Sort::Int);
    let other_var = split_atom(&mut terms, "=", two_r, zero, Sort::Bool);
    assert!(!super::lia::recognize_arith_disequality_split(
        &terms,
        &[first, second, other_var]
    ));
    // ADVERSARIAL: the guard carries an EXTRA variable.
    // `q <= -1 ∨ q >= 1 ∨ 2q + 2r = 0` is FALSE at q = 0, r = 1.
    let two_q = split_atom(&mut terms, "*", q, two, Sort::Int);
    let sum = split_atom(&mut terms, "+", two_q, two_r, Sort::Int);
    let extra_var = split_atom(&mut terms, "=", sum, zero, Sort::Bool);
    assert!(!super::lia::recognize_arith_disequality_split(
        &terms,
        &[first, second, extra_var]
    ));
    // ADVERSARIAL: the two BRANCHES bracket different forms.
    // `q <= -1 ∨ r >= 1 ∨ 2q = 0` is FALSE at q = 1, r = 0.
    let r_lower = split_atom(&mut terms, "<=", one, r, Sort::Bool);
    let scaled_guard = split_atom(&mut terms, "=", two_q, zero, Sort::Bool);
    assert!(!super::lia::recognize_arith_disequality_split(
        &terms,
        &[first, r_lower, scaled_guard]
    ));
}

#[test]
fn scaled_guard_rejects_a_gap_wider_than_one_value() {
    // ADVERSARIAL: `q <= -2 ∨ q >= 1 ∨ 2q = 0` is FALSE at q = -1 — the
    // branches no longer force `C_b = T_b`, so no multiplier can rescue it.
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let clause = scaled_split_clause(&mut terms, q, (-2, 1), (2, 0, 0, 0));
    assert!(!super::lia::recognize_arith_disequality_split(
        &terms, &clause
    ));
}

#[test]
fn scaled_guard_stays_out_of_the_real_arm() {
    // ADVERSARIAL: over Real the branches do NOT force `C_b = T_b`
    // (`T_b - 1 < x < T_b + 1` has non-integer solutions), so the scaling
    // argument is invalid there. The Real arm is untouched and matches only
    // the exact strict-order pair on the guard's own operands.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let two = terms.mk_rational(num_rational::BigRational::from(BigInt::from(2)));
    let forward = split_atom(&mut terms, "<", x, y, Sort::Bool);
    let reverse = split_atom(&mut terms, "<", y, x, Sort::Bool);
    let two_x = split_atom(&mut terms, "*", x, two, Sort::Real);
    let two_y = split_atom(&mut terms, "*", y, two, Sort::Real);
    let scaled_guard = split_atom(&mut terms, "=", two_x, two_y, Sort::Bool);
    assert!(!super::lia::recognize_arith_disequality_split(
        &terms,
        &[forward, reverse, scaled_guard]
    ));
}

#[test]
fn positive_integer_scale_rejects_zero_negative_and_fractional() {
    use std::collections::BTreeMap;
    let base_var = TermId(7);
    let other_var = TermId(9);
    let base: BTreeMap<TermId, BigInt> = [(base_var, BigInt::from(2))].into_iter().collect();
    let scale = |c: i64| -> BTreeMap<TermId, BigInt> {
        [(base_var, BigInt::from(c))].into_iter().collect()
    };

    // The canonical maps `int_linear_diff` produces can never SPELL a zero or
    // negative multiplier (`LinearExpr` drops a coefficient the moment it
    // reaches zero, and both callers normalize the leading coefficient
    // positive), so these branches are pinned at the helper — the only place
    // they are reachable at all.
    assert_eq!(
        super::lia::positive_integer_scale(&base, &scale(0)),
        None,
        "k = 0 must be rejected"
    );
    assert_eq!(
        super::lia::positive_integer_scale(&base, &scale(-4)),
        None,
        "k < 0 must be rejected"
    );
    assert_eq!(
        super::lia::positive_integer_scale(&base, &scale(3)),
        None,
        "k = 3/2 is not an integer and must be rejected"
    );
    assert_eq!(
        super::lia::positive_integer_scale(&base, &scale(6)),
        Some(BigInt::from(3))
    );
    // A different variable at the same arity must not scale.
    let renamed: BTreeMap<TermId, BigInt> = [(other_var, BigInt::from(4))].into_iter().collect();
    assert_eq!(super::lia::positive_integer_scale(&base, &renamed), None);
    // A pivot that scales while a sibling does not.
    let two_var_base: BTreeMap<TermId, BigInt> =
        [(base_var, BigInt::from(2)), (other_var, BigInt::from(3))]
            .into_iter()
            .collect();
    let inconsistent: BTreeMap<TermId, BigInt> =
        [(base_var, BigInt::from(4)), (other_var, BigInt::from(7))]
            .into_iter()
            .collect();
    assert_eq!(
        super::lia::positive_integer_scale(&two_var_base, &inconsistent),
        None
    );
    let empty: BTreeMap<TermId, BigInt> = BTreeMap::new();
    assert_eq!(super::lia::positive_integer_scale(&empty, &empty), None);
}

#[test]
fn scaled_guard_accepts_only_genuine_integer_tautologies() {
    // EXHAUSTIVE ADVERSARIAL SWEEP. Every clause of the split's own shape
    //     `q <= upper ∨ lower <= q ∨ (gc·q + ge = gf·q + gg)`
    // over a small coefficient box is offered to the recognizer, and every
    // ACCEPT is independently re-evaluated at 81 integer points. An accept
    // that is false anywhere is a meta-false-PROVE, so this is the test that
    // catches a mis-stated multiplier rule.
    let mut terms = TermStore::new();
    let q = terms.mk_var("sweep-q", Sort::Int);
    let range = -2_i64..=2;
    let mut accepted = 0_u32;
    for upper in range.clone() {
        for lower in range.clone() {
            for gc in range.clone() {
                for ge in range.clone() {
                    for gf in range.clone() {
                        for gg in range.clone() {
                            let clause = scaled_split_clause(
                                &mut terms,
                                q,
                                (upper, lower),
                                (gc, ge, gf, gg),
                            );
                            if !super::lia::recognize_arith_disequality_split(&terms, &clause) {
                                continue;
                            }
                            accepted += 1;
                            for value in -40_i64..=40 {
                                let holds = value <= upper
                                    || lower <= value
                                    || gc * value + ge == gf * value + gg;
                                assert!(
                                    holds,
                                    "ACCEPTED a non-tautology: \
                                     q <= {upper} | {lower} <= q | {gc}q + {ge} = {gf}q + {gg} \
                                     is FALSE at q = {value}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
    // Guard against the sweep silently accepting nothing, which would make the
    // assertion above vacuous.
    assert!(
        accepted >= 20,
        "sweep degenerated: only {accepted} clauses accepted"
    );
}

#[test]
fn scaled_guard_rejects_a_per_variable_ratio() {
    // ADVERSARIAL: the multiplier must be UNIFORM. Branches bracket `q + r`;
    // the guard scales `q` by 2 and `r` by 3. `q + r <= -1 ∨ q + r >= 1 ∨
    // 2q + 3r = 0` is FALSE at q = 1, r = -1 (the branch form is 0, the guard
    // form is -1). Only the full per-coefficient verification rejects this —
    // a pivot-only check would accept it.
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let minus_one = terms.mk_int(BigInt::from(-1));
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));
    let sum = split_atom(&mut terms, "+", q, r, Sort::Int);
    let first = split_atom(&mut terms, "<=", sum, minus_one, Sort::Bool);
    let second = split_atom(&mut terms, "<=", one, sum, Sort::Bool);
    let two_q = split_atom(&mut terms, "*", q, two, Sort::Int);
    let three_r = split_atom(&mut terms, "*", r, three, Sort::Int);
    let skewed = split_atom(&mut terms, "+", two_q, three_r, Sort::Int);
    let guard = split_atom(&mut terms, "=", skewed, zero, Sort::Bool);
    assert!(!super::lia::recognize_arith_disequality_split(
        &terms,
        &[first, second, guard]
    ));

    // The UNIFORM companion is accepted: `2q + 2r = 0` is `k = 2`.
    let two_r = split_atom(&mut terms, "*", r, two, Sort::Int);
    let uniform = split_atom(&mut terms, "+", two_q, two_r, Sort::Int);
    let uniform_guard = split_atom(&mut terms, "=", uniform, zero, Sort::Bool);
    assert_eq!(
        super::lia::arith_disequality_split_guard_multiplier(
            &terms,
            &[first, second, uniform_guard]
        ),
        Some(BigInt::from(2))
    );
}
