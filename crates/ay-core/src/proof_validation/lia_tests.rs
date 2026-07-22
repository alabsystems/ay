// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;

use super::lia::{validate_lia_theory_lemma, LiaValidationError};
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
