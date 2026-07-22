// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use num_bigint::BigInt;

use super::{verify_farkas_conflict_lits_full, FarkasValidationError};
use crate::{FarkasAnnotation, Sort, Symbol, TermStore, TheoryLit};

/// Helper: build the `integer_ops` test_mul congruence conflict family.
///
/// `nl` = nonlinear-mul symbol for the LEFT product, `nr` = symbol for the
/// RIGHT product (equal in the genuine case), `lhs_eq_rhs` chooses whether the
/// two argument-equality premises actually relate the products' arguments.
/// Mirrors the captured driver conflict
/// `{ eqdv <= -1, mul(l_view,r_view) - mul(l,r) <= eqdv, l_view=l, r_view=r }`.
struct MulCongruenceConflict {
    terms: TermStore,
    conflict: Vec<TheoryLit>,
}

fn build_mul_congruence_conflict(
    left_sym: &str,
    right_sym: &str,
    relate_l: bool,
    relate_r: bool,
    direction_a: bool,
) -> MulCongruenceConflict {
    let mut terms = TermStore::new();
    let l_view = terms.mk_var("l_view", Sort::Int);
    let l = terms.mk_var("l", Sort::Int);
    let r_view = terms.mk_var("r_view", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let other = terms.mk_var("other", Sort::Int);

    let mul1 = terms.mk_app(Symbol::named(left_sym), vec![l_view, r_view], Sort::Int);
    let mul2 = terms.mk_app(Symbol::named(right_sym), vec![l, r], Sort::Int);
    let neg_mul2 = terms.mk_neg(mul2);
    let diff = terms.mk_add(vec![mul1, neg_mul2]); // mul1 - mul2

    let eqdv = terms.mk_var("__ay_eqdv", Sort::Int);
    let neg_one = terms.mk_int(BigInt::from(-1));
    let one = terms.mk_int(BigInt::from(1));

    let (lit0, lit1) = if direction_a {
        // eqdv <= -1  ;  mul1 - mul2 <= eqdv
        (terms.mk_le(eqdv, neg_one), terms.mk_le(diff, eqdv))
    } else {
        // 1 <= eqdv   ;  eqdv <= mul1 - mul2
        (terms.mk_le(one, eqdv), terms.mk_le(eqdv, diff))
    };

    // Argument-equality premises. When `relate_*` is false, equate the view to a
    // DIFFERENT variable so the products' arguments are NOT pairwise equal.
    let l_eq = terms.mk_eq(l_view, if relate_l { l } else { other });
    let r_eq = terms.mk_eq(r_view, if relate_r { r } else { other });

    let conflict = vec![
        TheoryLit::new(lit0, true),
        TheoryLit::new(lit1, true),
        TheoryLit::new(l_eq, true),
        TheoryLit::new(r_eq, true),
    ];
    MulCongruenceConflict { terms, conflict }
}

#[test]
fn euf_congruence_mul_conflict_direction_a_validates() {
    // The exact captured integer_ops conflict A (cert [1,1,1,1]): UNSAT only via
    // congruence mul(l_view,r_view) = mul(l,r). Must validate now.
    let c = build_mul_congruence_conflict(
        "__verification_consumer_nonlinear_mul",
        "__verification_consumer_nonlinear_mul",
        true,
        true,
        true,
    );
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1, 1]);
    verify_farkas_conflict_lits_full(&c.terms, &c.conflict, &farkas)
        .expect("congruence-justified mul conflict (direction A) should validate");
}

#[test]
fn euf_congruence_mul_conflict_direction_b_validates() {
    // Captured integer_ops conflict B (the other difference-variable bound).
    let c = build_mul_congruence_conflict(
        "__verification_consumer_nonlinear_mul",
        "__verification_consumer_nonlinear_mul",
        true,
        true,
        false,
    );
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1, 1]);
    verify_farkas_conflict_lits_full(&c.terms, &c.conflict, &farkas)
        .expect("congruence-justified mul conflict (direction B) should validate");
}

#[test]
fn euf_congruence_missing_left_arg_equality_stays_rejected() {
    // SOUNDNESS GATE #1/#2: if l_view is NOT equated to l (congruence does not
    // actually hold), the two products are independent variables and the
    // conflict is SAT — the certificate MUST stay rejected.
    let c = build_mul_congruence_conflict(
        "__verification_consumer_nonlinear_mul",
        "__verification_consumer_nonlinear_mul",
        false, // l_view = other, NOT l
        true,
        true,
    );
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1, 1]);
    let err = verify_farkas_conflict_lits_full(&c.terms, &c.conflict, &farkas)
        .expect_err("broken left-arg congruence must NOT be certified");
    assert!(
        matches!(err, FarkasValidationError::VariablesNotEliminated { .. }),
        "unexpected error: {err:?}"
    );
}

#[test]
fn euf_congruence_missing_right_arg_equality_stays_rejected() {
    let c = build_mul_congruence_conflict(
        "__verification_consumer_nonlinear_mul",
        "__verification_consumer_nonlinear_mul",
        true,
        false, // r_view = other, NOT r
        true,
    );
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1, 1]);
    let err = verify_farkas_conflict_lits_full(&c.terms, &c.conflict, &farkas)
        .expect_err("broken right-arg congruence must NOT be certified");
    assert!(
        matches!(err, FarkasValidationError::VariablesNotEliminated { .. }),
        "unexpected error: {err:?}"
    );
}

#[test]
fn euf_congruence_distinct_function_symbols_stays_rejected() {
    // SOUNDNESS: even with both argument equalities present, two applications of
    // DIFFERENT function symbols are NOT congruent — must stay rejected.
    let c = build_mul_congruence_conflict(
        "__verification_consumer_nonlinear_mul",
        "__verification_consumer_nonlinear_div", // different symbol
        true,
        true,
        true,
    );
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1, 1]);
    let err = verify_farkas_conflict_lits_full(&c.terms, &c.conflict, &farkas)
        .expect_err("distinct function symbols must NOT be treated as congruent");
    assert!(
        matches!(err, FarkasValidationError::VariablesNotEliminated { .. }),
        "unexpected error: {err:?}"
    );
}

#[test]
fn euf_congruence_does_not_false_accept_genuinely_sat_uf_conflict() {
    // A genuinely-SAT UF conflict (no relating equalities, opaque products free):
    // mul1 - mul2 <= eqdv ∧ eqdv <= -1 with mul1, mul2 unconstrained is SAT.
    // Drop the equality premises entirely (2-literal conflict) and confirm the
    // verifier still rejects — congruence machinery must not invent equalities.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let mul1 = terms.mk_app(
        Symbol::named("__verification_consumer_nonlinear_mul"),
        vec![a, b],
        Sort::Int,
    );
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let mul2 = terms.mk_app(
        Symbol::named("__verification_consumer_nonlinear_mul"),
        vec![c, d],
        Sort::Int,
    );
    let neg_mul2 = terms.mk_neg(mul2);
    let diff = terms.mk_add(vec![mul1, neg_mul2]);
    let eqdv = terms.mk_var("__ay_eqdv", Sort::Int);
    let neg_one = terms.mk_int(BigInt::from(-1));
    let lit0 = terms.mk_le(eqdv, neg_one);
    let lit1 = terms.mk_le(diff, eqdv);
    let conflict = vec![TheoryLit::new(lit0, true), TheoryLit::new(lit1, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let err = verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect_err("SAT UF conflict without congruence premises must be rejected");
    assert!(
        matches!(err, FarkasValidationError::VariablesNotEliminated { .. }),
        "unexpected error: {err:?}"
    );
}

#[test]
fn test_verify_farkas_conflict_lits_full_accepts_simple_bounds_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);

    let conflict = vec![TheoryLit::new(x_le_5, true), TheoryLit::new(x_ge_10, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);

    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("simple bounds conflict should validate");
}

#[test]
fn test_verify_farkas_conflict_lits_full_accepts_equality_orientation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));

    let x_eq_0 = terms.mk_eq(x, zero);
    let x_ge_1 = terms.mk_ge(x, one);

    let conflict = vec![TheoryLit::new(x_eq_0, true), TheoryLit::new(x_ge_1, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);

    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("equality orientation should validate");
}

#[test]
fn test_verify_farkas_conflict_lits_full_rejects_bad_coefficients() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);

    let conflict = vec![TheoryLit::new(x_le_5, true), TheoryLit::new(x_ge_10, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 0]);

    let err = verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect_err("invalid coefficients should be rejected");
    assert!(
        matches!(err, FarkasValidationError::VariablesNotEliminated { .. }),
        "unexpected error: {err:?}"
    );
}

#[test]
fn refuter_strict_cancellation_x_lt_5_x_gt_5_is_genuine_contradiction() {
    // Conflict {x < 5, x > 5}: blocking clause {x>=5, x<=5} is a TAUTOLOGY.
    // The Farkas combination 1*(x-5<0) + 1*(5-x<0) = (0 < 0) is impossible.
    // Accepting this is CORRECT, not a hole.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let x_lt_5 = terms.mk_lt(x, five);
    let x_gt_5 = terms.mk_gt(x, five);
    let conflict = vec![TheoryLit::new(x_lt_5, true), TheoryLit::new(x_gt_5, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let res = verify_farkas_conflict_lits_full(&terms, &conflict, &farkas);
    println!("REFUTER strict-cancel {{x<5,x>5}} => {:?}", res);
    assert!(
        res.is_ok(),
        "strict cancellation IS a genuine contradiction"
    );
}

#[test]
fn refuter_non_tautological_clause_must_be_rejected() {
    // Conflict {x < 5, x > 3} is NOT jointly UNSAT (x=4 satisfies both),
    // so blocking clause {x>=5, x<=3} is NOT a tautology (x=4 falsifies it).
    // Farkas 1*(x-5<0)+1*(3-x<0) = (x-5+3-x) = (-2 < 0)  -> TRUE inequality,
    // is_contradiction needs constant>=0 (strict); -2 >= 0 is FALSE -> REJECT.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let five = terms.mk_int(BigInt::from(5));
    let x_lt_5 = terms.mk_lt(x, five);
    let x_gt_3 = terms.mk_gt(x, three);
    let conflict = vec![TheoryLit::new(x_lt_5, true), TheoryLit::new(x_gt_3, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let res = verify_farkas_conflict_lits_full(&terms, &conflict, &farkas);
    println!("REFUTER non-taut {{x<5,x>3}} => {:?}", res);
    assert!(
        res.is_err(),
        "non-tautological clause MUST be rejected (no hole)"
    );
}

// ── Integer strengthening (#4666) ──────────────────────────────────────────
//
// A strict inequality `e < 0` over an INTEGER-valued form `e` strengthens to
// `e + 1 <= 0`. This lets the real-Farkas validator certify integer-only
// conflicts that have NO real refutation. The exact conflict that blocked
// `filter_positive`'s `lemma_num_of_pos_increasing` was `{ j+1 <= k (false),
// j < k (true) }` = `k < j+1 ∧ j < k`, real-SAT (j=0, k=0.5) but integer-UNSAT.

#[test]
fn integer_strict_gap_j_lt_k_and_k_lt_j_plus_1_validates() {
    let mut terms = TermStore::new();
    let j = terms.mk_var("j", Sort::Int);
    let k = terms.mk_var("k", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let j_plus_1 = terms.mk_add(vec![j, one]);

    // L0: (<= (+ j 1) k) asserted FALSE  ⟹  k < j+1
    let jp1_le_k = terms.mk_le(j_plus_1, k);
    // L1: (< j k) asserted TRUE
    let j_lt_k = terms.mk_lt(j, k);

    let conflict = vec![
        TheoryLit::new(jp1_le_k, false),
        TheoryLit::new(j_lt_k, true),
    ];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);

    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("integer-only strict gap j<k ∧ k<j+1 should validate after strengthening");
}

#[test]
fn integer_strict_gap_stays_rejected_over_reals() {
    // SAME conflict shape but Real-sorted: j<k ∧ k<j+1 is genuinely SAT over the
    // reals (j=0, k=0.5), so integer strengthening must NOT apply and the
    // certificate must be REJECTED (no false-accept).
    let mut terms = TermStore::new();
    let j = terms.mk_var("j", Sort::Real);
    let k = terms.mk_var("k", Sort::Real);
    let one = terms.mk_rational(num_rational::BigRational::from(BigInt::from(1)));
    let j_plus_1 = terms.mk_add(vec![j, one]);

    let jp1_le_k = terms.mk_le(j_plus_1, k);
    let j_lt_k = terms.mk_lt(j, k);

    let conflict = vec![
        TheoryLit::new(jp1_le_k, false),
        TheoryLit::new(j_lt_k, true),
    ];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);

    let err = verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect_err("real-SAT gap must be rejected (strengthening is integer-only)");
    assert!(
        matches!(err, FarkasValidationError::NoContradiction { .. }),
        "unexpected error: {err:?}"
    );
}

#[test]
fn integer_strengthening_does_not_false_accept_sat_set() {
    // `j < k ∧ k < j+2` is SAT over the integers (k = j+1). Even WITH integer
    // strengthening the combination must NOT yield a contradiction — proving the
    // strengthening cannot turn a satisfiable integer set into a false UNSAT.
    let mut terms = TermStore::new();
    let j = terms.mk_var("j", Sort::Int);
    let k = terms.mk_var("k", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let j_plus_2 = terms.mk_add(vec![j, two]);

    let j_lt_k = terms.mk_lt(j, k);
    let k_lt_jp2 = terms.mk_lt(k, j_plus_2);

    let conflict = vec![TheoryLit::new(j_lt_k, true), TheoryLit::new(k_lt_jp2, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);

    let err = verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect_err("SAT integer set must not be certified as a conflict");
    assert!(
        matches!(err, FarkasValidationError::NoContradiction { .. }),
        "unexpected error: {err:?}"
    );
}

#[test]
fn resolve_equality_signs_flips_lhs_minus_rhs_orientation() {
    // `x >= 3 ∧ x = 2` refutes with λ = [1, 1] internally (the validator
    // searches the equality orientation). The Alethe `la_generic` printing of
    // that combination must carry the equality coefficient as `-1`: the
    // external checker forms `1·(x - 3) + d·(x - 2) ≥ 0` and only `d = -1`
    // cancels `x` into the contradiction `-1 ≥ 0`.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));
    let x_ge_3 = terms.mk_ge(x, three);
    let x_eq_2 = terms.mk_eq(x, two);

    let conflict = vec![TheoryLit::new(x_ge_3, true), TheoryLit::new(x_eq_2, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("internal certificate must verify");

    let signed = super::resolve_equality_coefficient_signs(&terms, &conflict, &farkas)
        .expect("sign resolution must succeed");
    assert_eq!(
        signed,
        vec![
            num_rational::Rational64::from(1),
            num_rational::Rational64::from(-1)
        ]
    );
}

#[test]
fn resolve_equality_signs_keeps_pure_inequalities_bitwise() {
    // No equality literals → unique orientations → the printed coefficients
    // must come back exactly as stored (byte-stability of existing proofs).
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));
    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);

    let conflict = vec![TheoryLit::new(x_le_5, true), TheoryLit::new(x_ge_10, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    let signed = super::resolve_equality_coefficient_signs(&terms, &conflict, &farkas)
        .expect("sign resolution must succeed");
    assert_eq!(signed, farkas.coefficients);
}

#[test]
fn resolve_equality_signs_rejects_non_contradicting_certificate() {
    // `x >= 3 ∧ x = 4` is SAT: no orientation contradicts, so the resolver
    // must decline rather than fabricate signed args.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let four = terms.mk_int(BigInt::from(4));
    let x_ge_3 = terms.mk_ge(x, three);
    let x_eq_4 = terms.mk_eq(x, four);

    let conflict = vec![TheoryLit::new(x_ge_3, true), TheoryLit::new(x_eq_4, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    assert!(super::resolve_equality_coefficient_signs(&terms, &conflict, &farkas).is_none());
}

// =========================================================================
// LINEAR-only verification (`verify_farkas_conflict_lits_linear`, class 4)
// =========================================================================

/// A congruence-only conflict `x = y ∧ f(x) < f(y)` with unit coefficients:
/// the FULL verifier accepts it (via the #4666 congruence-closure merge), but
/// the LINEAR-only verifier must reject it — external `la_generic` checkers
/// perform no congruence reasoning, so exporting it as `la_generic` would be
/// a wrong proof step.
#[test]
fn test_linear_verifier_rejects_congruence_only_certificate() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let fx = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let fy = terms.mk_app(Symbol::named("f"), vec![y], Sort::Int);
    let eq = terms.mk_eq(x, y);
    let lt = terms.mk_lt(fx, fy);
    let conflict = vec![TheoryLit::new(eq, true), TheoryLit::new(lt, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);

    assert!(
        verify_farkas_conflict_lits_full(&terms, &conflict, &farkas).is_ok(),
        "FULL verifier (congruence merge) should accept the theory conflict"
    );
    assert!(
        super::verify_farkas_conflict_lits_linear(&terms, &conflict, &farkas).is_err(),
        "LINEAR verifier must reject: opaque f(x), f(y) never cancel linearly"
    );
}

/// An opaque-atom conflict that IS linearly contradictory —
/// `(select a i) > 5 ∧ (select a i) < 3` — must pass the LINEAR verifier:
/// the shared select term is one opaque variable and cancels.
#[test]
fn test_linear_verifier_accepts_opaque_atom_farkas() {
    let mut terms = TermStore::new();
    let s = terms.mk_var("s", Sort::Int); // stands in for the array
    let i = terms.mk_var("i", Sort::Int);
    let sel = terms.mk_app(Symbol::named("select"), vec![s, i], Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let three = terms.mk_int(BigInt::from(3));
    let gt = terms.mk_gt(sel, five);
    let lt = terms.mk_lt(sel, three);
    let conflict = vec![TheoryLit::new(gt, true), TheoryLit::new(lt, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);

    assert!(
        super::verify_farkas_conflict_lits_linear(&terms, &conflict, &farkas).is_ok(),
        "shared opaque select atom cancels; certificate is linearly valid"
    );
}

/// The `la_generic` bridge shape `(= s t) ∧ (R s t)` over opaque atoms —
/// equality asserted TRUE plus a contradicting comparison — is linearly
/// contradictory (s − t = 0 vs s − t < 0) and must pass.
#[test]
fn test_linear_verifier_accepts_equality_vs_comparison_bridge() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let fx = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let fy = terms.mk_app(Symbol::named("f"), vec![y], Sort::Int);
    let eq = terms.mk_eq(fx, fy);
    let lt = terms.mk_lt(fx, fy);
    let conflict = vec![TheoryLit::new(eq, true), TheoryLit::new(lt, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);

    assert!(
        super::verify_farkas_conflict_lits_linear(&terms, &conflict, &farkas).is_ok(),
        "equality-true vs strict comparison over the same opaque atoms is linearly UNSAT"
    );
}

// =========================================================================
// Multi-equality Farkas chains (the `try_rebuild_with_pure_bounds` producer
// class: a conjunction of equalities substituted into a linear assertion).
// The verifier must ACCEPT genuine joint infeasibility — recomputing
// Σλᵢ·cᵢ with equalities searched in BOTH orientations — and REJECT every
// forged variant. Nothing here trusts annotation presence.
// =========================================================================

/// THE model-checker-consumer-wall shape: `x = n ∧ y = 0 ∧ n < x + y` with λ = [1, 1, 1].
/// Orientations `(n - x) + (-y) + (n < x + y ⇒ n - x - y < 0)`… the
/// verifier finds `(x - n) ≤ 0` is not needed: `(n - x) ≤ 0` is wrong; the
/// contradicting combination is `(x - n) + (y) + (n - x - y) < 0` = `0 < 0`.
#[test]
fn multi_equality_two_premise_chain_validates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let n = terms.mk_var("n", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));

    let x_eq_n = terms.mk_eq(x, n);
    let y_eq_0 = terms.mk_eq(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let n_lt_sum = terms.mk_lt(n, sum);

    let conflict = vec![
        TheoryLit::new(x_eq_n, true),
        TheoryLit::new(y_eq_0, true),
        TheoryLit::new(n_lt_sum, true),
    ];
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("two-equality chain into a strict inequality must validate");
}

/// Three equalities + one strict inequality: `x=a ∧ y=b ∧ z=c ∧
/// a+b+c < x+y+z` with λ = [1, 1, 1, 1] (six variables eliminated).
#[test]
fn multi_equality_three_premise_chain_validates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);

    let x_eq_a = terms.mk_eq(x, a);
    let y_eq_b = terms.mk_eq(y, b);
    let z_eq_c = terms.mk_eq(z, c);
    let abc = terms.mk_add(vec![a, b, c]);
    let xyz = terms.mk_add(vec![x, y, z]);
    let lt = terms.mk_lt(abc, xyz);

    let conflict = vec![
        TheoryLit::new(x_eq_a, true),
        TheoryLit::new(y_eq_b, true),
        TheoryLit::new(z_eq_c, true),
        TheoryLit::new(lt, true),
    ];
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1, 1]);
    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("three-equality chain must validate");
}

/// Mixed equality/inequality bounds: `x = n ∧ y <= 0 ∧ n < x + y`.
#[test]
fn multi_equality_mixed_eq_ineq_chain_validates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let n = terms.mk_var("n", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));

    let x_eq_n = terms.mk_eq(x, n);
    let y_le_0 = terms.mk_le(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let n_lt_sum = terms.mk_lt(n, sum);

    let conflict = vec![
        TheoryLit::new(x_eq_n, true),
        TheoryLit::new(y_le_0, true),
        TheoryLit::new(n_lt_sum, true),
    ];
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("mixed equality/inequality chain must validate");
}

/// Scaled coefficients: `2x = 6 ∧ x >= 4` needs λ = [1, 2]
/// (`(2x - 6) + 2·(4 - x) = 2 > 0`).
#[test]
fn multi_equality_scaled_coefficients_validate() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let four = terms.mk_int(BigInt::from(4));
    let six = terms.mk_int(BigInt::from(6));

    let two_x = terms.mk_app(Symbol::named("*"), vec![two, x], Sort::Int);
    let eq = terms.mk_eq(two_x, six);
    let ge = terms.mk_ge(x, four);

    let conflict = vec![TheoryLit::new(eq, true), TheoryLit::new(ge, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 2]);
    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("scaled-coefficient equality chain must validate");
}

/// FORGED: the right premises with a WRONG coefficient. The FULL verifier
/// may still re-derive a genuine contradiction through its congruence merge
/// (a VERIFIED equality substitution — the conflict IS unsatisfiable), but
/// the la_generic export surface must stay exact: the LINEAR verifier
/// (external `la_generic` semantics, no congruence reasoning) must reject
/// the coefficients, and sign resolution must decline to print them. This
/// is the fail-closed pair the producer dry-runs BEFORE attaching any
/// certificate.
#[test]
fn multi_equality_chain_wrong_coefficient_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let n = terms.mk_var("n", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));

    let x_eq_n = terms.mk_eq(x, n);
    let y_eq_0 = terms.mk_eq(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let n_lt_sum = terms.mk_lt(n, sum);

    let conflict = vec![
        TheoryLit::new(x_eq_n, true),
        TheoryLit::new(y_eq_0, true),
        TheoryLit::new(n_lt_sum, true),
    ];
    let farkas = FarkasAnnotation::from_ints(&[2, 1, 1]);
    super::verify_farkas_conflict_lits_linear(&terms, &conflict, &farkas)
        .expect_err("wrong coefficient must not eliminate the variables linearly");
    assert!(
        super::resolve_equality_coefficient_signs(&terms, &conflict, &farkas).is_none(),
        "no signed printing of a non-eliminating combination"
    );
    // The correct certificate for the SAME conflict stays accepted.
    let good = FarkasAnnotation::from_ints(&[1, 1, 1]);
    super::verify_farkas_conflict_lits_linear(&terms, &conflict, &good)
        .expect("the true coefficients validate linearly");
}

/// FORGED: a SATISFIABLE equality set (`x = 5 ∧ x >= 3`) must be rejected in
/// every orientation — the "coefficients prove the WRONG constant" class.
#[test]
fn multi_equality_chain_satisfiable_set_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let five = terms.mk_int(BigInt::from(5));

    let x_eq_5 = terms.mk_eq(x, five);
    let x_ge_3 = terms.mk_ge(x, three);

    let conflict = vec![TheoryLit::new(x_eq_5, true), TheoryLit::new(x_ge_3, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect_err("satisfiable set must be rejected in every equality orientation");
}

/// FORGED: strict/nonstrict confusion. `x <= 5 ∧ x >= 5` sums to `0 ≤ 0` —
/// NOT a contradiction under the nonstrict rule (needs k > 0). The set is
/// satisfiable at x = 5; only a strict literal would make 0 a witness.
#[test]
fn multi_equality_chain_nonstrict_boundary_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_5 = terms.mk_ge(x, five);

    let conflict = vec![TheoryLit::new(x_le_5, true), TheoryLit::new(x_ge_5, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas).expect_err(
        "boundary-satisfiable nonstrict pair must be rejected (0 ≤ 0 is no contradiction)",
    );
}

/// FORGED: the all-zero combination derives `0 ≤ 0` from anything — it must
/// never count as a contradiction.
#[test]
fn multi_equality_chain_zero_combination_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let n = terms.mk_var("n", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));

    let x_eq_n = terms.mk_eq(x, n);
    let y_eq_0 = terms.mk_eq(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let n_lt_sum = terms.mk_lt(n, sum);

    let conflict = vec![
        TheoryLit::new(x_eq_n, true),
        TheoryLit::new(y_eq_0, true),
        TheoryLit::new(n_lt_sum, true),
    ];
    let farkas = FarkasAnnotation::from_ints(&[0, 0, 0]);
    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect_err("the zero combination proves nothing");
}

/// FORGED: negative λ would let a forger flip constraint directions at will;
/// the shape check must reject it outright.
#[test]
fn multi_equality_chain_negative_lambda_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let n = terms.mk_var("n", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));

    let x_eq_n = terms.mk_eq(x, n);
    let y_eq_0 = terms.mk_eq(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let n_lt_sum = terms.mk_lt(n, sum);

    let conflict = vec![
        TheoryLit::new(x_eq_n, true),
        TheoryLit::new(y_eq_0, true),
        TheoryLit::new(n_lt_sum, true),
    ];
    let farkas = FarkasAnnotation::new(vec![
        num_rational::Rational64::from(-1),
        num_rational::Rational64::from(1),
        num_rational::Rational64::from(1),
    ]);
    let err = verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect_err("negative coefficients must be rejected by the shape check");
    assert!(
        matches!(err, FarkasValidationError::NegativeCoefficients { .. }),
        "unexpected error: {err:?}"
    );
}

/// FORGED: coefficient count must match the conflict length exactly.
#[test]
fn multi_equality_chain_count_mismatch_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let n = terms.mk_var("n", Sort::Int);
    let x_eq_n = terms.mk_eq(x, n);
    let x_lt_n = terms.mk_lt(x, n);

    let conflict = vec![TheoryLit::new(x_eq_n, true), TheoryLit::new(x_lt_n, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    let err = verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect_err("coefficient/conflict count mismatch must be rejected");
    assert!(
        matches!(err, FarkasValidationError::CoefficientCountMismatch { .. }),
        "unexpected error: {err:?}"
    );
}

/// The printed `la_generic` signs for the model-checker-consumer-wall chain: the internal
/// non-negative certificate resolves to SIGNED coefficients (the equalities
/// used in their flipped orientations print negative), and the resolved
/// combination is re-verified — a non-contradicting certificate resolves to
/// `None` (see `resolve_equality_signs_rejects_non_contradicting_certificate`).
#[test]
fn multi_equality_chain_sign_resolution_is_exact() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let n = terms.mk_var("n", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));

    let x_eq_n = terms.mk_eq(x, n);
    let y_eq_0 = terms.mk_eq(y, zero);
    let sum = terms.mk_add(vec![x, y]);
    let n_lt_sum = terms.mk_lt(n, sum);

    let conflict = vec![
        TheoryLit::new(x_eq_n, true),
        TheoryLit::new(y_eq_0, true),
        TheoryLit::new(n_lt_sum, true),
    ];
    let farkas = FarkasAnnotation::from_ints(&[1, 1, 1]);
    let signed = super::resolve_equality_coefficient_signs(&terms, &conflict, &farkas)
        .expect("the contradicting orientation must resolve to printable signs");
    assert_eq!(signed.len(), 3, "one signed coefficient per literal");
    assert!(
        signed
            .iter()
            .all(|c| *c != num_rational::Rational64::from(0)),
        "no zero coefficients in a resolved combination: {signed:?}"
    );
}

/// #4666 regression (pointer-safe-10, QF_ALIA): a 12-literal all-equality
/// telescoping chain whose contradicting combination needs FIVE equality sign
/// flips. The 2^12 = 4096 orientation space exceeds the 1024 search cap, and
/// the single-flip fast path cannot reach it, so this exact certificate was
/// rejected ("combination does not eliminate variables: coeff = 2") on every
/// such conflict — forcing the semantic backstop. The sign-free equality
/// elimination path must validate it.
#[test]
fn long_equality_chain_beyond_search_cap_validates() {
    let mut terms = TermStore::new();
    let names = [
        "x_9", "x_14", "x_23", "x_26", "x_34", "x_37", "x_45", "x_48", "x_51", "x_56", "x_62",
    ];
    let v: std::collections::BTreeMap<&str, crate::TermId> = names
        .iter()
        .map(|n| (*n, terms.mk_var(*n, Sort::Int)))
        .collect();
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let x14_plus_1 = terms.mk_add(vec![v["x_14"], one]);

    // Captured conflict shape (all positive equalities, all coefficients 1):
    let lits = vec![
        terms.mk_eq(v["x_9"], v["x_23"]),
        terms.mk_eq(v["x_14"], one),
        terms.mk_eq(v["x_9"], zero),
        terms.mk_eq(v["x_45"], v["x_62"]),
        terms.mk_eq(v["x_51"], v["x_62"]),
        terms.mk_eq(v["x_48"], v["x_56"]),
        terms.mk_eq(v["x_45"], v["x_56"]),
        terms.mk_eq(v["x_26"], x14_plus_1),
        terms.mk_eq(v["x_23"], v["x_34"]),
        terms.mk_eq(v["x_37"], v["x_48"]),
        terms.mk_eq(v["x_34"], v["x_51"]),
        terms.mk_eq(v["x_26"], v["x_37"]),
    ];
    let conflict: Vec<TheoryLit> = lits.into_iter().map(|t| TheoryLit::new(t, true)).collect();
    let farkas = FarkasAnnotation::from_ints(&[1; 12]);
    verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect("#4666 long equality chain certificate must validate");
}

/// Soundness guard for the equality-elimination path: a SATISFIABLE
/// all-equality set (same chain with the contradiction removed) must still be
/// rejected — sign-free equality multipliers must not manufacture a
/// contradiction where none exists.
#[test]
fn long_equality_chain_satisfiable_set_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));

    // x = y, y = z, z = w, x = 0: satisfiable (all zero).
    let lits = vec![
        terms.mk_eq(x, y),
        terms.mk_eq(y, z),
        terms.mk_eq(z, w),
        terms.mk_eq(x, zero),
    ];
    let conflict: Vec<TheoryLit> = lits.into_iter().map(|t| TheoryLit::new(t, true)).collect();
    let farkas = FarkasAnnotation::from_ints(&[1; 4]);
    let err = verify_farkas_conflict_lits_full(&terms, &conflict, &farkas)
        .expect_err("satisfiable equality set must be rejected");
    assert!(matches!(
        err,
        FarkasValidationError::VariablesNotEliminated { .. }
            | FarkasValidationError::NoContradiction { .. }
    ));
}
