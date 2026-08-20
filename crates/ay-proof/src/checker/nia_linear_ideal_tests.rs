// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{Proof, Sort, Symbol, TheoryLemmaKind};
use num_bigint::BigInt;
use num_rational::BigRational;

fn int_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Int)
}

fn int_const(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_int(n.into())
}

fn equality_literal(terms: &mut TermStore, name: &str) -> TermId {
    let variable = int_var(terms, name);
    let zero = int_const(terms, 0);
    terms.mk_eq(variable, zero)
}

fn refuse_exact_charge(
    terms: &TermStore,
    clause: &[TermId],
    rejected: (usize, usize),
) -> (ProofCheckError, bool) {
    let mut refused = false;
    let error = validate_linear_ideal_refutation_with_progress(
        terms,
        ProofId(0),
        clause,
        &mut |work, bytes| {
            if (work, bytes) == rejected {
                refused = true;
                return false;
            }
            true
        },
    )
    .expect_err("the selected caller-envelope charge must be refused");
    (error, refused)
}

#[test]
fn constraint_slot_refusal_is_typed_and_precedes_push() {
    let mut terms = TermStore::new();
    let equality = equality_literal(&mut terms, "constraint_slot_x");
    let not_equality = terms.mk_not_raw(equality);
    let bytes = super::super::nra_poly::generic_container_slot_bytes::<
        super::super::nra_poly::Constraint,
    >()
    .expect("constraint slot accounting fits usize");

    let (error, refused) = refuse_exact_charge(&terms, &[not_equality], (1, bytes));
    assert_eq!(error, ProofCheckError::ResourceLimit);
    assert!(refused, "fixture must reach the constraint-slot precharge");
}

#[test]
fn equality_row_slot_refusal_is_typed_and_precedes_push() {
    let mut terms = TermStore::new();
    let equality = equality_literal(&mut terms, "equality_row_slot_x");
    let not_equality = terms.mk_not_raw(equality);
    let bytes = super::super::nra_poly::generic_container_slot_bytes::<&MPoly>()
        .expect("row slot accounting fits usize");

    let (error, refused) = refuse_exact_charge(&terms, &[not_equality], (1, bytes));
    assert_eq!(error, ProofCheckError::ResourceLimit);
    assert!(refused, "fixture must reach the equality-row precharge");
}

#[test]
fn disequality_row_slot_refusal_is_typed_and_precedes_push() {
    let mut terms = TermStore::new();
    let equality = equality_literal(&mut terms, "disequality_row_slot_x");
    let bytes = super::super::nra_poly::generic_container_slot_bytes::<&MPoly>()
        .expect("row slot accounting fits usize");

    let (error, refused) = refuse_exact_charge(&terms, &[equality], (1, bytes));
    assert_eq!(error, ProofCheckError::ResourceLimit);
    assert!(refused, "fixture must reach the disequality-row precharge");
}

#[test]
fn memo_lookup_refusal_is_typed_and_precedes_tree_access() {
    let mut terms = TermStore::new();
    let equality = equality_literal(&mut terms, "memo_lookup_x");
    let not_equality = terms.mk_not_raw(equality);
    let expected = (super::super::nra_poly::GENERIC_MEMO_TREE_WORK, 0);

    let (error, refused) = refuse_exact_charge(&terms, &[not_equality], expected);
    assert_eq!(error, ProofCheckError::ResourceLimit);
    assert!(refused, "fixture must reach the memo-tree precharge");
}

#[test]
fn leading_lookup_refusal_precedes_next_back() {
    let mut terms = TermStore::new();
    let variable = int_var(&mut terms, "leading_lookup_x");
    let poly = MPoly::var(variable);
    let expected_work =
        (poly.terms.len() + 1) * (super::super::nra_poly::MAX_POLY_DEGREE as usize + 1);
    let mut refused = false;
    let mut progress = |work, bytes| {
        if (work, bytes) == (expected_work, 0) {
            refused = true;
            return false;
        }
        true
    };
    let mut meter = WorkMeter::with_progress(&mut progress);
    let mut envelope = IdealEnvelope::default();

    let error = envelope
        .leading_term(&poly, &mut meter)
        .expect_err("caller refusal must stop before the leading lookup");
    assert_eq!(error, WORK_METER_RESOURCE_LIMIT);
    assert!(refused, "fixture must reach the leading-lookup precharge");
}

/// The motivating shape: loop-invariant consecution, where the nonlinear
/// monomials cancel. Clause is `(or (not INV) INV_NEXT)`.
#[test]
fn accepts_invariant_consecution() {
    let mut terms = TermStore::new();
    let n = int_var(&mut terms, "n");
    let sum = int_var(&mut terms, "sum");
    let counter = int_var(&mut terms, "counter");
    let one = int_const(&mut terms, 1);

    // sum + counter*n = n*n
    let counter_n = terms.mk_mul(vec![counter, n]);
    let n_n = terms.mk_mul(vec![n, n]);
    let inv_lhs = terms.mk_add(vec![sum, counter_n]);
    let inv = terms.mk_eq(inv_lhs, n_n);

    // (sum + n) + (counter - 1)*n = n*n
    let sum_next = terms.mk_add(vec![sum, n]);
    let counter_next = terms.mk_sub(vec![counter, one]);
    let counter_next_n = terms.mk_mul(vec![counter_next, n]);
    let inv_next_lhs = terms.mk_add(vec![sum_next, counter_next_n]);
    let inv_next = terms.mk_eq(inv_next_lhs, n_n);

    let clause = vec![terms.mk_not_raw(inv), inv_next];
    validate_linear_ideal_refutation(&terms, ProofId(0), &clause)
        .expect("consecution clause is a polynomial identity and must validate");
}

/// Nontrivial row reduction: half the first equality minus half the second
/// yields the goal, so this exercises exact rational normalization rather
/// than merely recognizing two identical polynomials.
#[test]
fn accepts_multi_equality_rational_span() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "span_x");
    let y = int_var(&mut terms, "span_y");
    let z = int_var(&mut terms, "span_z");
    let zero = int_const(&mut terms, 0);
    let two = int_const(&mut terms, 2);

    // P1 = 2x + y = 0; P2 = y - 2z = 0.
    let two_x = terms.mk_mul(vec![two, x]);
    let p1_lhs = terms.mk_add(vec![two_x, y]);
    let p1 = terms.mk_eq(p1_lhs, zero);
    let two_z = terms.mk_mul(vec![two, z]);
    let p2_lhs = terms.mk_sub(vec![y, two_z]);
    let p2 = terms.mk_eq(p2_lhs, zero);

    // G = x + z = (P1 - P2) / 2.
    let goal_lhs = terms.mk_add(vec![x, z]);
    let goal = terms.mk_eq(goal_lhs, zero);
    let not_p1 = terms.mk_not_raw(p1);
    let not_p2 = terms.mk_not_raw(p2);
    let clause = vec![not_p1, not_p2, goal];

    validate_linear_ideal_refutation(&terms, ProofId(0), &clause)
        .expect("a rational combination of two equality rows must validate");
}

#[test]
fn rejects_wrong_coefficient_near_multi_equality_span() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "wrong_span_x");
    let y = int_var(&mut terms, "wrong_span_y");
    let z = int_var(&mut terms, "wrong_span_z");
    let zero = int_const(&mut terms, 0);
    let one = int_const(&mut terms, 1);
    let two = int_const(&mut terms, 2);

    let two_x = terms.mk_mul(vec![two, x]);
    let p1_lhs = terms.mk_add(vec![two_x, y]);
    let p1 = terms.mk_eq(p1_lhs, zero);
    let two_z = terms.mk_mul(vec![two, z]);
    let p2_lhs = terms.mk_sub(vec![y, two_z]);
    let p2 = terms.mk_eq(p2_lhs, zero);
    let x_plus_z = terms.mk_add(vec![x, z]);
    let wrong_goal_lhs = terms.mk_add(vec![x_plus_z, one]);
    let wrong_goal = terms.mk_eq(wrong_goal_lhs, zero);
    let not_p1 = terms.mk_not_raw(p1);
    let not_p2 = terms.mk_not_raw(p2);

    validate_linear_ideal_refutation(&terms, ProofId(0), &[not_p1, not_p2, wrong_goal])
        .expect_err("an affine off-by-one is not in the equality span");
}

/// A complete strict refutation pins the integration boundary: the
/// checker accepts a semantically revalidated `Generic` lemma and still
/// authenticates both authored assumptions and the terminal empty clause.
/// `trust_count` intentionally remains a diagnostic of the producer tag;
/// it is not the strict checker's acceptance predicate.
#[test]
fn strict_checker_accepts_validated_generic_but_reports_producer_tag() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "strict_span_x");
    let zero = int_const(&mut terms, 0);
    let two = int_const(&mut terms, 2);
    let two_x = terms.mk_mul(vec![two, x]);
    let premise = terms.mk_eq(two_x, zero);
    let goal = terms.mk_eq(x, zero);
    let not_premise = terms.mk_not_raw(premise);
    let not_goal = terms.mk_not_raw(goal);

    let mut proof = Proof::new();
    let h_premise = proof.add_assume(premise, None);
    let h_not_goal = proof.add_assume(not_goal, None);
    let lemma =
        proof.add_theory_lemma_with_kind("NIA", vec![not_premise, goal], TheoryLemmaKind::Generic);
    let goal_step = proof.add_resolution(vec![goal], premise, lemma, h_premise);
    proof.add_resolution(vec![], goal, goal_step, h_not_goal);

    let quality = crate::check_proof_strict_with_context(
        &proof,
        &terms,
        None,
        None,
        Some(&[premise, not_goal]),
    )
    .expect("the exact authored refutation must pass strict checking");
    assert_eq!(quality.trust_count, 1, "the Generic tag remains diagnostic");
    let terminal = crate::terminal_trust_report(&proof);
    assert!(
        terminal.trust_theory_lemma_on_path > 0,
        "the Generic lemma must remain reachable from the empty clause: {terminal:?}"
    );
    let alethe = crate::export_alethe(&proof, &terms);
    assert!(
        alethe.contains(":rule hole"),
        "Generic theory lemmas must remain honest holes on the Alethe wire:\n{alethe}"
    );
    assert!(
        !alethe.contains(":rule trust"),
        "the validated Generic theory lemma is a hole, not a Trust step:\n{alethe}"
    );

    crate::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[premise]))
        .expect_err("omitting an authored assumption must still fail closed");
}

#[test]
fn rejects_coefficient_over_private_width_cap() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "huge_coeff_x");
    let zero = int_const(&mut terms, 0);
    let huge = BigInt::from(1_u8) << (super::super::nra_poly::MAX_POLY_COEFF_BITS as usize + 1);
    let huge_term = terms.mk_int(huge);
    let huge_x = terms.mk_mul(vec![huge_term, x]);
    let equality = terms.mk_eq(huge_x, zero);
    let not_equality = terms.mk_not_raw(equality);

    let error = validate_linear_ideal_refutation(&terms, ProofId(0), &[not_equality, equality])
        .expect_err("an oversized exact coefficient must fail closed before elimination");
    assert!(
        error.to_string().contains("coefficient exceeds cap"),
        "unexpected refusal: {error}"
    );
}

#[test]
fn rejects_more_independent_rows_than_the_basis_cap() {
    let mut terms = TermStore::new();
    let zero = int_const(&mut terms, 0);
    let mut clause = Vec::with_capacity(MAX_BASIS_ROWS + 2);
    let mut first = None;
    for i in 0..=MAX_BASIS_ROWS {
        let x = int_var(&mut terms, &format!("basis_cap_{i}"));
        let equality = terms.mk_eq(x, zero);
        first.get_or_insert(equality);
        clause.push(terms.mk_not_raw(equality));
    }
    clause.push(first.expect("at least one row"));

    let error = decide_linear_ideal_refutation(&terms, &clause)
        .expect_err("a distinct 1025th pivot must trip the retained-basis cap");
    assert!(
        error.contains("basis-row cap"),
        "unexpected refusal: {error}"
    );
}

#[test]
fn opaque_terms_share_only_by_exact_term_id() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "opaque_arg");
    let zero = int_const(&mut terms, 0);
    let fx = terms.mk_app(Symbol::named("opaque_f"), vec![x], Sort::Int);
    let gx = terms.mk_app(Symbol::named("opaque_g"), vec![x], Sort::Int);
    let fx_zero = terms.mk_eq(fx, zero);
    let gx_zero = terms.mk_eq(gx, zero);
    let not_fx_zero = terms.mk_not_raw(fx_zero);

    validate_linear_ideal_refutation(&terms, ProofId(0), &[not_fx_zero, fx_zero])
        .expect("the same opaque TermId must denote one polynomial variable");
    validate_linear_ideal_refutation(&terms, ProofId(0), &[not_fx_zero, gx_zero])
        .expect_err("distinct opaque TermIds must never be merged");
}

#[test]
fn rejects_malformed_mixed_sort_relation() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "mixed_int");
    let y = terms.mk_var("mixed_real", Sort::Real);
    let malformed = terms.mk_app(Symbol::named("="), vec![x, y], Sort::Bool);
    let not_malformed = terms.mk_not_raw(malformed);

    validate_linear_ideal_refutation(&terms, ProofId(0), &[not_malformed, malformed])
        .expect_err("a forged mixed-sort equality must fail closed");
}

/// A clause that is NOT valid must be refused: the goal equality is not a
/// combination of the premise equality (an off-by-one in the update).
#[test]
fn rejects_non_identity() {
    let mut terms = TermStore::new();
    let n = int_var(&mut terms, "n");
    let sum = int_var(&mut terms, "sum");
    let counter = int_var(&mut terms, "counter");
    let one = int_const(&mut terms, 1);

    let counter_n = terms.mk_mul(vec![counter, n]);
    let n_n = terms.mk_mul(vec![n, n]);
    let inv_lhs = terms.mk_add(vec![sum, counter_n]);
    let inv = terms.mk_eq(inv_lhs, n_n);

    // WRONG update: sum + 1 instead of sum + n.
    let sum_next = terms.mk_add(vec![sum, one]);
    let counter_next = terms.mk_sub(vec![counter, one]);
    let counter_next_n = terms.mk_mul(vec![counter_next, n]);
    let inv_next_lhs = terms.mk_add(vec![sum_next, counter_next_n]);
    let inv_next = terms.mk_eq(inv_next_lhs, n_n);

    let clause = vec![terms.mk_not_raw(inv), inv_next];
    validate_linear_ideal_refutation(&terms, ProofId(0), &clause)
        .expect_err("a non-identity must NOT validate");
}

/// The rule must not accept a clause with no disequality to refute, even
/// when the equalities themselves are consistent.
#[test]
fn rejects_without_disequality() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let zero = int_const(&mut terms, 0);
    let ge = terms.mk_ge(x, zero);
    let clause = vec![ge];
    validate_linear_ideal_refutation(&terms, ProofId(0), &clause)
        .expect_err("no disequality conjunct means nothing is refuted");
}

/// The shared `Generic` entry point offers ONE normalization of the negated
/// clause to BOTH arithmetic lanes.
///
/// * An identity refutation is taken by the equality-span fast path — which is
///   the only lane that can see it, since it has no order conjunct at all.
/// * An order refutation is taken by the Fourier–Motzkin lane — which the span
///   rule declines by construction, as the companion assertion pins.
/// * A negation with a rational model is still refused by both.
#[test]
fn shared_entry_point_serves_both_arithmetic_lanes() {
    let mut terms = TermStore::new();

    // Lane 1 (span): 2x = 0 entails x = 0.
    let x = terms.mk_var("shared_lane_x", Sort::Int);
    let y = terms.mk_var("shared_lane_y", Sort::Int);
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let two_x = terms.mk_mul(vec![two, x]);
    let premise = terms.mk_eq(two_x, zero);
    let goal = terms.mk_eq(x, zero);
    let identity_clause = vec![terms.mk_not_raw(premise), goal];

    // Lane 2 (Fourier–Motzkin): x <= y and y <= x force x = y.
    let xy = terms.mk_le(x, y);
    let yx = terms.mk_le(y, x);
    let equal = terms.mk_eq(x, y);
    let order_clause = vec![terms.mk_not_raw(xy), terms.mk_not_raw(yx), equal];

    // Neither lane: 0 < x < 1 has the rational model x = 1/2.
    let positive = terms.mk_gt(x, zero);
    let below_one = terms.mk_lt(x, one);
    let satisfiable_clause = vec![terms.mk_not_raw(positive), terms.mk_not_raw(below_one)];

    let decide = |clause: &[TermId]| {
        let mut unbounded = |_: usize, _: usize| true;
        validate_generic_arithmetic_refutation_with_progress(
            &terms,
            ProofId(0),
            clause,
            &mut unbounded,
        )
    };
    decide(&identity_clause).expect("the equality-span fast path must take the identity");
    decide(&order_clause).expect("the Fourier-Motzkin lane must take the order refutation");
    decide(&satisfiable_clause)
        .expect_err("a negation with a rational model must be refused by both lanes");

    validate_linear_ideal_refutation(&terms, ProofId(0), &order_clause)
        .expect_err("the span rule alone has no order content");
}

/// Order constraints alone must never suffice FOR THIS RULE: the span rule
/// decides equalities and declines `x > 0` versus `x < 0`. (The shared entry
/// point above then hands exactly this shape to the Fourier–Motzkin lane, which
/// does refute it — the split of labour, not a soundness boundary.)
#[test]
fn rejects_order_only_conflict() {
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let zero = int_const(&mut terms, 0);
    let gt = terms.mk_gt(x, zero);
    let lt = terms.mk_lt(x, zero);
    let clause = vec![terms.mk_not_raw(gt), terms.mk_not_raw(lt)];
    validate_linear_ideal_refutation(&terms, ProofId(0), &clause)
        .expect_err("this rule decides equalities only; order conflicts belong to Farkas");
}

// ---------------------------------------------------------------------------
// `recognize_arith_clause_tautology` — or-packed and to_real coverage
// ---------------------------------------------------------------------------

#[test]
fn recognizes_or_packed_lia_tautology_unit() {
    // `(or (= 42 s) (not (= i (+ i 1))))` — valid because `i = i + 1` is
    // infeasible; `s` stays an opaque leaf. The QF_AUFLIRA ROW-envelope shape.
    let mut terms = TermStore::new();
    let i = int_var(&mut terms, "i");
    let s = int_var(&mut terms, "s");
    let one = int_const(&mut terms, 1);
    let forty_two = int_const(&mut terms, 42);
    let i_plus_1 = terms.mk_app(Symbol::named("+"), vec![i, one], Sort::Int);
    let bad_eq = terms.mk_app(Symbol::named("="), vec![i, i_plus_1], Sort::Bool);
    let not_bad = terms.mk_not(bad_eq);
    let sel_eq = terms.mk_app(Symbol::named("="), vec![forty_two, s], Sort::Bool);
    let unit = terms.mk_app(Symbol::named("or"), vec![sel_eq, not_bad], Sort::Bool);
    assert!(recognize_arith_clause_tautology(&terms, &[unit]));
}

#[test]
fn rejects_satisfiable_or_packed_unit() {
    // `(or (= 42 s) (not (= i 1)))` is falsifiable (`s = 0, i = 1`).
    let mut terms = TermStore::new();
    let i = int_var(&mut terms, "i");
    let s = int_var(&mut terms, "s");
    let one = int_const(&mut terms, 1);
    let forty_two = int_const(&mut terms, 42);
    let i_eq_one = terms.mk_app(Symbol::named("="), vec![i, one], Sort::Bool);
    let not_eq = terms.mk_not(i_eq_one);
    let sel_eq = terms.mk_app(Symbol::named("="), vec![forty_two, s], Sort::Bool);
    let unit = terms.mk_app(Symbol::named("or"), vec![sel_eq, not_eq], Sort::Bool);
    assert!(!recognize_arith_clause_tautology(&terms, &[unit]));
}

#[test]
fn to_real_embedding_links_int_and_real_sides() {
    // `¬(3/2 < r) ∨ ¬(r = to_real x) ∨ ¬(x <= 1)` — the QF_AUFLIRA cross-sort
    // gate conflict. Valid only if `to_real x` is read as `x`; an opaque leaf
    // loses the link and the clause would be wrongly refused.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let r = terms.mk_var("r", Sort::Real);
    let three_halves = terms.mk_rational(BigRational::new(BigInt::from(3), BigInt::from(2)));
    let one = int_const(&mut terms, 1);
    let to_real_x = terms.mk_app(Symbol::named("to_real"), vec![x], Sort::Real);
    let lt = terms.mk_app(Symbol::named("<"), vec![three_halves, r], Sort::Bool);
    let eq = terms.mk_app(Symbol::named("="), vec![r, to_real_x], Sort::Bool);
    let le = terms.mk_app(Symbol::named("<="), vec![x, one], Sort::Bool);
    let clause = [terms.mk_not(lt), terms.mk_not(eq), terms.mk_not(le)];
    assert!(recognize_arith_clause_tautology(&terms, &clause));
}

#[test]
fn bv2nat_of_constant_folds_exactly() {
    // `(<= (bv2nat #b0...0) 18446744073709551615)` — the ground Seq index
    // bound unit; valid because bv2nat folds to 0.
    let mut terms = TermStore::new();
    let zero64 = terms.mk_bitvec(BigInt::from(0), 64);
    let bv2nat = terms.mk_app(Symbol::named("bv2nat"), vec![zero64], Sort::Int);
    let max = int_const(&mut terms, i64::MAX); // any positive bound works
    let le = terms.mk_app(Symbol::named("<="), vec![bv2nat, max], Sort::Bool);
    assert!(recognize_arith_clause_tautology(&terms, &[le]));

    // The symbolic argument stays opaque: `(<= (bv2nat x) N)` alone is NOT
    // recognized (no range side-constraints are added).
    let x = terms.mk_var("x", Sort::BitVec(ay_core::BitVecSort { width: 64 }));
    let sym = terms.mk_app(Symbol::named("bv2nat"), vec![x], Sort::Int);
    let le_sym = terms.mk_app(Symbol::named("<="), vec![sym, max], Sort::Bool);
    assert!(!recognize_arith_clause_tautology(&terms, &[le_sym]));
}

#[test]
fn bv2nat_symbolic_width_bound_is_a_tautology() {
    // `(<= (bv2nat sk) 18446744073709551615)` over SYMBOLIC 64-bit `sk`:
    // valid by the operator's range, carried by the entailed side-bounds.
    let mut terms = TermStore::new();
    let sk = terms.mk_var("sk", Sort::BitVec(ay_core::BitVecSort { width: 64 }));
    let bv2nat = terms.mk_app(Symbol::named("bv2nat"), vec![sk], Sort::Int);
    let max = terms.mk_int(BigInt::from(u64::MAX));
    let le = terms.mk_app(Symbol::named("<="), vec![bv2nat, max], Sort::Bool);
    assert!(recognize_arith_clause_tautology(&terms, &[le]));

    // Nonnegativity too.
    let zero = int_const(&mut terms, 0);
    let ge = terms.mk_app(Symbol::named("<="), vec![zero, bv2nat], Sort::Bool);
    assert!(recognize_arith_clause_tautology(&terms, &[ge]));

    // But a TIGHTER bound is not entailed: `(<= (bv2nat sk) 5)` must reject.
    let five = int_const(&mut terms, 5);
    let tight = terms.mk_app(Symbol::named("<="), vec![bv2nat, five], Sort::Bool);
    assert!(!recognize_arith_clause_tautology(&terms, &[tight]));
}
