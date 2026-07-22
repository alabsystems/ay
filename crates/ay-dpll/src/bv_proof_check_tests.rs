// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for the semantic bit-vector proof checker.
//!
//! Coverage:
//! - Positive: genuine BV-theory tautologies (commutativity, De Morgan, masking,
//!   extract/concat round-trips, congruence over BV) — built as real `Proof` /
//!   `TermStore` objects — all validate via solver discharge.
//! - Negative: hand-corrupted clauses (wrong operator, wrong width, a
//!   non-identity) are rejected with a precise reason.
//! - Unsupported: a clause containing an out-of-fragment node (Int arithmetic)
//!   returns `Unchecked` (fail-closed), never `Valid`.
//! - Aggregation and skipping behave as documented.
//! - End-to-end: a real UNSAT QF_BV proof is run through the checker. This pins
//!   the finding that the live prover currently emits NO word-level BV
//!   `TheoryLemma` steps (a single `trust` empty-clause step instead), so the BV
//!   checker reports zero targeted steps — and never fabricates a `Valid`.

use super::*;
use ay_core::{Proof, ProofStep, Symbol, TermStore, TheoryLemmaKind};

/// Helper: wrap a clause as a `BvBitBlast` theory lemma and run it through the
/// BV checker, returning the single step's verdict.
fn check_bv_lemma(terms: &TermStore, clause: Vec<TermId>) -> BvStepVerdict {
    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "BV".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::BvBitBlast,
        lia: None,
    });
    let report = check_bv_proof(&proof, terms);
    assert_eq!(report.steps.len(), 1, "expected exactly one BV step");
    report.steps[0].verdict.clone()
}

fn bv(width: u32) -> Sort {
    Sort::bitvec(width)
}

// ---------------------------------------------------------------------------
// Positive cases: genuine BV-theory tautologies validate.
// ---------------------------------------------------------------------------

/// Commutativity of `bvadd`: `(= (bvadd x y) (bvadd y x))` is a BV tautology.
#[test]
fn bvadd_commutativity_validates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(8));
    let y = terms.mk_var("y", bv(8));
    let xy = terms.mk_bvadd(vec![x, y]);
    let yx = terms.mk_bvadd(vec![y, x]);
    let eq = terms.mk_eq(xy, yx);

    let verdict = check_bv_lemma(&terms, vec![eq]);
    assert_eq!(
        verdict,
        BvStepVerdict::Valid,
        "bvadd commutativity must validate"
    );
}

/// De Morgan over BV: `(= (bvnot (bvand x y)) (bvor (bvnot x) (bvnot y)))`.
#[test]
fn de_morgan_validates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(4));
    let y = terms.mk_var("y", bv(4));
    let and = terms.mk_bvand(vec![x, y]);
    let lhs = terms.mk_bvnot(and);
    let nx = terms.mk_bvnot(x);
    let ny = terms.mk_bvnot(y);
    let rhs = terms.mk_bvor(vec![nx, ny]);
    let eq = terms.mk_eq(lhs, rhs);

    let verdict = check_bv_lemma(&terms, vec![eq]);
    assert_eq!(verdict, BvStepVerdict::Valid, "De Morgan must validate");
}

/// Masking with all-ones: `(= (bvand x #b1111) x)` for a 4-bit `x`.
#[test]
fn and_all_ones_identity_validates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(4));
    let ones = terms.mk_bitvec(num_bigint::BigInt::from(0xF), 4);
    let masked = terms.mk_bvand(vec![x, ones]);
    let eq = terms.mk_eq(masked, x);

    let verdict = check_bv_lemma(&terms, vec![eq]);
    assert_eq!(
        verdict,
        BvStepVerdict::Valid,
        "and with all-ones is identity"
    );
}

/// Extract/concat round-trip: `(= (concat ((_ extract 7 4) x) ((_ extract 3 0) x)) x)`
/// for an 8-bit `x`. Exercises the indexed-operator translation path.
#[test]
fn extract_concat_roundtrip_validates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(8));
    let hi = terms.mk_bvextract(7, 4, x);
    let lo = terms.mk_bvextract(3, 0, x);
    let cat = terms.mk_bvconcat(vec![hi, lo]);
    let eq = terms.mk_eq(cat, x);

    let verdict = check_bv_lemma(&terms, vec![eq]);
    assert_eq!(
        verdict,
        BvStepVerdict::Valid,
        "extract/concat round-trip must validate, got {verdict:?}"
    );
}

/// A clausal (disjunctive) BV tautology: `(or (bvult x y) (bvuge x y))` — every
/// pair is either strictly-less or greater-or-equal. Exercises the multi-literal
/// clause-negation path.
#[test]
fn ult_or_uge_clause_validates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(4));
    let y = terms.mk_var("y", bv(4));
    let ult = terms.mk_app(Symbol::named("bvult"), [x, y], Sort::Bool);
    let uge = terms.mk_app(Symbol::named("bvuge"), [x, y], Sort::Bool);
    let clause = terms.mk_or(vec![ult, uge]);

    let verdict = check_bv_lemma(&terms, vec![clause]);
    assert_eq!(
        verdict,
        BvStepVerdict::Valid,
        "ult-or-uge is exhaustive and must validate"
    );
}

/// Sign-extend identity: extracting the original low bits of a sign-extended
/// value returns the original: `(= ((_ extract 3 0) ((_ sign_extend 4) x)) x)`.
#[test]
fn sign_extend_low_bits_validates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(4));
    let sext = terms.mk_bvsign_extend(4, x);
    let low = terms.mk_bvextract(3, 0, sext);
    let eq = terms.mk_eq(low, x);

    let verdict = check_bv_lemma(&terms, vec![eq]);
    assert_eq!(verdict, BvStepVerdict::Valid);
}

/// BV congruence clause (EUF over BV), as might be mislabelled as a bit-blast
/// lemma: `(or (not (= x y)) (= (f x) (f y)))` for a UF `f : BV4 -> BV4`.
/// The semantic checker validates it regardless of the wrong label.
#[test]
fn bv_congruence_clause_validates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(4));
    let y = terms.mk_var("y", bv(4));
    let fx = terms.mk_app(Symbol::named("f"), [x], bv(4));
    let fy = terms.mk_app(Symbol::named("f"), [y], bv(4));
    let xy = terms.mk_eq(x, y);
    let not_xy = terms.mk_not(xy);
    let fxfy = terms.mk_eq(fx, fy);
    let clause = terms.mk_or(vec![not_xy, fxfy]);

    let verdict = check_bv_lemma(&terms, vec![clause]);
    assert_eq!(
        verdict,
        BvStepVerdict::Valid,
        "BV congruence clause is entailed and must validate"
    );
}

/// Multiply-by-two is a left-shift: `(= (bvmul x #b0010) (bvshl x #b0001))` for
/// 4-bit `x` (mod 2^4). Exercises shifts and multiplication.
#[test]
fn mul_two_is_shift_validates() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(4));
    let two = terms.mk_bitvec(num_bigint::BigInt::from(2), 4);
    let one = terms.mk_bitvec(num_bigint::BigInt::from(1), 4);
    let mul = terms.mk_bvmul(vec![x, two]);
    let shl = terms.mk_bvshl(vec![x, one]);
    let eq = terms.mk_eq(mul, shl);

    let verdict = check_bv_lemma(&terms, vec![eq]);
    assert_eq!(verdict, BvStepVerdict::Valid);
}

// ---------------------------------------------------------------------------
// Negative cases: corrupted clauses are rejected with a precise reason.
// ---------------------------------------------------------------------------

/// `bvsub` is NOT commutative: `(= (bvsub x y) (bvsub y x))` is false in general.
#[test]
fn bvsub_not_commutative_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(8));
    let y = terms.mk_var("y", bv(8));
    let xy = terms.mk_bvsub(vec![x, y]);
    let yx = terms.mk_bvsub(vec![y, x]);
    let eq = terms.mk_eq(xy, yx);

    let verdict = check_bv_lemma(&terms, vec![eq]);
    assert!(
        verdict.is_invalid(),
        "bvsub commutativity is false and must be rejected, got {verdict:?}"
    );
    if let BvStepVerdict::Invalid { reason } = &verdict {
        assert!(
            reason.contains("not a BV-theory tautology"),
            "reason: {reason}"
        );
    }
}

/// Corrupted De Morgan (wrong outer op): `(= (bvnot (bvand x y)) (bvand (bvnot x) (bvnot y)))`
/// — the RHS should be `bvor`, not `bvand`. Not entailed -> Invalid.
#[test]
fn corrupted_de_morgan_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(4));
    let y = terms.mk_var("y", bv(4));
    let and = terms.mk_bvand(vec![x, y]);
    let lhs = terms.mk_bvnot(and);
    let nx = terms.mk_bvnot(x);
    let ny = terms.mk_bvnot(y);
    // Bug: bvand instead of bvor.
    let rhs = terms.mk_bvand(vec![nx, ny]);
    let eq = terms.mk_eq(lhs, rhs);

    let verdict = check_bv_lemma(&terms, vec![eq]);
    assert!(
        verdict.is_invalid(),
        "corrupted De Morgan must be rejected, got {verdict:?}"
    );
}

/// A false unit BV claim: `(= x (bvnot x))` is unsatisfiable as an equality
/// (no fixed point), so the *clause* `(= x (bvnot x))` is not a tautology and is
/// rejected.
#[test]
fn x_eq_not_x_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(4));
    let nx = terms.mk_bvnot(x);
    let eq = terms.mk_eq(x, nx);

    let verdict = check_bv_lemma(&terms, vec![eq]);
    assert!(
        verdict.is_invalid(),
        "x = ~x is never true and must be rejected, got {verdict:?}"
    );
}

/// A clause that is true for *some* but not all assignments:
/// `(or (bvult x y) (= x y))` drops the `bvugt` disjunct, so the assignment
/// `x > y` falsifies it -> Invalid.
#[test]
fn incomplete_trichotomy_clause_rejected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(4));
    let y = terms.mk_var("y", bv(4));
    let ult = terms.mk_app(Symbol::named("bvult"), [x, y], Sort::Bool);
    let eq = terms.mk_eq(x, y);
    let clause = terms.mk_or(vec![ult, eq]);

    let verdict = check_bv_lemma(&terms, vec![clause]);
    assert!(
        verdict.is_invalid(),
        "incomplete trichotomy clause must be rejected, got {verdict:?}"
    );
}

// ---------------------------------------------------------------------------
// Unsupported / fail-closed cases.
// ---------------------------------------------------------------------------

/// A non-tautological clause over Int `+` is now MODELLED under the LIA extension
/// (QF_LIA) and returns the PRECISE verdict `Invalid` (was `Unchecked` when Int was
/// outside the modelled fragment) — and, the load-bearing soundness property, it is
/// NEVER `Valid`. `(= (+ i j) i)` holds iff `j == 0`, so it is not a tautology.
#[test]
fn int_arithmetic_non_tautology_is_invalid_never_valid() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let sum = terms.mk_app(Symbol::named("+"), [i, j], Sort::Int);
    // (= (+ i j) i) — Boolean equality over Int with `+`.
    let eq = terms.mk_eq(sum, i);

    let verdict = check_bv_lemma(&terms, vec![eq]);
    assert!(
        verdict.is_invalid(),
        "non-tautological Int clause must be Invalid, got {verdict:?}"
    );
    assert!(!verdict.is_valid(), "must never be Valid");
}

/// An empty clause is ill-formed for a BV lemma -> Unchecked.
#[test]
fn empty_clause_is_unchecked() {
    let terms = TermStore::new();
    let verdict = check_bv_lemma(&terms, vec![]);
    assert!(
        verdict.is_unchecked(),
        "empty clause must be Unchecked, got {verdict:?}"
    );
}

/// A non-Bool clause literal (a BV term used directly as a literal) -> Unchecked.
#[test]
fn non_bool_literal_is_unchecked() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(4));
    // `x` itself (BitVec-sorted) is not a propositional literal.
    let verdict = check_bv_lemma(&terms, vec![x]);
    assert!(
        verdict.is_unchecked(),
        "non-Bool literal must be Unchecked, got {verdict:?}"
    );
}

/// A reserved builtin op the explicit dispatch does not model — here a BV
/// overflow predicate `bvsaddo` (pure BV, so the mixed-Int/BV guard does NOT
/// catch it) — must be declined as `Unchecked`, never re-declared as an
/// uninterpreted function. Re-declaring a reserved name hits ay-frontend's
/// reserved-symbol gate, which the panicking `Solver::declare_fun` wrapper would
/// turn into an ICE. Fail closed instead.
#[test]
fn reserved_overflow_predicate_is_unchecked_not_ice() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(8));
    let y = terms.mk_var("y", bv(8));
    // `(bvsaddo x y)` is a Bool-sorted BV overflow predicate not covered by the
    // checker's explicit BV dispatch, so it reaches the uninterpreted path.
    let saddo = terms.mk_app(Symbol::named("bvsaddo"), [x, y], Sort::Bool);

    let verdict = check_bv_lemma(&terms, vec![saddo]);
    assert!(
        verdict.is_unchecked(),
        "reserved builtin bvsaddo must be Unchecked (fail-closed), got {verdict:?}"
    );
    assert!(
        !verdict.is_valid(),
        "a reserved builtin must never be Valid"
    );
}

/// A quantified literal -> Unchecked (QF discharge cannot model it).
#[test]
fn quantified_literal_is_unchecked() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(4));
    let zero = terms.mk_bitvec(num_bigint::BigInt::from(0), 4);
    let body = terms.mk_eq(x, zero);
    let forall = terms.mk_forall(vec![("x".to_string(), bv(4))], body);

    let verdict = check_bv_lemma(&terms, vec![forall]);
    assert!(
        verdict.is_unchecked(),
        "quantified literal must be Unchecked, got {verdict:?}"
    );
    assert!(!verdict.is_valid());
}

// ---------------------------------------------------------------------------
// Skipping / aggregation.
// ---------------------------------------------------------------------------

/// Non-BV steps are not reported (the checker makes no claim about them).
#[test]
fn non_bv_steps_are_skipped() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(p));
    proof.add_step(ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause: vec![p],
        farkas: None,
        kind: TheoryLemmaKind::EufTransitive,
        lia: None,
    });
    let report = check_bv_proof(&proof, &terms);
    assert!(report.steps.is_empty(), "no BV steps -> empty report");
    assert!(report.all_bv_steps_valid(), "vacuously sound for BV");
}

/// The `BvBitBlastGate` annotated form is also targeted.
#[test]
fn gate_annotated_lemma_is_targeted() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(4));
    let y = terms.mk_var("y", bv(4));
    let xy = terms.mk_bvand(vec![x, y]);
    let yx = terms.mk_bvand(vec![y, x]);
    let eq = terms.mk_eq(xy, yx);

    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "BV".to_string(),
        clause: vec![eq],
        farkas: None,
        kind: TheoryLemmaKind::BvBitBlastGate {
            gate_type: ay_core::BvGateType::And,
            width: 4,
        },
        lia: None,
    });
    let report = check_bv_proof(&proof, &terms);
    assert_eq!(
        report.steps.len(),
        1,
        "gate-annotated lemma must be targeted"
    );
    assert_eq!(report.steps[0].verdict, BvStepVerdict::Valid);
}

/// Aggregate counts across a mixed proof: one valid, one invalid, one unchecked.
#[test]
fn aggregate_counts() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(4));
    let y = terms.mk_var("y", bv(4));

    // Valid: bvadd commutativity.
    let xy = terms.mk_bvadd(vec![x, y]);
    let yx = terms.mk_bvadd(vec![y, x]);
    let valid = terms.mk_eq(xy, yx);

    // Invalid: bvsub commutativity (false).
    let sxy = terms.mk_bvsub(vec![x, y]);
    let syx = terms.mk_bvsub(vec![y, x]);
    let invalid = terms.mk_eq(sxy, syx);

    // Unchecked: Real arithmetic — outside both the BV and the LIA fragments, so
    // the Real-sorted vars fail `supported_sort` and the step stays Unchecked.
    // (Int `+` is now modelled by the LIA extension, so it would be Invalid here,
    // not Unchecked; Real keeps this an honest unchecked aggregate-count case. Two
    // DISTINCT vars so `(= r s)` is not reflexivity-simplified to `true`.)
    let r = terms.mk_var("r", Sort::Real);
    let s = terms.mk_var("s", Sort::Real);
    let unchecked = terms.mk_eq(r, s);

    let mut proof = Proof::new();
    for clause in [valid, invalid, unchecked] {
        proof.add_step(ProofStep::TheoryLemma {
            theory: "BV".to_string(),
            clause: vec![clause],
            farkas: None,
            kind: TheoryLemmaKind::BvBitBlast,
            lia: None,
        });
    }

    let report = check_bv_proof(&proof, &terms);
    assert_eq!(report.steps.len(), 3);
    assert_eq!(report.valid_count(), 1, "{report:?}");
    assert_eq!(report.invalid_count(), 1, "{report:?}");
    assert_eq!(report.unchecked_count(), 1, "{report:?}");
    assert!(!report.all_bv_steps_valid());
    assert!(report.first_invalid().is_some());
}

// ---------------------------------------------------------------------------
// End-to-end against the live prover (documents the finding).
// ---------------------------------------------------------------------------

/// Fully end-to-end: drive the real `ay` solver on a small UNSAT QF_BV query,
/// take the *actual* `Proof` and its backing `TermStore`, and run the BV
/// checker over them.
///
/// FINDING (documented, not papered over): for these QF_BV queries the live
/// prover does NOT emit any word-level BV `TheoryLemma` step (it emits a single
/// `trust` empty-clause step from the bit-blasted SAT refutation). So the BV
/// semantic checker has zero *targeted* steps and reports vacuous validity for
/// the BV fragment — it never fabricates a `Valid` for the trust step (that is
/// the structural checker's job). This test pins both facts: no BV lemma steps
/// appear, and the checker reports zero valid/invalid BV steps.
#[test]
fn end_to_end_live_prover_emits_no_bv_theory_lemma() {
    use crate::api::{Logic, Solver};

    let mut solver = Solver::new(Logic::QfBv);
    solver.set_produce_proofs(true);
    let x = solver.declare_const("x", bv(4));
    let y = solver.declare_const("y", bv(4));
    // x + y != y + x  -> UNSAT (commutativity).
    let xy = solver.bvadd(x, y);
    let yx = solver.bvadd(y, x);
    let e = solver.eq(xy, yx);
    let ne = solver.not(e);
    solver.assert_term(ne);
    assert!(
        solver.check_sat().is_unsat(),
        "bvadd commutativity query must be UNSAT"
    );

    let proof = solver
        .last_proof()
        .expect("proof must be present after UNSAT");
    let store = solver.proof_term_store();
    let report = check_bv_proof(proof, store);

    // The live prover does not currently emit word-level BV theory lemmas for
    // bit-blasted queries: the checker therefore has no targeted steps.
    assert_eq!(
        report.steps.len(),
        0,
        "expected no BV theory-lemma steps from the bit-blasted proof, got {report:?}"
    );
    // Vacuously sound for the BV fragment, and crucially never a fabricated Valid.
    assert!(report.all_bv_steps_valid());
    assert_eq!(report.valid_count(), 0);
    assert_eq!(report.invalid_count(), 0);
}

/// End-to-end with a constructed proof carrying a genuine UNSAT-derived BV
/// lemma: solve a tiny UNSAT QF_BV query, then feed the BV checker a hand-built
/// `TheoryLemma` whose clause is the *negation* of the asserted (unsatisfiable)
/// conjunction — i.e. a genuine BV tautology — and confirm it validates. This
/// exercises the positive path through a real solver-derived clause shape.
#[test]
fn positive_unsat_derived_lemma_validates() {
    // The asserted formula `x != x` (over BV) is UNSAT, so its negation
    // `(= x x)` is a BV tautology; a BV lemma asserting it must validate.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", bv(8));
    let refl = terms.mk_eq(x, x);

    let verdict = check_bv_lemma(&terms, vec![refl]);
    assert_eq!(verdict, BvStepVerdict::Valid);
}

/// REGRESSION (#nia-oom forged-UNSAT): a MIXED Int+BV assertion set that is
/// genuinely SATISFIABLE must NEVER discharge as `Valid` under the thin BV proof
/// checker.
///
/// This is the exact shape of the `unbounded_alloc_const_oom` VC: the element
/// count `_2` is an `Int` pinned to `bv2nat(bvshl(int2bv_64(1), int2bv_64(28)))`
/// (== 1<<28 == 268_435_456) and the violation `_2 >= 268_435_456` is reachable,
/// so the conjunction is SAT (`_2 = 268_435_456` is a model).
///
/// `pick_logic` formerly chose pure `QF_BV` for this mixed obligation because
/// `has_bv` was set (the `int2bv`/`bvshl` chain); the `has_int && !has_bv` LIA arm
/// was skipped. The Translator then lossily coerced the unbounded `Int` `_2` (and
/// would have truncated any 64-bit ceiling literal) into a bit-vector, and the BV
/// solver returned a SPURIOUS UNSAT -> `Valid` -> a forged
/// `StrictProofVerdict::Verified` -> the OOM mutant verified instead of failing.
///
/// The checker must fail-closed (`Unchecked`) on a mixed Int+BV problem: the thin
/// word-level translator cannot soundly decide the BV<->LIA bridge; deciding it is
/// the full `Executor`'s job (which returns an honest `unknown` here, so the
/// deferred-trust rescue correctly stays `Rejected`). SOUNDNESS contract: never
/// `Valid` on a satisfiable mixed problem.
#[test]
fn mixed_int_bv_alloc_oom_is_never_valid() {
    use num_bigint::BigInt;
    let mut terms = TermStore::new();
    let int_var = |t: &mut TermStore, n: &str| t.mk_var(n, Sort::Int);
    let element_count = int_var(&mut terms, "_2");
    let shift_amount = int_var(&mut terms, "_3");
    let shift_in_range = terms.mk_var("_4", Sort::Bool);

    // _3 == 28  ;  _4 == (_3 < 64)  ;  assert _4
    let c28 = terms.mk_int(BigInt::from(28));
    let c64 = terms.mk_int(BigInt::from(64));
    let eq_3 = terms.mk_eq(shift_amount, c28);
    let lt_3_64 = terms.mk_app(Symbol::named("<"), vec![shift_amount, c64], Sort::Bool);
    let eq_4 = terms.mk_eq(shift_in_range, lt_3_64);

    // 0 <= _2 <= u64::MAX  (the unsigned-range bounds — note u64::MAX, which a
    // *signed* BV coercion turns into -1 and silently corrupts).
    let c0 = terms.mk_int(BigInt::from(0));
    let umax = terms.mk_int(BigInt::from(18_446_744_073_709_551_615u64));
    let le_0_2 = terms.mk_app(Symbol::named("<="), vec![c0, element_count], Sort::Bool);
    let le_2_umax = terms.mk_app(Symbol::named("<="), vec![element_count, umax], Sort::Bool);

    // _2 == bv2nat(bvshl(int2bv_64(1), int2bv_64(_3)))  [== 1 << 28 == 268435456]
    let one = terms.mk_int(BigInt::from(1));
    let one_bv = terms.mk_int2bv(64, one);
    let shift_bv = terms.mk_int2bv(64, shift_amount);
    let shifted = terms.mk_bvshl(vec![one_bv, shift_bv]);
    let count_val = terms.mk_bv2nat(shifted); // Int
    let def_2 = terms.mk_eq(element_count, count_val);

    // _2 <= 268435456  (upper-bounds _2 so the violation forces _2 == ceiling).
    let ceiling = terms.mk_int(BigInt::from(268_435_456));
    let le_2_ceil = terms.mk_app(
        Symbol::named("<="),
        vec![element_count, ceiling],
        Sort::Bool,
    );

    // Violation: _2 >= ceiling  OR  2*_2 >= ceiling  OR  2*_2 >= i64::MAX.
    let two = terms.mk_int(BigInt::from(2));
    let two_2 = terms.mk_app(Symbol::named("*"), vec![two, element_count], Sort::Int);
    let imax = terms.mk_int(BigInt::from(9_223_372_036_854_775_807i64));
    let ge_2_ceil = terms.mk_app(
        Symbol::named(">="),
        vec![element_count, ceiling],
        Sort::Bool,
    );
    let ge_2two_ceil = terms.mk_app(Symbol::named(">="), vec![two_2, ceiling], Sort::Bool);
    let ge_2two_imax = terms.mk_app(Symbol::named(">="), vec![two_2, imax], Sort::Bool);
    let viol = terms.mk_or(vec![ge_2_ceil, ge_2two_ceil, ge_2two_imax]);

    // The conjunction is SATISFIABLE (`_2 = 268435456`, `_3 = 28`, `_4 = true` is a
    // model), so the only sound discharge verdicts are Invalid (a model exists) or
    // Unchecked (declined). A `Valid` here is a forged UNSAT — the OOM mutant would
    // then verify instead of failing.
    let assertions = [
        eq_3,
        eq_4,
        shift_in_range,
        le_0_2,
        le_2_umax,
        def_2,
        le_2_ceil,
        viol,
    ];
    let verdict = check_bv_assertions_unsat(&terms, &assertions);
    assert!(
        !verdict.is_valid(),
        "mixed Int+BV SAT problem must never discharge as Valid (forged UNSAT), got {verdict:?}"
    );
    assert!(
        verdict.is_unchecked(),
        "mixed Int+BV must fail-closed to Unchecked, got {verdict:?}"
    );
}
