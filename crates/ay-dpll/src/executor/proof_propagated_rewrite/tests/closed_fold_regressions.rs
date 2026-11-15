// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Closed collapsing folds over bit-vectors wider than the bounded BV/LIA
//! interpreter's 64 bits (`equality/closed_fold.rs`).
//!
//! The planner fixtures are synthetic. The authored conjunction
//! `(and p (= w c) q)` pins the 128-bit `w` to `c`. Substituting the pin into
//! its own conjunct folds `(= c c)` to `true`, and the conjunct disappears
//! from the rewritten `(and p q)`. Before the checker chose the closing step,
//! that fold was always closed by a `BvLiaTautology` lemma, which the strict
//! checker refuses for a 128-bit term.
//!
//! Only the end-to-end fixture is model-checker-consumer's realloc validation query,
//! reduced (`tests/fixtures/closed_fold_wide_bv_pin_with_array_conjunct.smt2`).
//! On it the default posture answered `unknown (incomplete
//! self-check-rejected)`, although z3 refutes the query in 0.02 s.

use super::*;

fn bv_sort(width: u32) -> Sort {
    Sort::BitVec(ay_core::BitVecSort::new(width))
}

fn bv_literal(terms: &mut TermStore, value: u128, width: u32) -> TermId {
    terms.mk_bitvec(num_bigint::BigInt::from(value), width)
}

/// The value of model-checker-consumer's 128-bit pin (`_9_fld1`).
const WIDE_PIN: u128 = 147_573_952_589_676_412_932;

/// `(and p (pred w bound) q)` with the pin `(= w c)`: the middle conjunct
/// folds away. `pred` is `=` for the self-substituted pin itself.
fn pinned_conjunct(width: u32, pred: &str, value: u128, bound: u128) -> (Fixture, TermId) {
    let mut terms = TermStore::new();
    let p = bool_fun(&mut terms, "pa", 0);
    let q = bool_fun(&mut terms, "pc", 0);
    let w = terms.mk_var("w", bv_sort(width));
    let c = bv_literal(&mut terms, value, width);
    let pin = terms.mk_app(Symbol::named("="), [w, c], Sort::Bool);
    let conjunct = if pred == "=" {
        pin
    } else {
        let bound = bv_literal(&mut terms, bound, width);
        terms.mk_app(Symbol::named(pred), [w, bound], Sort::Bool)
    };
    let before = terms.mk_app(Symbol::named("and"), [p, conjunct, q], Sort::Bool);
    let true_term = terms.true_term();
    let after = terms.mk_and(vec![p, true_term, q]);
    assert_ne!(
        after, before,
        "the fixture must eliminate the middle conjunct"
    );

    let mut fixture = Fixture::new(vec![before, pin], terms);
    fixture.entry(w, c, pin, 1);
    fixture.record(before, after, 1);
    (fixture, after)
}

/// Plan `(cl target)`, close it into a refutation, run the untouched strict
/// checker over the whole proof, and return the planned chain.
fn strictly_checked_chain(fixture: &mut Fixture, target: TermId) -> Proof {
    let (chain, conclusion) = fixture
        .plan(target)
        .expect("planner must derive the recorded rewrite");
    let mut refutation = chain.clone();
    let negated = fixture.terms.mk_not_raw(target);
    let counter = refutation.add_assume(negated, None);
    refutation.add_resolution(Vec::new(), target, conclusion, counter);
    let quality = ay_proof::check_proof_strict(&refutation, &fixture.terms)
        .expect("every planned step must re-derive under the strict checker");
    assert_eq!(
        quality.trust_count, 0,
        "planned chains must be trust-free: {quality}"
    );
    chain
}

fn has_rule(chain: &Proof, wanted: AletheRule) -> bool {
    chain
        .steps
        .iter()
        .any(|step| matches!(step, ProofStep::Step { rule, .. } if *rule == wanted))
}

fn has_lemma(chain: &Proof, wanted: &TheoryLemmaKind) -> bool {
    chain
        .steps
        .iter()
        .any(|step| matches!(step, ProofStep::TheoryLemma { kind, .. } if kind == wanted))
}

/// GREEN: the 128-bit pin closes with a strict `evaluate` of
/// `(= (= c c) true)`, which pinned Carcara also checks `valid`. Without the
/// checker-chosen route this chain carries a `BvLiaTautology` the strict
/// checker refuses ("query is outside the checked BV/LIA fragment").
#[test]
fn wide_bv_pin_substituted_into_itself_closes_with_a_checked_evaluate() {
    let (mut fixture, after) = pinned_conjunct(128, "=", WIDE_PIN, 0);
    let chain = strictly_checked_chain(&mut fixture, after);
    assert!(has_rule(&chain, AletheRule::Evaluate), "{chain:?}");
    assert!(
        !has_lemma(&chain, &TheoryLemmaKind::BvLiaTautology),
        "a 128-bit fold is outside the bounded interpreter: {chain:?}"
    );
}

/// GREEN: a wide unsigned comparison folds to `true` and takes the same
/// route; the ground evaluator orders 128-bit literals exactly.
#[test]
fn wide_bv_unsigned_comparison_closes_with_a_checked_evaluate() {
    let (mut fixture, after) = pinned_conjunct(128, "bvult", WIDE_PIN, WIDE_PIN + 1);
    let chain = strictly_checked_chain(&mut fixture, after);
    assert!(has_rule(&chain, AletheRule::Evaluate), "{chain:?}");
}

/// UNCHANGED: inside the bounded interpreter's fragment the fold keeps the
/// `BvLiaTautology` route, so every proof that route already closed is
/// emitted as before.
#[test]
fn in_fragment_bv_pin_keeps_the_bounded_tautology() {
    let (mut fixture, after) = pinned_conjunct(64, "=", 42, 0);
    let chain = strictly_checked_chain(&mut fixture, after);
    assert!(
        has_lemma(&chain, &TheoryLemmaKind::BvLiaTautology),
        "{chain:?}"
    );
    assert!(!has_rule(&chain, AletheRule::Evaluate), "{chain:?}");
}

/// `(= y (bvadd w 1))` under the pin `(= w c)`: `(bvadd c 1)` collapses to a
/// literal, and the recorded `after` is the pass's own rebuild.
fn pinned_sum(width: u32) -> (Fixture, TermId) {
    let mut terms = TermStore::new();
    let w = terms.mk_var("w", bv_sort(width));
    let y = terms.mk_var("y", bv_sort(width));
    let c = bv_literal(&mut terms, WIDE_PIN % (1_u128 << 63), width);
    let one = bv_literal(&mut terms, 1, width);
    let sum = terms.mk_app(Symbol::named("bvadd"), [w, one], bv_sort(width));
    let before = terms.mk_app(Symbol::named("="), [y, sum], Sort::Bool);
    let pin = terms.mk_app(Symbol::named("="), [w, c], Sort::Bool);
    let folded_sum =
        PropagateValues::fold_rebuild(&mut terms, Symbol::named("bvadd"), sum, vec![c, one]);
    assert!(
        matches!(terms.get(folded_sum), TermData::Const(_)),
        "the fixture must collapse the sum to a literal"
    );
    let after =
        PropagateValues::fold_rebuild(&mut terms, Symbol::named("="), before, vec![y, folded_sum]);

    let mut fixture = Fixture::new(vec![before, pin], terms);
    fixture.entry(w, c, pin, 1);
    fixture.record(before, after, 1);
    (fixture, after)
}

/// NEGATIVE: a wide bit-vector-valued fold has no step the strict checker
/// re-derives. The bounded interpreter stops at 64 bits, and no strict
/// `evaluate` validator admits a 128-bit `bvadd` with a bit-vector right-hand
/// side. The plan must decline instead of emitting a lemma the checker
/// refuses. The 64-bit twin plans, so the decline comes from the route and
/// not from the record shape.
#[test]
fn wide_bv_valued_fold_without_a_strict_route_declines() {
    let (mut narrow, narrow_after) = pinned_sum(64);
    let narrow_chain = strictly_checked_chain(&mut narrow, narrow_after);
    assert!(
        has_lemma(&narrow_chain, &TheoryLemmaKind::BvLiaTautology),
        "{narrow_chain:?}"
    );

    let (mut wide, wide_after) = pinned_sum(128);
    assert!(
        wide.plan(wide_after).is_none(),
        "a closed fold no strict route closes must fail the plan"
    );
}

/// END TO END: the reduced model-checker-consumer query publishes `unsat` through the
/// caller-authored boundary in the CLI's default posture: a synthesized Alethe
/// artifact, so best-effort proof production with the CLI's 1M-step budget.
/// Before the checker chose the closing step, the replay's refused
/// `BvLiaTautology` rejected the whole certificate: `unknown (incomplete
/// self-check-rejected)`.
#[test]
fn reduced_realloc_validation_query_publishes_unsat_in_the_default_posture() {
    let script = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/fixtures/closed_fold_wide_bv_pin_with_array_conjunct.smt2"
    ));
    let commands = ay_frontend::parse(script).expect("fixture must parse");
    let mut executor = Executor::new();
    executor.set_best_effort_produce_proofs(1_000_000);
    let mut outputs = Vec::new();
    for command in &commands {
        if let Some(line) = executor
            .execute_authored(command)
            .expect("fixture must execute")
        {
            outputs.push(line);
        }
    }
    let admission = executor.last_command_unsat_admission_tag();
    let reason = executor
        .execute(&ay_frontend::Command::GetInfo(
            ":reason-unknown".to_string(),
        ))
        .ok()
        .flatten();
    assert_eq!(outputs, ["unsat"], "reason-unknown: {reason:?}");
    assert_eq!(
        admission,
        Some("strict-proof"),
        "the published unsat must be admitted by a strict proof"
    );
}

/// NEGATIVE: a wide `bv2nat` fold (`ubv_to_int` after elaboration) is one the
/// strict ground evaluator admits, but pinned Carcara cannot parse `bv2nat`,
/// so a published `evaluate` step over it makes the document invalid. The
/// plan must decline. Without the head allowlist the planner closes it with
/// `(= (bv2nat c) n) :rule evaluate`, which the strict checker accepts.
#[test]
fn wide_bv2nat_fold_declines_because_pinned_carcara_cannot_parse_it() {
    let mut terms = TermStore::new();
    let w = terms.mk_var("w", bv_sort(128));
    let y = terms.mk_var("y", Sort::Int);
    let c = bv_literal(&mut terms, WIDE_PIN, 128);
    let nat = terms.mk_app(Symbol::named("bv2nat"), [w], Sort::Int);
    let before = terms.mk_app(Symbol::named("="), [y, nat], Sort::Bool);
    let pin = terms.mk_app(Symbol::named("="), [w, c], Sort::Bool);
    let folded_nat =
        PropagateValues::fold_rebuild(&mut terms, Symbol::named("bv2nat"), nat, vec![c]);
    assert!(
        matches!(terms.get(folded_nat), TermData::Const(Constant::Int(_))),
        "the fixture must collapse the conversion to an integer literal"
    );
    let raw = terms.mk_app(Symbol::named("bv2nat"), [c], Sort::Int);
    let evaluate = terms.mk_app(Symbol::named("="), [raw, folded_nat], Sort::Bool);
    assert!(
        ay_proof::recognize_ground_evaluate(&terms, evaluate),
        "the strict evaluator admits the step, so only the head allowlist declines it"
    );
    let after =
        PropagateValues::fold_rebuild(&mut terms, Symbol::named("="), before, vec![y, folded_nat]);
    let mut fixture = Fixture::new(vec![before, pin], terms);
    fixture.entry(w, c, pin, 1);
    fixture.record(before, after, 1);
    assert!(
        fixture.plan(after).is_none(),
        "a closed fold pinned Carcara cannot parse must fail the plan"
    );
}

/// NEGATIVE (#4751): when the plan's target is the literal constant the fold
/// concludes, a wide closed fold declines as every other constant-fold bridge
/// does, so the original-assertion rebuild keeps that preprocessing-time
/// refutation. Measured on the CLI with `(= w c)` and `(= w 5)` both asserted
/// over a 128-bit `w`: closing this fold with `evaluate` turned a
/// `trust_free=yes`, Carcara-`valid` certificate into a holey one. The twin
/// without a constant target still plans, so the decline is the guard's.
#[test]
fn wide_bv_fold_to_the_constant_target_is_left_to_the_original_assertion_rebuild() {
    let mut terms = TermStore::new();
    let w = terms.mk_var("w", bv_sort(128));
    let c = bv_literal(&mut terms, WIDE_PIN, 128);
    let five = bv_literal(&mut terms, 5, 128);
    let pin = terms.mk_app(Symbol::named("="), [w, c], Sort::Bool);
    let clash = terms.mk_app(Symbol::named("="), [w, five], Sort::Bool);
    let false_term = terms.false_term();

    let mut fixture = Fixture::new(vec![pin, clash], terms);
    fixture.entry(w, c, pin, 1);
    fixture.record(clash, false_term, 1);
    assert!(
        fixture.plan_with_constant_target(false_term).is_none(),
        "a literal-constant target must stay with the original-assertion rebuild"
    );
    assert!(
        fixture.plan(false_term).is_some(),
        "without a constant target the same fold closes with `evaluate`"
    );
}
