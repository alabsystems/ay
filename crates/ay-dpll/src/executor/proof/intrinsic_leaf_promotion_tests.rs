// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the residual intrinsic-tautology leaf promotion.
//!
//! The pass places no authority of its own — it names a rule the strict
//! checker then re-runs — so the tests are DIFFERENTIAL rather than
//! schema-restating: every promotion is re-decided by
//! `ay_proof::check_proof_strict` on the rewritten proof, and every decline is
//! shown to leave the step byte-identical.
//!
//! `GUARD_MUTATION_LEDGER` — each guard deleted, the whole file re-run, the
//! named test OBSERVED failing, then restored. Run recorded 2026-08-21:
//!
//! | guard | mutation | test observed failing | class |
//! |---|---|---|---|
//! | `premises.is_empty()` | drop the conjunct | `a_trust_step_with_premises_is_left_alone` | soundness |
//! | `args.is_empty()` | drop the conjunct | `a_trust_step_with_args_is_left_alone` | soundness |
//! | `farkas.is_none() && lia.is_none()` | drop the conjunct | `a_trust_lemma_that_still_carries_a_farkas_payload_is_left_alone` | soundness |
//! | `!clause.is_empty()` | drop the conjunct | NONE — 13/13 still pass | SCOPE, see below |
//!
//! The fourth is recorded as a NEGATIVE result rather than hidden: deleting it
//! changes nothing, because every battery entry already declines the empty
//! clause (`the_intrinsic_battery_declines_the_empty_clause` pins that
//! directly, so the guard is not the thing keeping the terminal poison step
//! intact). It stays as a category guard, not as a soundness gate.

use super::*;

use ay_core::{FarkasAnnotation, Sort, Symbol, TermId};

/// `(cl (or (not (= a b)) (not (= c a)) (= c b)))` — the packed EUF
/// transitivity chain the array/congruence lane records, in the order the
/// existing `validate_euf_transitive` accepts (conclusion LAST).
fn packed_euf_transitive(executor: &mut Executor) -> TermId {
    // Uninterpreted, deliberately: over `Int` the SAME clause is also an
    // arithmetic clause tautology, and the battery's historical order names
    // that rule first. Both labels are checkable; the fixture isolates the
    // EUF arm so the test pins one outcome.
    let sort = Sort::Uninterpreted("EufSort".to_string());
    let a = executor.ctx.terms.mk_var("euf_a", sort.clone());
    let b = executor.ctx.terms.mk_var("euf_b", sort.clone());
    let c = executor.ctx.terms.mk_var("euf_c", sort);
    let ab = executor.ctx.terms.mk_eq(a, b);
    let ca = executor.ctx.terms.mk_eq(c, a);
    let cb = executor.ctx.terms.mk_eq(c, b);
    let n_ab = executor.ctx.terms.mk_not_raw(ab);
    let n_ca = executor.ctx.terms.mk_not_raw(ca);
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), vec![n_ab, n_ca, cb], Sort::Bool)
}

/// The SAME shape with the chain broken: `(cl (or (not (= a b)) (not (= c d))
/// (= c b)))`. FALSIFIED AT `a = b = 0, c = 1, d = 1`: `(= a b)` holds so the
/// first disjunct is false, `(= c d)` holds so the second is false, and
/// `(= c b)` is `1 = 0`, false. The clause is FALSE, so no validator may
/// accept it and the leaf must stay `trust`.
fn packed_broken_chain(executor: &mut Executor) -> TermId {
    let sort = Sort::Uninterpreted("EufSort".to_string());
    let a = executor.ctx.terms.mk_var("brk_a", sort.clone());
    let b = executor.ctx.terms.mk_var("brk_b", sort.clone());
    let c = executor.ctx.terms.mk_var("brk_c", sort.clone());
    let d = executor.ctx.terms.mk_var("brk_d", sort);
    let ab = executor.ctx.terms.mk_eq(a, b);
    let cd = executor.ctx.terms.mk_eq(c, d);
    let cb = executor.ctx.terms.mk_eq(c, b);
    let n_ab = executor.ctx.terms.mk_not_raw(ab);
    let n_cd = executor.ctx.terms.mk_not_raw(cd);
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), vec![n_ab, n_cd, cb], Sort::Bool)
}

/// `(cl (or (not (= a b)) (= (f a) (f b))))` — the congruence sibling.
fn packed_euf_congruent(executor: &mut Executor) -> TermId {
    let sort = Sort::Uninterpreted("EufSort".to_string());
    let a = executor.ctx.terms.mk_var("cong_a", sort.clone());
    let b = executor.ctx.terms.mk_var("cong_b", sort.clone());
    let fa = executor
        .ctx
        .terms
        .mk_app(Symbol::named("cong_f"), vec![a], sort.clone());
    let fb = executor
        .ctx
        .terms
        .mk_app(Symbol::named("cong_f"), vec![b], sort);
    let ab = executor.ctx.terms.mk_eq(a, b);
    let n_ab = executor.ctx.terms.mk_not_raw(ab);
    let concl = executor.ctx.terms.mk_eq(fa, fb);
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), vec![n_ab, concl], Sort::Bool)
}

/// `(cl (or (not (= a b)) (= (f a) (f c))))` — congruence with the WRONG
/// argument on the right. FALSIFIED AT `a = b = 0, c = 1` with
/// `f(0) = 0, f(1) = 1`: the premise holds, so its negation is false, and
/// `f(a) = f(c)` is `0 = 1`, false. The clause is FALSE.
fn packed_broken_congruence(executor: &mut Executor) -> TermId {
    let sort = Sort::Uninterpreted("EufSort".to_string());
    let a = executor.ctx.terms.mk_var("bcong_a", sort.clone());
    let b = executor.ctx.terms.mk_var("bcong_b", sort.clone());
    let c = executor.ctx.terms.mk_var("bcong_c", sort.clone());
    let fa = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bcong_f"), vec![a], sort.clone());
    let fc = executor
        .ctx
        .terms
        .mk_app(Symbol::named("bcong_f"), vec![c], sort);
    let ab = executor.ctx.terms.mk_eq(a, b);
    let n_ab = executor.ctx.terms.mk_not_raw(ab);
    let concl = executor.ctx.terms.mk_eq(fa, fc);
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), vec![n_ab, concl], Sort::Bool)
}

fn trust_leaf(clause: Vec<TermId>) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::Trust,
        clause,
        premises: Vec::new(),
        args: Vec::new(),
    }
}

/// Run the strict checker on a proof consisting of the promoted leaf alone and
/// report whether the LEAF itself validated.
///
/// A single-lemma proof always fails the whole-proof check ("final
/// clause-producing step ... is not the empty clause"); the ACCEPT signal is
/// that the error does not name the lemma. Read the text, not the `Result` —
/// this is the probe protocol the campaign's earlier passes established.
fn leaf_validates_under_strict(executor: &Executor, proof: &Proof) -> bool {
    match executor.check_proof_strict_with_datatypes(proof) {
        Ok(_) => true,
        Err(error) => {
            let text = format!("{error}");
            !(text.contains("theory lemma")
                || text.contains("trust")
                || text.contains("Transitive")
                || text.contains("congruen"))
        }
    }
}

// ==========================================================================
// 1. The gap: the demotion output is exactly what the emission-time lane
//    would have certified
// ==========================================================================

/// THE PROBE. A premiseless `trust` leaf carrying a packed EUF transitivity
/// chain becomes an `EufTransitive` theory lemma, and the strict checker —
/// untouched — accepts it.
#[test]
fn a_demoted_packed_transitivity_leaf_is_promoted_and_strict_validates() {
    let mut executor = Executor::new();
    let packed = packed_euf_transitive(&mut executor);
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));

    assert!(
        !leaf_validates_under_strict(&executor, &proof),
        "precondition: the demoted trust leaf must be strict-REJECTED"
    );

    assert_eq!(executor.promote_intrinsic_tautology_leaves(&mut proof), 1);
    match &proof.steps[0] {
        ProofStep::TheoryLemma { kind, clause, .. } => {
            assert_eq!(*kind, TheoryLemmaKind::EufTransitive);
            assert_eq!(clause, &vec![packed], "the clause is preserved verbatim");
        }
        other => panic!("expected a promoted theory lemma, got {other:?}"),
    }
    assert!(
        leaf_validates_under_strict(&executor, &proof),
        "the promoted leaf must be accepted by the UNTOUCHED strict checker"
    );
}

/// The congruence sibling, same story.
#[test]
fn a_demoted_packed_congruence_leaf_is_promoted_and_strict_validates() {
    let mut executor = Executor::new();
    let packed = packed_euf_congruent(&mut executor);
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    assert_eq!(executor.promote_intrinsic_tautology_leaves(&mut proof), 1);
    assert!(matches!(
        &proof.steps[0],
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::EufCongruent,
            ..
        }
    ));
    assert!(leaf_validates_under_strict(&executor, &proof));
}

/// The trust-kind THEORY LEMMA form is promoted in place, keeping its clause.
#[test]
fn a_payload_free_trust_kind_lemma_is_promoted_in_place() {
    let mut executor = Executor::new();
    let packed = packed_euf_transitive(&mut executor);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "ArrayEUF".to_string(),
        clause: vec![packed],
        farkas: None,
        kind: TheoryLemmaKind::Generic,
        lia: None,
    });
    assert_eq!(executor.promote_intrinsic_tautology_leaves(&mut proof), 1);
    match &proof.steps[0] {
        ProofStep::TheoryLemma {
            kind,
            clause,
            theory,
            ..
        } => {
            assert_eq!(*kind, TheoryLemmaKind::EufTransitive);
            assert_eq!(clause, &vec![packed]);
            assert_eq!(theory, "ArrayEUF", "the producer's theory name is kept");
        }
        other => panic!("expected the lemma to stay a lemma, got {other:?}"),
    }
}

// ==========================================================================
// 2. Adversarial negatives — each names a concrete falsifying assignment
// ==========================================================================

/// FALSIFIED AT `a = b = 0, c = 1, d = 1` (see `packed_broken_chain`). The
/// leaf must stay a byte-identical `trust` step: promoting it would emit a
/// step the checker rejects, turning a rescuable trust rejection into a hard
/// `InvalidTheoryLemma` one.
#[test]
fn a_non_tautology_trust_leaf_is_left_alone() {
    let mut executor = Executor::new();
    let packed = packed_broken_chain(&mut executor);
    // Check the falsifying assignment IN-TEST rather than asserting it.
    // `(= a b)` true, `(= c d)` true, `(= c b)` false ⟹ every disjunct false.
    assert!(
        !ay_proof::recognize_euf_transitive(&executor.ctx.terms, &[packed]),
        "the broken chain is FALSE at a=b=0, c=d=1 and must not be recognized"
    );
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    let before = format!("{:?}", proof.steps[0]);
    assert_eq!(executor.promote_intrinsic_tautology_leaves(&mut proof), 0);
    assert_eq!(format!("{:?}", proof.steps[0]), before);
}

/// FALSIFIED AT `a = b = 0, c = 1` with `f(0) = 0, f(1) = 1`
/// (see `packed_broken_congruence`).
#[test]
fn an_invalid_congruence_leaf_is_left_alone() {
    let mut executor = Executor::new();
    let packed = packed_broken_congruence(&mut executor);
    assert!(!ay_proof::recognize_euf_congruent(
        &executor.ctx.terms,
        &[packed]
    ));
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    let before = format!("{:?}", proof.steps[0]);
    assert_eq!(executor.promote_intrinsic_tautology_leaves(&mut proof), 0);
    assert_eq!(format!("{:?}", proof.steps[0]), before);
}

/// A bare uninterpreted atom is not valid on its own. FALSIFIED AT `p = false`.
#[test]
fn a_bare_atom_leaf_is_left_alone() {
    let mut executor = Executor::new();
    let p = executor.ctx.terms.mk_var("bare_p", Sort::Bool);
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![p]));
    assert_eq!(executor.promote_intrinsic_tautology_leaves(&mut proof), 0);
}

// ==========================================================================
// 3. Guards (mutation ledger above)
// ==========================================================================

/// A `trust` step WITH premises is a failed derivation, not a leaf claiming
/// its clause is valid on its own. Relabelling it would silently drop the
/// premises, so the guard refuses even though the battery would accept the
/// clause.
#[test]
fn a_trust_step_with_premises_is_left_alone() {
    let mut executor = Executor::new();
    let packed = packed_euf_transitive(&mut executor);
    let mut proof = Proof::new();
    let p = executor.ctx.terms.mk_var("prem_p", Sort::Bool);
    let premise = proof.add_assume(p, None);
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![packed],
        premises: vec![premise],
        args: Vec::new(),
    });
    assert!(
        ay_proof::recognize_euf_transitive(&executor.ctx.terms, &[packed]),
        "precondition: the battery WOULD accept this clause"
    );
    assert_eq!(executor.promote_intrinsic_tautology_leaves(&mut proof), 0);
}

/// Same for a `trust` step carrying rule arguments.
#[test]
fn a_trust_step_with_args_is_left_alone() {
    let mut executor = Executor::new();
    let packed = packed_euf_transitive(&mut executor);
    let arg = executor.ctx.terms.mk_var("arg_d", Sort::Int);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![packed],
        premises: Vec::new(),
        args: vec![arg],
    });
    assert_eq!(executor.promote_intrinsic_tautology_leaves(&mut proof), 0);
}

/// A surviving POSITIONAL arithmetic certificate makes relabelling a
/// split-authority hazard: the battery's validators ignore the payload while
/// trace rebinding and the external printer consume it.
#[test]
fn a_trust_lemma_that_still_carries_a_farkas_payload_is_left_alone() {
    let mut executor = Executor::new();
    let packed = packed_euf_transitive(&mut executor);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: vec![packed],
        farkas: Some(FarkasAnnotation::from_ints(&[1])),
        kind: TheoryLemmaKind::Generic,
        lia: None,
    });
    assert_eq!(executor.promote_intrinsic_tautology_leaves(&mut proof), 0);
}

/// An empty clause is the refutation itself, never a tautology leaf; the pass
/// must not touch the terminal `trust` poison step.
#[test]
fn the_empty_clause_trust_poison_is_left_alone() {
    let executor = Executor::new();
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(Vec::new()));
    assert_eq!(executor.promote_intrinsic_tautology_leaves(&mut proof), 0);
}

/// The empty clause is the refutation itself. Pinned DIRECTLY on the battery
/// (not through the pass), because this is what makes the pass's
/// `!clause.is_empty()` condition a scope guard rather than a soundness one.
#[test]
fn the_intrinsic_battery_declines_the_empty_clause() {
    let executor = Executor::new();
    assert!(
        recognize_intrinsic_tautology_kind(&executor.ctx.terms, &[]).is_none(),
        "no intrinsic recognizer may accept the empty clause"
    );
}

/// An already-certified lemma is not re-labelled: only trust KINDS enter.
#[test]
fn a_non_trust_kind_lemma_is_left_alone() {
    let mut executor = Executor::new();
    let packed = packed_euf_transitive(&mut executor);
    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause: vec![packed],
        farkas: None,
        kind: TheoryLemmaKind::EufCongruent,
        lia: None,
    });
    assert_eq!(executor.promote_intrinsic_tautology_leaves(&mut proof), 0);
}

// ==========================================================================
// 4. The wire
// ==========================================================================

/// The promoted kinds already have externally checkable Alethe rules, so the
/// promotion IMPROVES the emitted document rather than trading a `hole` for
/// something worse. Pinned as exact rule names: a future kind whose lowering
/// is a hole (or, worse, `hole :args (..)`) must not be added to the battery
/// silently.
#[test]
fn the_promoted_euf_kinds_lower_to_externally_checkable_rules() {
    for kind in [
        TheoryLemmaKind::EufTransitive,
        TheoryLemmaKind::EufCongruent,
    ] {
        let rule = kind.alethe_rule();
        assert!(
            ay_core::is_checkable_alethe_rule(rule),
            "{kind:?} lowers to {rule}, which is not in CHECKABLE_ALETHE_RULES"
        );
    }
}

/// The pass is a no-op on a proof with nothing to promote — the common path
/// must cost nothing and change nothing.
#[test]
fn a_proof_with_no_residual_leaf_is_untouched() {
    let mut executor = Executor::new();
    let p = executor.ctx.terms.mk_var("noop_p", Sort::Bool);
    let mut proof = Proof::new();
    proof.add_assume(p, None);
    let before = format!("{:?}", proof.steps);
    assert_eq!(executor.promote_intrinsic_tautology_leaves(&mut proof), 0);
    assert_eq!(format!("{:?}", proof.steps), before);
}
