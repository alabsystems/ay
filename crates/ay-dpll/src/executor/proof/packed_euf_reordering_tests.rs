// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the packed-EUF `reordering` lane.
//!
//! The pass places no authority of its own — it names two rules the strict
//! checker then re-runs — so the tests are DIFFERENTIAL: the headline test
//! builds a COMPLETE refutation, shows the UNTOUCHED strict checker rejects it
//! before the pass, and shows the same checker accepts it after. Every decline
//! is shown to leave both steps byte-identical.
//!
//! `GUARD_MUTATION_LEDGER` — each guard deleted or weakened, the crate's tests
//! re-run, the named test OBSERVED failing, then restored. Run recorded
//! 2026-08-22:
//!
//! | guard | mutation | test observed failing | class |
//! |---|---|---|---|
//! | not already accepted as recorded | drop the check | `a_leaf_already_in_validator_order_is_left_to_the_intrinsic_sweep` | scope (ownership) |
//! | `premises.is_empty() && args.is_empty()` | drop both conjuncts | `a_trust_step_with_premises_is_left_alone` | soundness |
//! | exactly one positive literal (`conclusion_last`) | take the FIRST positive instead of demanding uniqueness | NONE — 18/18 passed at the time of the run | SCOPE, see below |
//! | `recognize_euf_transitive(&permuted)` | drop the check | `a_broken_chain_is_left_alone` | soundness |
//! | consumer is `AletheRule::Or` | accept any consumer rule | `a_leaf_whose_consumer_is_not_an_or_step_is_left_alone` | soundness |
//! | consumer clause `== flat` | drop the comparison | `a_consumer_whose_clause_is_not_the_flattened_children_is_left_alone` | soundness |
//! | exactly one reference | take the first reference | `a_leaf_with_a_second_consumer_is_left_alone` | soundness |
//! | `consumer > index` | drop the ordering check | `a_consumer_that_precedes_its_leaf_is_left_alone` | soundness |
//! | surface-override renderability | drop the check | `a_leaf_whose_hypothesis_prints_unrenderably_is_left_alone` | fail-closed (rejection class) |
//!
//! NEGATIVE RESULT, recorded rather than hidden. Weakening the uniqueness
//! requirement in `conclusion_last` to "take the first positive literal" fails
//! NO test, because the validator ALREADY rejects every such clause: with two
//! or more positive literals, moving one last leaves another positive literal
//! among the premises, and `validate_euf_transitive` requires every premise to
//! be a NEGATED equality. The property that makes the requirement redundant is
//! pinned directly by
//! `no_permutation_of_a_two_positive_clause_is_ever_accepted`, so it is a
//! readability/fail-fast condition rather than a guard.

use super::*;

use ay_core::{Sort, Symbol, TermId};

/// `a`, `b`, `c` over one uninterpreted sort, plus the three equalities the
/// transitivity chain uses.
pub(super) struct Chain {
    eq_ab: TermId,
    eq_ca: TermId,
    eq_cb: TermId,
    not_ab: TermId,
    not_ca: TermId,
}

pub(super) fn chain(executor: &mut Executor, tag: &str) -> Chain {
    let sort = Sort::Uninterpreted("EufSort".to_string());
    let a = executor.ctx.terms.mk_var(format!("{tag}_a"), sort.clone());
    let b = executor.ctx.terms.mk_var(format!("{tag}_b"), sort.clone());
    let c = executor.ctx.terms.mk_var(format!("{tag}_c"), sort);
    let eq_ab = executor.ctx.terms.mk_eq(a, b);
    let eq_ca = executor.ctx.terms.mk_eq(c, a);
    let eq_cb = executor.ctx.terms.mk_eq(c, b);
    let not_ab = executor.ctx.terms.mk_not_raw(eq_ab);
    let not_ca = executor.ctx.terms.mk_not_raw(eq_ca);
    Chain {
        eq_ab,
        eq_ca,
        eq_cb,
        not_ab,
        not_ca,
    }
}

pub(super) fn or_term(executor: &mut Executor, literals: Vec<TermId>) -> TermId {
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), literals, Sort::Bool)
}

pub(super) fn trust_leaf(clause: Vec<TermId>) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::Trust,
        clause,
        premises: Vec::new(),
        args: Vec::new(),
    }
}

pub(super) fn or_step(clause: Vec<TermId>, premise: u32) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::Or,
        clause,
        premises: vec![ProofId(premise)],
        args: Vec::new(),
    }
}

/// The exact pair the demotion leaves behind: a premiseless `trust` over the
/// packed `or`, and the `or` step that flattens it. The conclusion equality
/// sits in the MIDDLE, which is what `validate_euf_transitive` refuses.
fn demoted_pair(executor: &mut Executor, link: &Chain) -> (Proof, Vec<TermId>) {
    let flat = vec![link.not_ab, link.eq_cb, link.not_ca];
    let packed = or_term(executor, flat.clone());
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    proof.add_step(or_step(flat.clone(), 0));
    (proof, flat)
}

pub(super) fn is_reordering_of(step: &ProofStep, expected: &[TermId], premise: u32) -> bool {
    matches!(
        step,
        ProofStep::Step { rule: AletheRule::Reordering, clause, premises, args }
            if clause.as_slice() == expected
                && premises.as_slice() == [ProofId(premise)]
                && args.is_empty()
    )
}

// ==========================================================================
// 1. The gap, and the differential proof that it closes
// ==========================================================================

/// PRECONDITION, measured rather than assumed: the recorded order is REJECTED
/// by the existing validator and the permuted order is ACCEPTED. Everything
/// else in this file rests on that asymmetry.
#[test]
fn the_recorded_order_is_rejected_and_the_permutation_is_accepted() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "pre");
    let flat = vec![link.not_ab, link.eq_cb, link.not_ca];
    let packed = or_term(&mut executor, flat.clone());
    let terms = &executor.ctx.terms;
    assert!(
        !ay_proof::recognize_euf_transitive(terms, &[packed]),
        "the PACKED unit must be rejected — the conclusion is not last"
    );
    assert!(
        !ay_proof::recognize_euf_transitive(terms, &flat),
        "the FLAT clause in recorded order must be rejected too"
    );
    let permuted = vec![link.not_ab, link.not_ca, link.eq_cb];
    assert!(
        ay_proof::recognize_euf_transitive(terms, &permuted),
        "the permutation with the conclusion LAST must be accepted"
    );
}

/// THE HEADLINE. A complete refutation that the untouched strict checker
/// REJECTS before the pass and ACCEPTS after, with the consumer's clause
/// byte-identical across the rewrite.
#[test]
fn a_complete_refutation_goes_from_strict_rejected_to_strict_accepted() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "e2e");
    let flat = vec![link.not_ab, link.eq_cb, link.not_ca];
    let packed = or_term(&mut executor, flat.clone());
    let not_cb = executor.ctx.terms.mk_not_raw(link.eq_cb);

    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(link.eq_ab)); // t0
    proof.add_step(ProofStep::Assume(link.eq_ca)); // t1
    proof.add_step(ProofStep::Assume(not_cb)); // t2
    proof.add_step(trust_leaf(vec![packed])); // t3
    proof.add_step(or_step(flat.clone(), 3)); // t4
    proof.add_step(ProofStep::Resolution {
        clause: vec![link.eq_cb, link.not_ca],
        pivot: link.eq_ab,
        clause1: ProofId(4),
        clause2: ProofId(0),
    }); // t5
    proof.add_step(ProofStep::Resolution {
        clause: vec![link.eq_cb],
        pivot: link.eq_ca,
        clause1: ProofId(5),
        clause2: ProofId(1),
    }); // t6
    proof.add_step(ProofStep::Resolution {
        clause: Vec::new(),
        pivot: link.eq_cb,
        clause1: ProofId(6),
        clause2: ProofId(2),
    }); // t7

    let before = ay_proof::check_proof_strict(&proof, &executor.ctx.terms);
    assert!(
        before.is_err(),
        "precondition: the demoted trust leaf must make the proof strict-REJECTED"
    );

    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        1
    );

    match &proof.steps[3] {
        ProofStep::TheoryLemma { kind, clause, .. } => {
            assert_eq!(*kind, TheoryLemmaKind::EufTransitive);
            assert_eq!(
                clause,
                &vec![link.not_ab, link.not_ca, link.eq_cb],
                "the leaf carries the validator's accepted order"
            );
        }
        other => panic!("expected the leaf to become an EUF lemma, got {other:?}"),
    }
    assert!(
        is_reordering_of(&proof.steps[4], &flat, 3),
        "the consumer must become `reordering` with its clause UNCHANGED"
    );

    ay_proof::check_proof_strict(&proof, &executor.ctx.terms)
        .expect("the UNTOUCHED strict checker must accept the rewritten refutation");
}

/// The rewrite is LOCAL: no step is added, removed or renumbered, and every
/// step other than the two it touches is byte-identical.
#[test]
fn the_rewrite_adds_no_step_and_leaves_every_other_step_untouched() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "local");
    let (mut proof, flat) = demoted_pair(&mut executor, &link);
    // A downstream consumer of the `or` step's clause — NOT of the leaf, which
    // must keep exactly one reference for the lane to fire.
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Contraction,
        clause: flat.clone(),
        premises: vec![ProofId(1)],
        args: Vec::new(),
    });
    let before_tail = format!("{:?}", proof.steps[2]);
    let before_len = proof.steps.len();

    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        1
    );

    assert_eq!(proof.steps.len(), before_len, "no step may be added");
    assert_eq!(format!("{:?}", proof.steps[2]), before_tail);
    assert!(is_reordering_of(&proof.steps[1], &flat, 0));
}

/// Running the pass twice is a no-op: the second call finds no `trust` leaf.
#[test]
fn the_pass_is_idempotent() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "idem");
    let (mut proof, _flat) = demoted_pair(&mut executor, &link);
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        1
    );
    let after = format!("{:?}", proof.steps);
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        0
    );
    assert_eq!(format!("{:?}", proof.steps), after);
}

// ==========================================================================
// 2. Adversarial negatives — each names a concrete falsifying assignment
// ==========================================================================

/// A clause whose chain is BROKEN. FALSIFIED AT `a = b = 0`, `c = d = 1`:
/// `(= a b)` holds so `(not (= a b))` is false, `(= c d)` holds so
/// `(not (= c d))` is false, and the conclusion `(= c b)` is `1 = 0`, false.
/// Every disjunct is false, so the clause is FALSE and no reordering of it may
/// be promoted — doing so would emit a step the checker rejects, trading a
/// rescuable `trust` rejection for a hard `InvalidTheoryLemma` one.
#[test]
fn a_broken_chain_is_left_alone() {
    let mut executor = Executor::new();
    let sort = Sort::Uninterpreted("EufSort".to_string());
    let a = executor.ctx.terms.mk_var("brk_a", sort.clone());
    let b = executor.ctx.terms.mk_var("brk_b", sort.clone());
    let c = executor.ctx.terms.mk_var("brk_c", sort.clone());
    let d = executor.ctx.terms.mk_var("brk_d", sort);
    let eq_ab = executor.ctx.terms.mk_eq(a, b);
    let eq_cd = executor.ctx.terms.mk_eq(c, d);
    let eq_cb = executor.ctx.terms.mk_eq(c, b);
    let not_ab = executor.ctx.terms.mk_not_raw(eq_ab);
    let not_cd = executor.ctx.terms.mk_not_raw(eq_cd);
    let flat = vec![not_ab, eq_cb, not_cd];
    // The falsifying assignment, CHECKED through the validator rather than
    // asserted: no permutation of a false clause is a transitivity chain.
    let permuted = vec![not_ab, not_cd, eq_cb];
    assert!(
        !ay_proof::recognize_euf_transitive(&executor.ctx.terms, &permuted),
        "the broken chain is FALSE at a=b=0, c=d=1 and must not be recognized"
    );
    let packed = or_term(&mut executor, flat.clone());
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    proof.add_step(or_step(flat, 0));
    let before = format!("{:?}", proof.steps);
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        0
    );
    assert_eq!(format!("{:?}", proof.steps), before);
}

/// Two positive literals: `(or (= a b) (= c b) (not (= c a)))`. Moving either
/// one last leaves the other as a "premise" that is not a NEGATED equality, so
/// the validator refuses — but a producer that guessed would be picking which
/// half of a disjunction to believe. FALSIFIED AT `a = 0, b = 1, c = 2`:
/// `(= a b)` false, `(= c b)` false, `(= c a)` false so `(not (= c a))` is
/// TRUE — so this particular clause is not false, but its EUF reading is not
/// justified, and the guard declines rather than assert one.
#[test]
fn a_clause_with_two_positive_literals_is_left_alone() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "twopos");
    let flat = vec![link.eq_ab, link.eq_cb, link.not_ca];
    let packed = or_term(&mut executor, flat.clone());
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    proof.add_step(or_step(flat, 0));
    let before = format!("{:?}", proof.steps);
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        0
    );
    assert_eq!(format!("{:?}", proof.steps), before);
}

/// No positive literal at all — `(or (not (= a b)) (not (= c a)))`. FALSIFIED
/// AT `a = b = c = 0`: both equalities hold, so both disjuncts are false and
/// the clause is FALSE.
#[test]
fn a_clause_with_no_positive_literal_is_left_alone() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "nopos");
    let flat = vec![link.not_ab, link.not_ca];
    let packed = or_term(&mut executor, flat.clone());
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    proof.add_step(or_step(flat, 0));
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        0
    );
}

/// The property the `conclusion_last` uniqueness requirement rests on, pinned
/// DIRECTLY rather than through the pass: for a clause with two positive
/// literals, NO choice of which one to move last is accepted, because the
/// other one is then a premise that is not a negated equality.
#[test]
fn no_permutation_of_a_two_positive_clause_is_ever_accepted() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "sweep");
    let flat = vec![link.eq_ab, link.eq_cb, link.not_ca];
    let terms = &executor.ctx.terms;
    for chosen in 0..flat.len() {
        if matches!(terms.get(flat[chosen]), TermData::Not(_)) {
            continue;
        }
        let mut permuted = flat.clone();
        let conclusion = permuted.remove(chosen);
        permuted.push(conclusion);
        assert!(
            !ay_proof::recognize_euf_transitive(terms, &permuted),
            "moving positive literal {chosen} last must still be rejected"
        );
    }
}

#[path = "packed_euf_reordering_guard_tests.rs"]
mod guards;
