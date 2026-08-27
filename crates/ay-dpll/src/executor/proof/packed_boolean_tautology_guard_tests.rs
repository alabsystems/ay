// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The packed Boolean-tautology lane's ADVERSARIAL NEGATIVES, its GUARD
//! MUTATION fixtures and its WIRE check — sections 3 to 5 of
//! `packed_boolean_tautology_tests.rs`, split out only to keep each file
//! inside the repository's 500-line ceiling.
//!
//! Every fixture here is a COMPLETE refutation for the reason the sibling file
//! records, and every negative names a concrete falsifying assignment and
//! CHECKS it with the independent truth-table oracle before asserting that the
//! lane declines.

use super::super::*;

use super::tests::{
    atoms, complete_refutation, falsifying_assignment, or_term, run_lane, trust_leaf,
};

// ===== 3. adversarial negatives, each with a CHECKED falsifying assignment ==

/// A clause over THREE distinct atoms is not an equivalence tautology, and the
/// lane leaves it byte-identical.
///
/// Falsifying assignment, CHECKED in-test: `X = true`, `Y = false`,
/// `Z = false` makes `(= X Y)` false, `(not X)` false and `(not Z)` true —
/// so the third literal is replaced to make every literal false below.
#[test]
fn a_clause_over_three_distinct_atoms_is_refused_with_a_named_counterexample() {
    let mut executor = Executor::new();
    let a = atoms(&mut executor);
    let not_x = executor.ctx.terms.mk_not(a.x);
    let literals = vec![a.eq_xy, not_x, a.z];
    let witness = falsifying_assignment(&executor.ctx.terms, &[a.x, a.y, a.z], &literals)
        .expect("this clause MUST be falsifiable, or the negative is vacuous");
    // Name the assignment explicitly: X true, Y false, Z false.
    let named: Vec<bool> = [a.x, a.y, a.z]
        .iter()
        .map(|atom| {
            witness
                .iter()
                .find(|(term, _)| term == atom)
                .expect("bound")
                .1
        })
        .collect();
    assert_eq!(
        named,
        vec![true, false, false],
        "the falsifying assignment is X=true, Y=false, Z=false"
    );
    assert!(
        executor.strict_checked_tautology_rule(&literals).is_none(),
        "the checker must refuse a falsifiable clause"
    );
    let (mut proof, _, _) = complete_refutation(&mut executor, &literals);
    let before = proof.steps.clone();
    assert_eq!(run_lane(&mut executor, &mut proof), 0);
    assert_eq!(
        proof.steps.len(),
        before.len(),
        "a refused leaf must leave the proof byte-identical"
    );
}

/// A two-literal packed leaf that is NOT a tautology is refused.
///
/// Falsifying assignment, CHECKED in-test: `X = false`, `Y = false` falsifies
/// both `X` and `Y`.
#[test]
fn a_falsifiable_two_literal_leaf_is_refused() {
    let mut executor = Executor::new();
    let a = atoms(&mut executor);
    let literals = vec![a.x, a.y];
    let witness = falsifying_assignment(&executor.ctx.terms, &[a.x, a.y], &literals)
        .expect("X or Y is falsifiable");
    assert!(
        witness.iter().all(|(_, value)| !*value),
        "the falsifying assignment sets both atoms FALSE: {witness:?}"
    );
    assert!(executor.strict_checked_tautology_rule(&literals).is_none());
    let (mut proof, _, _) = complete_refutation(&mut executor, &literals);
    assert_eq!(run_lane(&mut executor, &mut proof), 0);
}

/// The WRONG-polarity equivalence — `(= X Y) ∨ X ∨ (not Y)` — is refused.
///
/// Falsifying assignment, CHECKED in-test: `X = false`, `Y = true`.
#[test]
fn a_wrong_polarity_equivalence_is_refused() {
    let mut executor = Executor::new();
    let a = atoms(&mut executor);
    let not_y = executor.ctx.terms.mk_not(a.y);
    let literals = vec![a.eq_xy, a.x, not_y];
    let witness = falsifying_assignment(&executor.ctx.terms, &[a.x, a.y], &literals)
        .expect("this mixed polarity is falsifiable");
    let x_value = witness.iter().find(|(t, _)| *t == a.x).expect("bound").1;
    let y_value = witness.iter().find(|(t, _)| *t == a.y).expect("bound").1;
    assert_eq!(
        (x_value, y_value),
        (false, true),
        "the falsifying assignment is X=false, Y=true"
    );
    assert!(executor.strict_checked_tautology_rule(&literals).is_none());
    let (mut proof, _, _) = complete_refutation(&mut executor, &literals);
    assert_eq!(run_lane(&mut executor, &mut proof), 0);
}

// ===== 4. guard mutations =====

/// GUARD 1 (SCOPE, not soundness — RE-AIMED, and the finding is recorded):
/// a `trust` step that carries a PREMISE is not a leaf this lane replaces.
///
/// The first version of this test used a two-step fixture and came back GREEN
/// under its own mutation, because a fixture that is not a refutation makes
/// `commit_bridge_fragments` revert whatever the guard does. This version is a
/// COMPLETE refutation in which the premised leaf's clause is the same packed
/// tautology, so the lane really would rewrite it with the guard gone.
///
/// Mutation ledger entry 1: deleting `premises.is_empty()` makes this test
/// RED — but only AFTER the re-aim. With the two-step fixture it came back
/// STILL PASSED, because a fixture that is not a refutation makes the commit
/// gate revert whatever the guard does. Recorded because the mutated lane is
/// not UNSOUND — the fragment is a closed derivation of the SAME clause,
/// re-validated by the strict checker — it orphans the premise's own
/// derivation, so the guard is scope that the test now pins behaviourally.
#[test]
fn a_trust_step_with_a_premise_is_left_alone() {
    let mut executor = Executor::new();
    let a = atoms(&mut executor);
    let not_x = executor.ctx.terms.mk_not(a.x);
    let not_y = executor.ctx.terms.mk_not(a.y);
    let literals = vec![a.eq_xy, not_x, not_y];
    let packed = or_term(&mut executor, literals.clone());
    // PRECONDITION: the very same clause, premiseless, IS rewritten. Without
    // this the test could pass because the clause is out of scope entirely.
    {
        let mut control = Executor::new();
        let c = atoms(&mut control);
        let c_not_x = control.ctx.terms.mk_not(c.x);
        let c_not_y = control.ctx.terms.mk_not(c.y);
        let (mut proof, _, _) = complete_refutation(&mut control, &[c.eq_xy, c_not_x, c_not_y]);
        assert_eq!(
            run_lane(&mut control, &mut proof),
            1,
            "the premiseless control must be rewritten, or the guard is not what declines"
        );
    }
    // A COMPLETE refutation whose leaf carries a premise.
    let mut proof = Proof::new();
    let root = proof.add_step(ProofStep::Assume(a.x));
    let leaf = proof.add_step(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![packed],
        premises: vec![root],
        args: Vec::new(),
    });
    let mut current = proof.add_step(ProofStep::Step {
        rule: AletheRule::Or,
        clause: literals.clone(),
        premises: vec![leaf],
        args: Vec::new(),
    });
    let mut remaining = literals.clone();
    let mut assumptions = vec![a.x];
    for &literal in &literals {
        let negated = executor.ctx.terms.mk_not(literal);
        assumptions.push(negated);
        let assumed = proof.add_step(ProofStep::Assume(negated));
        remaining.retain(|&other| other != literal);
        current = proof.add_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: remaining.clone(),
            premises: vec![current, assumed],
            args: Vec::new(),
        });
    }
    let _ = current;
    executor.set_self_check_authored_assertions_for_tests(assumptions);
    let before = proof.steps.clone();
    assert_eq!(run_lane(&mut executor, &mut proof), 0);
    assert_eq!(proof.steps.len(), before.len());
    assert!(
        matches!(
            proof.steps.get(1),
            Some(ProofStep::Step { rule: AletheRule::Trust, premises, .. }) if !premises.is_empty()
        ),
        "the premised trust step must be untouched"
    );
}

/// GUARD 1 (SCOPE — RE-AIMED): a leaf whose clause is NOT a packed `or` unit
/// is counted out before anything is planned.
///
/// RE-AIMED for the same reason: the fixture is a COMPLETE refutation of a
/// FLAT three-literal `equiv_neg1` clause — a clause the strict checker
/// accepts outright — so with the shape test gone the lane genuinely reaches
/// it.
///
/// Mutation ledger entry 2: replacing the `or` test with `Some(clause)` leaves
/// this GREEN, and that is an HONEST NEGATIVE. The mutated lane treats the
/// clause's FIRST literal as the packed term, builds `(cl l1 (not l1))` under
/// `or_neg`, and guard 3's replay refuses it because `l1` is not a
/// disjunction. The shape test is the CHEAP way to count the leaf out, not
/// the thing that keeps it sound.
#[test]
fn a_flat_multi_literal_trust_leaf_is_out_of_scope() {
    let mut executor = Executor::new();
    let a = atoms(&mut executor);
    let not_x = executor.ctx.terms.mk_not(a.x);
    let not_y = executor.ctx.terms.mk_not(a.y);
    let literals = vec![a.eq_xy, not_x, not_y];
    // PRECONDITION: the strict checker accepts this clause FLAT, so the only
    // thing standing between the lane and it is the packed-shape test.
    assert!(
        executor.strict_checked_tautology_rule(&literals).is_some(),
        "the flat clause must be checker-accepted, or the guard is not what declines"
    );
    let mut proof = Proof::new();
    let leaf = proof.add_step(trust_leaf(literals.clone()));
    let mut current = leaf;
    let mut remaining = literals.clone();
    let mut assumptions = Vec::new();
    for &literal in &literals {
        let negated = executor.ctx.terms.mk_not(literal);
        assumptions.push(negated);
        let assumed = proof.add_step(ProofStep::Assume(negated));
        remaining.retain(|&other| other != literal);
        current = proof.add_step(ProofStep::Step {
            rule: AletheRule::Resolution,
            clause: remaining.clone(),
            premises: vec![current, assumed],
            args: Vec::new(),
        });
    }
    let _ = current;
    assert!(
        matches!(proof.steps.last(), Some(ProofStep::Step { clause, .. }) if clause.is_empty()),
        "the fixture must be a COMPLETE refutation"
    );
    executor.set_self_check_authored_assertions_for_tests(assumptions);
    let before = proof.steps.clone();
    assert_eq!(run_lane(&mut executor, &mut proof), 0);
    assert_eq!(proof.steps.len(), before.len());
}

/// GUARD 2: the rule is named by the UNTOUCHED strict checker, from the flat
/// clause alone — a clause it refuses under EVERY candidate is never planned.
///
/// Mutation ledger entry 3: returning `Some(EquivNeg1)` from
/// `strict_checked_tautology_rule` without consulting the checker makes this
/// RED, and the two adversarial negatives above RED as well.
#[test]
fn the_strict_checker_is_the_only_thing_that_names_the_rule() {
    let mut executor = Executor::new();
    let a = atoms(&mut executor);
    let not_x = executor.ctx.terms.mk_not(a.x);
    // A clause with a REPEATED equality and no complementary pair.
    let literals = vec![a.eq_xy, a.eq_xy, not_x];
    assert!(
        falsifying_assignment(&executor.ctx.terms, &[a.x, a.y], &literals).is_some(),
        "the fixture must be falsifiable"
    );
    assert!(executor.strict_checked_tautology_rule(&literals).is_none());
}

/// GUARD 3/4: the closed RE-PACKED fragment is replayed, and the fragment ends
/// on exactly the leaf's clause.
///
/// Mutation ledger entry 4: dropping the `check_proof_strict` call in
/// `plan_packed_tautology_fragment` leaves this test GREEN — it is defence in
/// depth behind guard 2 and `repack_derivation`'s own postcondition — and that
/// is recorded as an HONEST NEGATIVE rather than claimed as coverage. What IS
/// pinned directly is the postcondition itself.
#[test]
fn the_fragment_ends_on_exactly_the_leaf_clause() {
    let mut executor = Executor::new();
    let a = atoms(&mut executor);
    let not_x = executor.ctx.terms.mk_not(a.x);
    let not_y = executor.ctx.terms.mk_not(a.y);
    let literals = vec![a.eq_xy, not_x, not_y];
    let packed = or_term(&mut executor, literals.clone());
    let fragment = executor
        .plan_packed_tautology_fragment(packed, &literals)
        .expect("the measured head must plan");
    let Some(ProofStep::Step { clause, .. }) = fragment.last() else {
        panic!("the fragment must end on a step");
    };
    assert_eq!(
        clause.as_slice(),
        [packed],
        "the fragment's last clause must be the leaf's, byte for byte"
    );
}

/// GUARD 6: the whole-proof commit gate reverts a rewrite that would cost the
/// proof its certification.
///
/// The fixture is a complete refutation whose OTHER steps do not check, so the
/// rebuilt proof cannot check either and `commit_bridge_fragments` must revert
/// wholesale rather than ship a broken proof.
///
/// Mutation ledger entry 5: removing the `check_proof` arm of
/// `commit_bridge_fragments` makes this RED.
#[test]
fn a_rewrite_that_breaks_the_proof_is_reverted_wholesale() {
    let mut executor = Executor::new();
    let a = atoms(&mut executor);
    let not_x = executor.ctx.terms.mk_not(a.x);
    let not_y = executor.ctx.terms.mk_not(a.y);
    let literals = vec![a.eq_xy, not_x, not_y];
    let packed = or_term(&mut executor, literals.clone());
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    // A BROKEN consumer: a resolution whose clause does not follow.
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![ProofId(0)],
        args: Vec::new(),
    });
    let before = proof.steps.clone();
    assert_eq!(
        run_lane(&mut executor, &mut proof),
        0,
        "a rewrite that leaves the proof unchecked must be reverted"
    );
    assert_eq!(proof.steps.len(), before.len());
    assert!(
        matches!(
            proof.steps.first(),
            Some(ProofStep::Step {
                rule: AletheRule::Trust,
                ..
            })
        ),
        "the reverted proof keeps its original trust leaf"
    );
}

// ===== 5. the wire =====

/// The fragment prints its OWN rules on the Alethe wire — no `hole`, no
/// `trust` — and the exact rule names are pinned.
#[test]
fn the_packed_tautology_fragment_prints_its_own_rules_on_the_wire() {
    let mut executor = Executor::new();
    let a = atoms(&mut executor);
    let not_x = executor.ctx.terms.mk_not(a.x);
    let not_y = executor.ctx.terms.mk_not(a.y);
    let literals = vec![a.eq_xy, not_x, not_y];
    let (mut proof, _, _) = complete_refutation(&mut executor, &literals);
    assert_eq!(run_lane(&mut executor, &mut proof), 1);
    let document = ay_proof::try_export_alethe(&proof, &executor.ctx.terms)
        .expect("the spliced proof must render");
    assert!(
        !document.contains(":rule hole"),
        "the lane must not trade a trust step for a hole:\n{document}"
    );
    assert!(
        !document.contains(":rule trust"),
        "no trust step may survive:\n{document}"
    );
    assert!(
        document.contains(":rule equiv_neg1"),
        "the flat clause prints as equiv_neg1:\n{document}"
    );
    assert!(
        document.contains(":rule or_neg"),
        "each disjunct is re-packed by an or_neg:\n{document}"
    );
    assert!(
        document.contains(":rule th_resolution"),
        "each or_neg is discharged by th_resolution:\n{document}"
    );
}

/// Every rule this lane can emit is EXTERNALLY checkable and does not degrade
/// to `hole` on the pinned wire.
#[test]
fn every_rule_the_lane_can_emit_is_externally_checkable() {
    let mut emitted: Vec<&str> = super::PACKED_TAUTOLOGY_RULES
        .iter()
        .map(AletheRule::name)
        .collect();
    emitted.push(AletheRule::OrNeg.name());
    emitted.push(AletheRule::ThResolution.name());
    for rule in emitted {
        assert!(
            ay_core::is_checkable_alethe_rule(rule),
            "{rule} is not in the external checker's vocabulary"
        );
        assert_ne!(
            ay_core::wire_rule_name(rule),
            "hole",
            "{rule} degrades to a hole on the wire"
        );
    }
}

/// The candidate list carries no rule that needs a premise or an `:args`
/// payload: a BARE step under such a rule cannot authenticate on the pinned
/// external checker, so planning one would trade a `trust` for an `invalid`.
#[test]
fn no_candidate_rule_requires_a_premise_or_argument() {
    for rule in super::PACKED_TAUTOLOGY_RULES {
        assert!(
            !ay_core::alethe_rule_requires_premises_or_args(rule.name()),
            "{} cannot authenticate a premise-free, argument-free step",
            rule.name()
        );
    }
}
