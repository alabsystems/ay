// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness tests for the `reordering` rule.
//!
//! Every ADVERSARIAL NEGATIVE below names a concrete falsifying assignment and
//! CHECKS it in-test with `eval_clause`, an evaluator that shares no code with
//! the validator: it demonstrates an assignment under which the premise clause
//! is TRUE and the proposed conclusion is FALSE, i.e. the rejected step is not
//! merely out of scope but would be an unsound inference.
//!
//! # `GUARD_MUTATION_LEDGER`
//!
//! Each guard was deleted or weakened, the named test observed FAILING, and the
//! guard restored.
//!
//! | guard | mutation applied | tests observed failing | class |
//! |---|---|---|---|
//! | `let [premise] = premise_clauses` | `premise_clauses.first().copied().unwrap_or(&[])` | `a_premiseless_reordering_cannot_forge_the_empty_clause`, `more_than_one_premise_is_rejected` (13 passed / 2 failed) | SOUNDNESS |
//! | multiset comparison | arm deleted | `a_substituted_literal_is_rejected`, `a_dropped_literal_is_rejected`, `a_negated_literal_is_rejected`, `the_permutation_must_be_of_the_cited_premise`, `multiplicity_must_match_not_merely_the_literal_set` (10 passed / 5 failed) | SOUNDNESS |
//! | multiset comparison | `dedup()` both sides, i.e. compare SETS | `multiplicity_must_match_not_merely_the_literal_set` (14 passed / 1 failed) | SCOPE (external-checker parity) |
//!
//! The last row is honestly classified as SCOPE: dropping a repeated literal
//! from a disjunction is entailment-preserving, so a set comparison would not
//! be unsound. It is rejected so that `reordering` means exactly what the
//! pinned external `reordering` means.
//!
//! NEGATIVE RESULT, recorded rather than hidden: an explicit
//! `clause.len() != premise.len()` arm was written first and DELETED, because
//! removing it failed NO test (15/15 still passed) — sorted-`Vec` equality
//! already implies equal length. It is gone rather than kept as a guard no
//! test can distinguish from its absence.

use ay_core::{AletheRule, ProofId, ProofStep, Sort, TermData, TermId, TermStore};

use super::super::validate_step;
use super::ProofCheckError;

/// Assignment over the Boolean variables named in a test.
type Assignment<'a> = &'a [(&'a str, bool)];

/// Independent evaluator: no code shared with the validator.
fn eval_literal(terms: &TermStore, literal: TermId, assignment: Assignment<'_>) -> bool {
    match terms.get(literal) {
        TermData::Not(inner) => !eval_literal(terms, *inner, assignment),
        TermData::Var(name, _) => {
            let entry = assignment
                .iter()
                .find(|(var, _)| var == name)
                .expect("every variable in the clause must be assigned");
            entry.1
        }
        other => panic!("test clauses contain only variables and negations, got {other:?}"),
    }
}

/// A clause IS a disjunction: true iff some literal is true. The empty clause
/// is false under every assignment.
fn eval_clause(terms: &TermStore, clause: &[TermId], assignment: Assignment<'_>) -> bool {
    clause
        .iter()
        .any(|&literal| eval_literal(terms, literal, assignment))
}

fn check(
    terms: &TermStore,
    conclusion: Vec<TermId>,
    premises: Vec<ProofId>,
    prior: Vec<Option<Vec<TermId>>>,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::Step {
        rule: AletheRule::Reordering,
        clause: conclusion,
        premises,
        args: vec![],
    };
    let mut derived = prior;
    let step_id = ProofId(u32::try_from(derived.len()).expect("small test proof"));
    validate_step(terms, &mut derived, step_id, &step, true, None)
}

/// `a b c` plus `(not b)`, the alphabet every test below draws from.
fn alphabet() -> (TermStore, TermId, TermId, TermId, TermId) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let not_b = terms.mk_not_raw(b);
    (terms, a, b, c, not_b)
}

// ---------------------------------------------------------------- positives

#[test]
fn the_identity_permutation_is_accepted() {
    let (terms, a, b, _c, _not_b) = alphabet();
    check(&terms, vec![a, b], vec![ProofId(0)], vec![Some(vec![a, b])])
        .expect("a clause is a permutation of itself");
}

#[test]
fn a_reversed_clause_is_accepted() {
    let (terms, a, b, c, _not_b) = alphabet();
    check(
        &terms,
        vec![c, b, a],
        vec![ProofId(0)],
        vec![Some(vec![a, b, c])],
    )
    .expect("reversal is a permutation");
}

#[test]
fn repeated_literals_are_carried_as_a_multiset() {
    let (terms, a, b, _c, _not_b) = alphabet();
    check(
        &terms,
        vec![b, a, a],
        vec![ProofId(0)],
        vec![Some(vec![a, a, b])],
    )
    .expect("same literals with the same multiplicities");
}

#[test]
fn the_empty_clause_reorders_to_itself() {
    let (terms, _a, _b, _c, _not_b) = alphabet();
    check(&terms, vec![], vec![ProofId(0)], vec![Some(vec![])])
        .expect("the empty clause is its own only permutation");
}

/// The rule's whole content, decided rather than asserted: over EVERY
/// permutation of a 5-literal clause and EVERY assignment to its variables,
/// premise and conclusion have the SAME truth value — so the validator's
/// accept is an equivalence, not a one-directional entailment.
#[test]
fn every_permutation_is_accepted_and_is_truth_value_preserving() {
    let mut terms = TermStore::new();
    let vars: Vec<TermId> = ["a", "b", "c", "d", "e"]
        .iter()
        .map(|name| terms.mk_var(*name, Sort::Bool))
        .collect();
    // literals: a, (not b), c, (not d), e — a mix, so negation is exercised.
    let mut clause = Vec::new();
    for (index, &var) in vars.iter().enumerate() {
        clause.push(if index % 2 == 1 {
            terms.mk_not_raw(var)
        } else {
            var
        });
    }
    let names = ["a", "b", "c", "d", "e"];
    let mut permutations = 0usize;
    let mut indices: Vec<usize> = (0..clause.len()).collect();
    // Heap's algorithm, iterative, so all 120 permutations are visited.
    let mut counters = vec![0usize; indices.len()];
    let visit = |permuted: &[usize], terms: &TermStore| {
        let conclusion: Vec<TermId> = permuted.iter().map(|&i| clause[i]).collect();
        check(
            terms,
            conclusion.clone(),
            vec![ProofId(0)],
            vec![Some(clause.clone())],
        )
        .expect("every permutation must be accepted");
        for mask in 0..32u32 {
            let assignment: Vec<(&str, bool)> = names
                .iter()
                .enumerate()
                .map(|(bit, name)| (*name, mask & (1 << bit) != 0))
                .collect();
            assert_eq!(
                eval_clause(terms, &clause, &assignment),
                eval_clause(terms, &conclusion, &assignment),
                "permutation changed the clause's truth value at mask {mask}"
            );
        }
    };
    visit(&indices, &terms);
    permutations += 1;
    let mut i = 0usize;
    while i < indices.len() {
        if counters[i] < i {
            if i % 2 == 0 {
                indices.swap(0, i);
            } else {
                indices.swap(counters[i], i);
            }
            visit(&indices, &terms);
            permutations += 1;
            counters[i] += 1;
            i = 0;
        } else {
            counters[i] = 0;
            i += 1;
        }
    }
    assert_eq!(permutations, 120, "5! permutations must all be visited");
}

// ---------------------------------------------------- adversarial negatives

/// SOUNDNESS. With no premise there is nothing to permute, and admitting the
/// case would accept `(step t (cl) :rule reordering)` — a derivation of FALSE
/// from nothing, which forges a refutation of every satisfiable problem.
#[test]
fn a_premiseless_reordering_cannot_forge_the_empty_clause() {
    let (terms, _a, _b, _c, _not_b) = alphabet();
    let error = check(&terms, vec![], vec![], vec![])
        .expect_err("a premiseless reordering must be rejected");
    assert!(matches!(error, ProofCheckError::InvalidBooleanRule { .. }));
    // The falsifying assignment, checked: under a := true the (empty) leaf set
    // is satisfiable, and the claimed conclusion is FALSE there.
    let assignment = [("a", true)];
    assert!(
        !eval_clause(&terms, &[], &assignment),
        "the empty clause is false under a := true, so nothing entails it"
    );
}

/// SOUNDNESS. Same guard, a non-empty conclusion: `(cl a)` from nothing.
#[test]
fn a_premiseless_reordering_cannot_assert_a_literal() {
    let (terms, a, _b, _c, _not_b) = alphabet();
    let error =
        check(&terms, vec![a], vec![], vec![]).expect_err("a premiseless reordering is not a rule");
    assert!(matches!(error, ProofCheckError::InvalidBooleanRule { .. }));
    let assignment = [("a", false)];
    assert!(
        !eval_clause(&terms, &[a], &assignment),
        "a := false falsifies the asserted clause"
    );
}

/// SOUNDNESS. Swapping one literal for another is not a permutation.
#[test]
fn a_substituted_literal_is_rejected() {
    let (terms, a, b, c, _not_b) = alphabet();
    let error = check(&terms, vec![a, c], vec![ProofId(0)], vec![Some(vec![a, b])])
        .expect_err("literal substitution must be rejected");
    assert!(matches!(error, ProofCheckError::InvalidBooleanRule { .. }));
    let assignment = [("a", false), ("b", true), ("c", false)];
    assert!(
        eval_clause(&terms, &[a, b], &assignment),
        "premise (cl a b) is TRUE under a:=false b:=true c:=false"
    );
    assert!(
        !eval_clause(&terms, &[a, c], &assignment),
        "conclusion (cl a c) is FALSE under the same assignment"
    );
}

/// SOUNDNESS. Dropping a literal strengthens the clause.
#[test]
fn a_dropped_literal_is_rejected() {
    let (terms, a, b, _c, _not_b) = alphabet();
    let error = check(&terms, vec![a], vec![ProofId(0)], vec![Some(vec![a, b])])
        .expect_err("dropping a literal must be rejected");
    assert!(matches!(error, ProofCheckError::InvalidBooleanRule { .. }));
    let assignment = [("a", false), ("b", true)];
    assert!(eval_clause(&terms, &[a, b], &assignment), "premise is TRUE");
    assert!(
        !eval_clause(&terms, &[a], &assignment),
        "conclusion (cl a) is FALSE under a := false"
    );
}

/// SOUNDNESS. Negating a literal is not a permutation either.
#[test]
fn a_negated_literal_is_rejected() {
    let (terms, a, b, _c, not_b) = alphabet();
    let error = check(
        &terms,
        vec![a, not_b],
        vec![ProofId(0)],
        vec![Some(vec![a, b])],
    )
    .expect_err("negating a literal must be rejected");
    assert!(matches!(error, ProofCheckError::InvalidBooleanRule { .. }));
    let assignment = [("a", false), ("b", true)];
    assert!(eval_clause(&terms, &[a, b], &assignment), "premise is TRUE");
    assert!(
        !eval_clause(&terms, &[a, not_b], &assignment),
        "conclusion (cl a (not b)) is FALSE under a := false, b := true"
    );
}

/// SOUNDNESS. A permutation of some OTHER derived clause is not a permutation
/// of this step's premise.
#[test]
fn the_permutation_must_be_of_the_cited_premise() {
    let (terms, a, b, c, _not_b) = alphabet();
    let error = check(
        &terms,
        vec![c, a],
        vec![ProofId(1)],
        vec![Some(vec![a, c]), Some(vec![a, b])],
    )
    .expect_err("the conclusion permutes step 0, but step 1 is cited");
    assert!(matches!(error, ProofCheckError::InvalidBooleanRule { .. }));
    let assignment = [("a", false), ("b", true), ("c", false)];
    assert!(
        eval_clause(&terms, &[a, b], &assignment),
        "the CITED premise (cl a b) is TRUE"
    );
    assert!(
        !eval_clause(&terms, &[c, a], &assignment),
        "the conclusion (cl c a) is FALSE under the same assignment"
    );
}

/// SCOPE, not soundness — recorded as such. Collapsing a repeated literal is
/// entailment-preserving (there is NO falsifying assignment, asserted below),
/// but `reordering` must mean exactly what the pinned external rule means, so
/// the multiset comparison rejects it and `contraction` owns that inference.
#[test]
fn multiplicity_must_match_not_merely_the_literal_set() {
    let (terms, a, b, _c, _not_b) = alphabet();
    let error = check(
        &terms,
        vec![a, b, b],
        vec![ProofId(0)],
        vec![Some(vec![a, a, b])],
    )
    .expect_err("a multiplicity change is out of scope for reordering");
    assert!(matches!(error, ProofCheckError::InvalidBooleanRule { .. }));
    for mask in 0..4u32 {
        let assignment = [("a", mask & 1 != 0), ("b", mask & 2 != 0)];
        assert_eq!(
            eval_clause(&terms, &[a, a, b], &assignment),
            eval_clause(&terms, &[a, b, b], &assignment),
            "the rejection is SCOPE: no assignment separates these two clauses"
        );
    }
}

/// SCOPE. Two premises is not the rule's shape; picking the first would be
/// sound but would let a step cite evidence it does not use.
#[test]
fn more_than_one_premise_is_rejected() {
    let (terms, a, b, c, _not_b) = alphabet();
    let error = check(
        &terms,
        vec![b, a],
        vec![ProofId(0), ProofId(1)],
        vec![Some(vec![a, b]), Some(vec![c])],
    )
    .expect_err("reordering takes exactly one premise");
    assert!(matches!(error, ProofCheckError::InvalidBooleanRule { .. }));
}

/// The step is only checked in STRICT mode, like every other Boolean rule; the
/// non-strict path records the clause without re-deriving it.
#[test]
fn the_non_strict_path_records_the_clause_without_validating() {
    let (terms, a, b, c, _not_b) = alphabet();
    let step = ProofStep::Step {
        rule: AletheRule::Reordering,
        clause: vec![a, c],
        premises: vec![ProofId(0)],
        args: vec![],
    };
    let mut derived = vec![Some(vec![a, b])];
    validate_step(&terms, &mut derived, ProofId(1), &step, false, None)
        .expect("non-strict validation defers");
}

// ------------------------------------------------------------- wire surface

#[test]
fn the_rule_lowers_to_the_pinned_checkable_wire_name() {
    assert_eq!(AletheRule::Reordering.name(), "reordering");
    assert_eq!(AletheRule::Reordering.wire_name(), "reordering");
    assert!(ay_core::is_checkable_alethe_rule("reordering"));
    assert!(ay_core::CHECKABLE_ALETHE_RULES.contains(&"reordering"));
}
