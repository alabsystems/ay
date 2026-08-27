// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The GUARD-MUTATION targets of the ITE-definition leaf lane, and the DIRECT
//! pins for the guards a paired mutation still leaves green.
//!
//! Split out of `ite_definition_leaf_tests.rs` so each file stays inside the
//! repository's 500-line ceiling. The ledger that indexes these tests is in
//! that file's module docs.

use ay_core::{AletheRule, ProofId, ProofStep, Sort, Symbol, TermData};

use super::tests::{fixture, leaf_proof, negative_half, premiseless_unit_trust_leaves, rerun};

// ===== Guard mutation targets =====

#[test]
fn a_proof_carrying_an_anchor_is_left_alone() {
    let mut f = fixture();
    let goal = negative_half(&mut f);
    let mut proof = leaf_proof(&mut f.exec, goal);
    proof.steps.push(ProofStep::Anchor {
        end_step: ProofId(0),
        variables: Vec::new(),
    });
    assert_eq!(rerun(&mut f.exec, &mut proof), 0);
    assert_eq!(premiseless_unit_trust_leaves(&proof), 2);
}

#[test]
fn a_trust_step_with_premises_is_left_alone() {
    let mut f = fixture();
    let goal = negative_half(&mut f);
    let mut proof = leaf_proof(&mut f.exec, goal);
    let ProofStep::Step { premises, .. } = &mut proof.steps[0] else {
        unreachable!()
    };
    *premises = vec![ProofId(1)];
    assert_eq!(rerun(&mut f.exec, &mut proof), 0);
}

#[test]
fn a_trust_step_with_args_is_left_alone() {
    let mut f = fixture();
    let goal = negative_half(&mut f);
    let mut proof = leaf_proof(&mut f.exec, goal);
    let ProofStep::Step { args, .. } = &mut proof.steps[0] else {
        unreachable!()
    };
    *args = vec![goal];
    assert_eq!(rerun(&mut f.exec, &mut proof), 0);
}

#[test]
fn a_guard_clause_over_an_ordinary_variable_is_left_alone() {
    let mut f = fixture();
    let sort = f.exec.ctx.terms.sort(f.ite).clone();
    let ordinary = f.exec.ctx.terms.mk_var("itedef_ordinary", sort);
    let equality = f.exec.ctx.terms.mk_eq(ordinary, f.then_branch);
    let not_condition = f.exec.ctx.terms.mk_not(f.condition);
    let goal = f.exec.ctx.terms.mk_or(vec![not_condition, equality]);
    let mut proof = leaf_proof(&mut f.exec, goal);
    assert_eq!(rerun(&mut f.exec, &mut proof), 0);
    assert_eq!(premiseless_unit_trust_leaves(&proof), 2);
}

#[test]
fn a_definiendum_whose_suffix_is_not_an_ite_is_left_alone() {
    let mut f = fixture();
    // `itedef_c` is a Bool VARIABLE, not an ite; name a definiendum after it.
    let sort = f.exec.ctx.terms.sort(f.ite).clone();
    let forged = f
        .exec
        .ctx
        .terms
        .mk_var(format!("__ay_ite_def_{}", f.condition.0), sort);
    let equality = f.exec.ctx.terms.mk_eq(forged, f.then_branch);
    let not_condition = f.exec.ctx.terms.mk_not(f.condition);
    let goal = f.exec.ctx.terms.mk_or(vec![not_condition, equality]);
    let mut proof = leaf_proof(&mut f.exec, goal);
    assert!(
        !matches!(f.exec.ctx.terms.get(f.condition), TermData::Ite(..)),
        "the suffix must really name a non-ite"
    );
    assert_eq!(rerun(&mut f.exec, &mut proof), 0);
}

#[test]
fn a_forged_spelling_that_denotes_another_variable_is_left_alone() {
    let mut f = fixture();
    // A variable spelled for THIS ite but declared at a DIFFERENT sort: the
    // `mk_var(name, sort)` re-derivation returns the other `TermId`.
    let forged = f
        .exec
        .ctx
        .terms
        .mk_var(format!("__ay_ite_def_{}", f.ite.0), Sort::Real);
    assert_ne!(forged, f.definiendum);
    let value = f.exec.ctx.terms.mk_var("itedef_real", Sort::Real);
    let equality = f.exec.ctx.terms.mk_eq(forged, value);
    let not_condition = f.exec.ctx.terms.mk_not(f.condition);
    let goal = f.exec.ctx.terms.mk_or(vec![not_condition, equality]);
    let mut proof = leaf_proof(&mut f.exec, goal);
    assert_eq!(rerun(&mut f.exec, &mut proof), 0);
}

#[test]
fn a_guard_clause_whose_branch_does_not_match_is_left_alone() {
    let mut f = fixture();
    // Guard-NEGATIVE polarity but the ELSE branch on the right-hand side —
    // `(or (not c) (= d 0))` is FALSE at `c = true, d = 1`.
    let equality = f.exec.ctx.terms.mk_eq(f.definiendum, f.else_branch);
    let not_condition = f.exec.ctx.terms.mk_not(f.condition);
    let goal = f.exec.ctx.terms.mk_or(vec![not_condition, equality]);
    let mut proof = leaf_proof(&mut f.exec, goal);
    assert_eq!(rerun(&mut f.exec, &mut proof), 0);
    assert_eq!(premiseless_unit_trust_leaves(&proof), 2);
}

#[test]
fn a_definiendum_the_problem_constrains_is_never_defined() {
    let mut f = fixture();
    let goal = negative_half(&mut f);
    // The problem now MENTIONS the definiendum, so defining it is an ordinary
    // added constraint rather than a conservative extension.
    let constraint = f.exec.ctx.terms.mk_eq(f.definiendum, f.else_branch);
    f.exec.ctx.assertions.push(constraint);
    let mut proof = leaf_proof(&mut f.exec, goal);
    assert_eq!(rerun(&mut f.exec, &mut proof), 0);
    assert_eq!(premiseless_unit_trust_leaves(&proof), 2);
}

#[test]
fn a_definiendum_an_assume_mentions_is_never_defined() {
    let mut f = fixture();
    let goal = negative_half(&mut f);
    let mut proof = leaf_proof(&mut f.exec, goal);
    let mentioned = f.exec.ctx.terms.mk_eq(f.definiendum, f.else_branch);
    proof.steps.insert(0, ProofStep::Assume(mentioned));
    if let Some(ProofStep::Step { premises, .. }) = proof.steps.last_mut() {
        *premises = vec![ProofId(1), ProofId(2)];
    }
    assert_eq!(rerun(&mut f.exec, &mut proof), 0);
}

// ===== the checker is the authority =====

#[test]
fn the_checker_decides_both_new_leaf_steps() {
    let mut f = fixture();
    let terms = &mut f.exec.ctx.terms;
    let definition = terms.mk_app(Symbol::named("="), [f.definiendum, f.ite], Sort::Bool);
    let projection = terms.mk_app(Symbol::named("="), [f.ite, f.then_branch], Sort::Bool);
    let not_condition = terms.mk_not(f.condition);
    // ACCEPTED, on exactly the triples the lane emits.
    assert!(ay_core::proof_validation::recognize_fresh_def_eq(
        terms,
        &[definition],
        0,
        &[f.definiendum]
    )
    .is_ok());
    assert!(ay_proof::recognize_ite_branch_projection(
        terms,
        &[not_condition, projection]
    ));
    // REFUSED, two-sided: the MIRROR polarity is a different, refutable claim.
    assert!(
        !ay_proof::recognize_ite_branch_projection(terms, &[f.condition, projection]),
        "`(cl c (= (ite c t e) t))` is false at c = false, t != e"
    );
    // REFUSED: a definition whose declared symbol is on neither side.
    assert!(ay_core::proof_validation::recognize_fresh_def_eq(
        terms,
        &[projection],
        0,
        &[f.definiendum]
    )
    .is_err());
}

#[test]
fn gate_two_is_the_checkers_own_registry() {
    let mut f = fixture();
    let goal = negative_half(&mut f);
    let mut proof = leaf_proof(&mut f.exec, goal);
    assert_eq!(rerun(&mut f.exec, &mut proof), 1);
    let scope = f.exec.complete_problem_assertions_for_strict_proof();
    assert!(
        ay_proof::FreshDefRegistry::collect(&proof, &f.exec.ctx.terms, Some(&scope)).is_ok(),
        "the finished proof must satisfy the checker's own whole-proof registry"
    );
    // And the registry REFUSES the same document once the problem constrains
    // the definiendum — the property Gate 2 exists to re-decide.
    let constraint = f.exec.ctx.terms.mk_eq(f.definiendum, f.else_branch);
    assert!(
        ay_proof::FreshDefRegistry::collect(&proof, &f.exec.ctx.terms, Some(&[constraint]))
            .is_err()
    );
}

/// The two leaf steps this lane writes are INTERNALLY checked rules with no
/// external Alethe primitive (`fresh_def_eq`, `ite_branch_projection`); every
/// OTHER rule it emits is externally checkable, and none of them is `trust`.
#[test]
fn every_other_rule_the_lane_emits_is_externally_checkable() {
    let mut f = fixture();
    let goal = negative_half(&mut f);
    let mut proof = leaf_proof(&mut f.exec, goal);
    assert_eq!(rerun(&mut f.exec, &mut proof), 1);
    let mut internal = 0usize;
    for step in &proof.steps {
        let ProofStep::Step { rule, clause, .. } = step else {
            // The `ite_branch_projection` theory lemma.
            internal += 1;
            continue;
        };
        if matches!(rule, AletheRule::Trust) {
            assert_eq!(clause.len(), 1, "only the fixture's closer stays trust");
            continue;
        }
        if matches!(rule, AletheRule::FreshDefEq) {
            internal += 1;
            continue;
        }
        assert!(
            ay_core::is_checkable_alethe_rule(rule.name()),
            "rule {rule:?} is not in CHECKABLE_ALETHE_RULES"
        );
        assert_ne!(ay_core::wire_rule_name(rule.name()), "hole");
    }
    assert_eq!(
        internal, 2,
        "exactly the minted definition and the ite projection"
    );
}

// ===== DIRECT pins for the guards the paired mutations left GREEN =====

/// Guard 8, SINGLE DEFINIENS. A proof that already binds this definiendum to a
/// DIFFERENT definiens must not get a second one: jointly the two would force
/// `then = else`, which is a genuine constraint on the problem's own terms, and
/// `FreshDefRegistry` rejects the document outright.
#[test]
fn a_competing_existing_binding_is_never_overwritten() {
    let mut f = fixture();
    let goal = negative_half(&mut f);
    let mut proof = leaf_proof(&mut f.exec, goal);
    // An existing `fresh_def_eq` binding `d := else` (raw `=`, as the checker
    // reads it), spliced ahead of the leaf.
    let other = f.exec.ctx.terms.mk_app(
        Symbol::named("="),
        [f.definiendum, f.else_branch],
        Sort::Bool,
    );
    proof.steps.insert(
        0,
        ProofStep::Step {
            rule: AletheRule::FreshDefEq,
            clause: vec![other],
            premises: Vec::new(),
            args: vec![f.definiendum],
        },
    );
    if let Some(ProofStep::Step { premises, .. }) = proof.steps.last_mut() {
        *premises = vec![ProofId(1), ProofId(2)];
    }
    // The lane sees the competing binding and declines.
    assert_eq!(rerun(&mut f.exec, &mut proof), 0);
    // And the property is real, not a convention: adding the second definition
    // by hand makes the CHECKER's own registry refuse the whole document.
    let definition =
        f.exec
            .ctx
            .terms
            .mk_app(Symbol::named("="), [f.definiendum, f.ite], Sort::Bool);
    let mut forged = proof.clone();
    forged.steps.insert(
        0,
        ProofStep::Step {
            rule: AletheRule::FreshDefEq,
            clause: vec![definition],
            premises: Vec::new(),
            args: vec![f.definiendum],
        },
    );
    assert!(
        ay_proof::FreshDefRegistry::collect(&forged, &f.exec.ctx.terms, Some(&[])).is_err(),
        "two definientia for one symbol must be refused by the registry"
    );
}

/// Guard 9, INDEPENDENT. A definiens that MENTIONS another definiendum makes
/// the definitions mutually recursive, and the extension is then no longer
/// conservative. The lane declines, and the checker's own registry agrees.
#[test]
fn a_definiens_mentioning_another_definiendum_is_declined() {
    let mut f = fixture();
    // An OUTER ite whose then-branch is the inner definiendum, named for
    // itself, exactly as nested ITE lifting would spell it.
    let outer_ite = f
        .exec
        .ctx
        .terms
        .mk_ite_raw(f.condition, f.definiendum, f.else_branch);
    let sort = f.exec.ctx.terms.sort(outer_ite).clone();
    let outer = f
        .exec
        .ctx
        .terms
        .mk_var(format!("__ay_ite_def_{}", outer_ite.0), sort);
    let equality = f.exec.ctx.terms.mk_eq(outer, f.definiendum);
    let not_condition = f.exec.ctx.terms.mk_not(f.condition);
    let goal = f.exec.ctx.terms.mk_or(vec![not_condition, equality]);
    let mut proof = leaf_proof(&mut f.exec, goal);
    // Bind the INNER definiendum first, so both names are in play.
    let inner_definition =
        f.exec
            .ctx
            .terms
            .mk_app(Symbol::named("="), [f.definiendum, f.ite], Sort::Bool);
    proof.steps.insert(
        0,
        ProofStep::Step {
            rule: AletheRule::FreshDefEq,
            clause: vec![inner_definition],
            premises: Vec::new(),
            args: vec![f.definiendum],
        },
    );
    if let Some(ProofStep::Step { premises, .. }) = proof.steps.last_mut() {
        *premises = vec![ProofId(1), ProofId(2)];
    }
    assert_eq!(
        rerun(&mut f.exec, &mut proof),
        0,
        "the outer definiens mentions the inner definiendum"
    );
    // Two-sided: the same document with BOTH definitions is refused by the
    // checker's own registry, so the decline is about INDEPENDENT and not
    // about the fragment's shape.
    let outer_definition =
        f.exec
            .ctx
            .terms
            .mk_app(Symbol::named("="), [outer, outer_ite], Sort::Bool);
    let mut forged = proof.clone();
    forged.steps.insert(
        0,
        ProofStep::Step {
            rule: AletheRule::FreshDefEq,
            clause: vec![outer_definition],
            premises: Vec::new(),
            args: vec![outer],
        },
    );
    assert!(
        ay_proof::FreshDefRegistry::collect(&forged, &f.exec.ctx.terms, Some(&[])).is_err(),
        "a definiens mentioning another definiendum must be refused"
    );
}
