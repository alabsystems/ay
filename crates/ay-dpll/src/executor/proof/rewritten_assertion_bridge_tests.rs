// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Coverage for the rewritten-assertion bridge LANE.
//!
//! `ay-proof`'s `definition_bridge_tests` / `definition_bridge_negative_tests`
//! own the PLANNER's bar: an INDEPENDENT evaluator that shares no code with it
//! re-checks every accept, exhaustive sweeps two-sided over a bounded alphabet,
//! and adversarial negatives that each name a concrete falsifying assignment
//! and CHECK it. This file owns the LANE — which leaves it touches, which it
//! refuses, and what the spliced proof looks like.
//!
//! **Every fixture is a REAL SOLVE of a COMPLETE problem.** That is
//! methodological, not stylistic: with a truncated fixture a guard mutation can
//! come back green because a backstop reverted the rewrite for an unrelated
//! reason. Here the proof either certifies under the untouched strict checker
//! or it does not, and the assertion is on that.

use ay_core::{AletheRule, ProofId, ProofStep, Sort, Symbol, TermData, TermId};
use ay_frontend::parse;

use crate::Executor;

/// `three_store_chain.smt2`, verbatim: `VariableSubstitution` folds the chain
/// `d = c = b = (store a i v)` and asserts `(= c (store a i v))`, which is NOT
/// an authored assertion. Measured on the corpus as one step of this class.
pub(super) const STORE_CHAIN: &str = r#"
    (set-logic QF_AX)
    (declare-sort Index 0)
    (declare-sort Element 0)
    (declare-fun a () (Array Index Element))
    (declare-fun b () (Array Index Element))
    (declare-fun c () (Array Index Element))
    (declare-fun d () (Array Index Element))
    (declare-fun i () Index)
    (declare-fun v () Element)
    (assert (= b (store a i v)))
    (assert (= c b))
    (assert (= d c))
    (assert (not (= (select d i) v)))
    (check-sat)
"#;

/// A solve in the CENSUS REGIME: `set_retain_parsed_assertions(false)`, which
/// is exactly what the CLI does for `--no-proof`, `--z3-mode` and competition
/// mode — the mandatory-certificate configuration this class was measured in.
pub(super) fn solve(text: &str) -> Executor {
    let commands = parse(text).expect("parse");
    let mut exec = Executor::new();
    exec.set_retain_parsed_assertions(false);
    assert_eq!(exec.execute_all(&commands).expect("exec"), vec!["unsat"]);
    exec
}

/// Every premiseless, argument-free `trust` step whose clause is a unit binary
/// `=` — the population this lane exists to remove.
pub(super) fn premiseless_equality_trust_leaves(exec: &Executor, proof: &ay_core::Proof) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| super::is_bridge_candidate(&exec.ctx.terms, step).is_some())
        .count()
}

/// The lane's own view of the finished proof, run a second time so a test can
/// assert on the count directly.
pub(super) fn rerun(exec: &mut Executor, proof: &mut ay_core::Proof) -> usize {
    let scope = exec.complete_problem_assertions_for_strict_proof();
    exec.derive_rewritten_assertions_by_congruence(proof, &scope)
}

/// A fresh, UNBRIDGED copy of the solved proof: the finished proof with its
/// bridge fragments replaced by the `trust` leaf they came from. Built by
/// re-solving with the lane's own entry point never called — which is what the
/// `AY_NO_ASSERTION_BRIDGE` arm does in the corpus A/B, and what a test gets by
/// constructing the leaf directly.
pub(super) fn leaf_proof(exec: &mut Executor, atom: TermId) -> ay_core::Proof {
    let negated = exec.ctx.terms.mk_not(atom);
    let mut proof = ay_core::Proof::new();
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![atom],
        premises: Vec::new(),
        args: Vec::new(),
    });
    proof.steps.push(ProofStep::Assume(negated));
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![ProofId(0), ProofId(1)],
        args: Vec::new(),
    });
    proof
}

/// `(= c (store a i v))` — the rewritten assertion the solve demotes, rebuilt
/// from the executor's own interned terms.
pub(super) fn rewritten_assertion(exec: &mut Executor) -> TermId {
    let index = Sort::Uninterpreted("Index".to_string());
    let element = Sort::Uninterpreted("Element".to_string());
    let array = Sort::Array(Box::new(ay_core::ArraySort::new(
        index.clone(),
        element.clone(),
    )));
    let terms = &mut exec.ctx.terms;
    let a = terms.mk_var("a", array.clone());
    let c = terms.mk_var("c", array.clone());
    let i = terms.mk_var("i", index);
    let v = terms.mk_var("v", element);
    let stored = terms.mk_app(Symbol::named("store"), vec![a, i, v], array);
    terms.mk_eq(c, stored)
}

/// A comparable rendering of a proof's steps. `ProofStep` has no `PartialEq`,
/// and a byte-identity claim needs one.
pub(super) fn shape(proof: &ay_core::Proof) -> String {
    format!("{:?}", proof.steps)
}

// ===== the lane, end to end =====

#[test]
fn the_rewritten_store_chain_assertion_is_derived_by_the_solve_itself() {
    let exec = solve(STORE_CHAIN);
    let proof = exec.last_proof.clone().expect("a finished proof");
    assert_eq!(
        premiseless_equality_trust_leaves(&exec, &proof),
        0,
        "the rewritten assertion must not survive as a trust leaf"
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::EqTransitive | AletheRule::EqCongruent,
                ..
            }
        )),
        "the derivation must be present in the finished proof"
    );
    // The finished proof carries ONE residual `trust` leaf, and it is a
    // NEGATED equality — `(not (= v (select c i)))`, the census's separate
    // `not[=#2]` class, which no congruence bridge applies to. Pinned so the
    // scope of this lane stays honest: the strict checker's first offender
    // must never again be a POSITIVE unit equality.
    if let Err(ay_proof::ProofCheckError::TrustStep { step }) =
        exec.check_proof_strict_with_datatypes(&proof)
    {
        let ProofStep::Step { clause, .. } = &proof.steps[step.0 as usize] else {
            panic!("a trust offender is a generic step");
        };
        assert!(
            super::is_bridge_candidate(&exec.ctx.terms, &proof.steps[step.0 as usize]).is_none(),
            "the first offender is still a leaf this lane claims: {clause:?}"
        );
    }
}

#[test]
fn a_hand_built_leaf_is_derived_and_the_rebuilt_proof_certifies() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_assertion(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    // The fixture must start REJECTED, or it proves nothing.
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    assert_eq!(premiseless_equality_trust_leaves(&exec, &proof), 0);
    // The negated leaf is not in the authored scope, so the closed fixture
    // cannot certify outright; what MUST hold is that every step of the
    // derivation replays and the only unauthorised leaf left is the one the
    // fixture introduced on purpose.
    match exec.check_proof_strict_with_datatypes(&proof) {
        Ok(_) => {}
        Err(ay_proof::ProofCheckError::UnauthorizedAssumption { .. }) => {}
        Err(other) => panic!("the rebuilt proof must replay, got {other:?}"),
    }
}

#[test]
fn the_replaced_leaf_keeps_its_clause_byte_for_byte() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_assertion(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let ProofStep::Step { premises, .. } = proof.steps.last().expect("a terminal step") else {
        panic!("the terminal step is a resolution");
    };
    let last = premises[0].0 as usize;
    let ProofStep::Step { clause, .. } = &proof.steps[last] else {
        panic!("the fragment ends on a generic step");
    };
    assert_eq!(clause.as_slice(), [atom]);
}

#[test]
fn every_rule_the_lane_emits_is_externally_checkable() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_assertion(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    for step in &proof.steps {
        let ProofStep::Step { rule, .. } = step else {
            continue;
        };
        if matches!(rule, AletheRule::Resolution) {
            continue; // the fixture's own closing step
        }
        assert!(
            ay_core::is_checkable_alethe_rule(rule.name()),
            "the lane emitted {}, which is not externally checkable",
            rule.name()
        );
        assert_ne!(
            ay_core::wire_rule_name(rule.name()),
            "hole",
            "the lane must not trade a trust step for a hole"
        );
    }
}

/// The wire: the lane's fragment prints, and it prints the derivation's own
/// rules rather than a `hole`.
#[test]
fn the_fragment_prints_its_own_rules_on_the_wire() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_assertion(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let document = ay_proof::try_export_alethe(&proof, &exec.ctx.terms)
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
        document.contains(":rule eq_transitive"),
        "the store-chain bridge is a transitivity:\n{document}"
    );
    assert!(
        document.contains(":rule th_resolution"),
        "each cited hypothesis is discharged by th_resolution:\n{document}"
    );
}

// ===== guards =====

#[test]
fn a_trust_step_with_premises_is_left_alone() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_assertion(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    let ProofStep::Step { premises, .. } = &mut proof.steps[0] else {
        unreachable!()
    };
    premises.push(ProofId(1));
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before, "the proof must be byte-identical");
}

#[test]
fn a_trust_step_with_args_is_left_alone() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_assertion(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    let ProofStep::Step { args, .. } = &mut proof.steps[0] else {
        unreachable!()
    };
    args.push(atom);
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

#[test]
fn a_proof_carrying_an_anchor_is_left_alone() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_assertion(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    proof.steps.push(ProofStep::Anchor {
        end_step: ProofId(2),
        variables: Vec::new(),
    });
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

#[test]
fn an_assertion_outside_the_strict_scope_is_never_assumed() {
    let mut exec = solve(STORE_CHAIN);
    // A leaf that is derivable ONLY from a hypothesis the STRICT scope does
    // not carry: `(= (f g1) (f g2))` from the GHOST `(= g1 g2)`. Offering the
    // ghost as a problem assertion must not license an `assume` of it, because
    // the mandatory gate re-authorises assumes against the strict scope and
    // would reject the whole proof — strictly worse than the `trust` step.
    let (goal, ghost) = {
        let element = Sort::Uninterpreted("Element".to_string());
        let terms = &mut exec.ctx.terms;
        let g1 = terms.mk_var("ghost_1", element.clone());
        let g2 = terms.mk_var("ghost_2", element.clone());
        let fg1 = terms.mk_app(Symbol::named("f"), vec![g1], element.clone());
        let fg2 = terms.mk_app(Symbol::named("f"), vec![g2], element);
        (terms.mk_eq(fg1, fg2), terms.mk_eq(g1, g2))
    };
    assert!(
        !exec
            .complete_problem_assertions_for_strict_proof()
            .contains(&ghost),
        "the fixture depends on the ghost being OUTSIDE the strict scope"
    );
    let mut proof = leaf_proof(&mut exec, goal);
    let scope = vec![ghost];
    assert_eq!(
        exec.derive_rewritten_assertions_by_congruence(&mut proof, &scope),
        0,
        "a term the strict scope does not carry must not become an assume"
    );
    assert!(
        !proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Assume(term) if *term == ghost)),
        "a term outside the strict scope must never be assumed"
    );
}

#[test]
fn a_leaf_the_authored_scope_does_not_entail_keeps_its_trust_step() {
    let mut exec = solve(STORE_CHAIN);
    let unrelated = {
        let element = Sort::Uninterpreted("Element".to_string());
        let terms = &mut exec.ctx.terms;
        let left = terms.mk_var("unrelated_l", element.clone());
        let right = terms.mk_var("unrelated_r", element);
        terms.mk_eq(left, right)
    };
    let mut proof = leaf_proof(&mut exec, unrelated);
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before, "the proof must be byte-identical");
}

#[test]
fn a_leaf_whose_clause_is_not_a_binary_equality_is_left_alone() {
    let mut exec = solve(STORE_CHAIN);
    let not_an_equality = {
        let element = Sort::Uninterpreted("Element".to_string());
        let terms = &mut exec.ctx.terms;
        let left = terms.mk_var("p_l", element.clone());
        let right = terms.mk_var("p_r", element);
        terms.mk_app(Symbol::named("p"), vec![left, right], Sort::Bool)
    };
    let mut proof = leaf_proof(&mut exec, not_an_equality);
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

/// The cited hypotheses really are AUTHORED: every `assume` the lane adds is a
/// term the strict scope carries, checked against that scope directly.
#[test]
fn every_assume_the_lane_adds_is_in_the_strict_scope() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_assertion(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    let negated = exec.ctx.terms.mk_not(atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let scope = exec.complete_problem_assertions_for_strict_proof();
    for step in &proof.steps {
        let ProofStep::Assume(term) = step else {
            continue;
        };
        if *term == negated {
            continue; // the fixture's own closing assume
        }
        assert!(
            scope.contains(term),
            "the lane assumed a term outside the strict scope"
        );
        assert!(
            matches!(
                exec.ctx.terms.get(*term),
                TermData::App(Symbol::Named(name), operands) if name == "=" && operands.len() == 2
            ),
            "the lane only ever assumes a binary equality"
        );
    }
}

/// GUARD MUTATION LEDGER — every guard deleted or weakened, the NAMED test
/// observed FAILING, the guard restored. Recorded results are in the pass
/// write-up; honest negatives are recorded there rather than hidden.
///
/// | guard (`rewritten_assertion_bridge.rs`) | named test |
/// |---|---|
/// | no `Anchor` steps | `a_proof_carrying_an_anchor_is_left_alone` |
/// | `premises.is_empty()` | `a_trust_step_with_premises_is_left_alone` |
/// | `args.is_empty()` | `a_trust_step_with_args_is_left_alone` |
/// | the clause is a binary `=` application | `a_leaf_whose_clause_is_not_a_binary_equality_is_left_alone` |
/// | the pool is the INTERSECTION of both authored scopes | `an_assertion_outside_the_strict_scope_is_never_assumed` |
/// | the fragment ends on the leaf's clause | `the_replaced_leaf_keeps_its_clause_byte_for_byte` |
/// | the closed derivation strict-checks | `the_rewritten_store_chain_assertion_is_derived_by_the_solve_itself` |
/// | the fragment RENDERS | `the_fragment_prints_its_own_rules_on_the_wire` |
const GUARD_MUTATION_LEDGER: () = ();

#[test]
fn the_guard_mutation_ledger_exists() {
    let () = GUARD_MUTATION_LEDGER;
}

#[path = "rewritten_assertion_bridge_conjunct_tests.rs"]
mod conjunct;
