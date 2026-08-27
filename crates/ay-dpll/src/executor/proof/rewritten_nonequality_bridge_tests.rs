// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Coverage for the NON-EQUALITY rewritten-assertion bridge LANE.
//!
//! `ay-proof`'s `definition_bridge_tests` / `definition_bridge_negative_tests`
//! own the PLANNER's bar and this lane does not change the planner, the
//! checker, or any validator: it calls `plan_definitional_bridge` on the
//! EQUALITY BETWEEN an authored assertion and the leaf, and closes the gap
//! with one `equiv_pos1`/`equiv_pos2` tautology that `ay-proof` already
//! validates. This file owns the LANE — which leaves it takes, which it
//! refuses, and what the spliced proof looks like.
//!
//! **Every fixture is a COMPLETE REFUTATION.** A hand-built leaf is closed
//! over the negation of its own clause, so a guard mutation cannot come back
//! green on a fragment that was never replayed; the end-to-end fixtures are
//! real solves of complete problems in the census regime.
//!
//! # GUARD MUTATION LEDGER
//!
//! Each guard was deleted or weakened, the whole file re-run, the named test
//! observed FAILING, and the guard restored. Honest negatives are recorded
//! rather than hidden.
//!
//! | # | guard | result |
//! |---|---|---|
//! | 1 | no `Anchor` steps | **FAILS** `a_proof_carrying_an_anchor_is_left_alone` |
//! | 2 | `premises.is_empty()` | **FAILS** `a_trust_step_with_premises_is_left_alone` |
//! | 3 | `args.is_empty()` | **FAILS** `a_trust_step_with_args_is_left_alone` |
//! | 4 | the goal is NOT a binary `=` | **FAILS** `an_equality_goal_is_left_to_the_sibling_lane` |
//! | 5 | the root is in the HANDED scope | **FAILS** `an_assertion_outside_the_handed_scope_is_never_assumed` |
//! | 6 | the root is in the STRICT scope (the other half of the intersection) | STILL PASSED — honest negative: on every fixture a REAL SOLVE produces, the handed scope and the strict scope coincide, so the intersection is not separately observable here. The property is pinned DIRECTLY by `the_lane_assumes_only_authored_roots`, which asserts every `Assume` the lane writes is a member of `complete_problem_assertions_for_strict_proof` |
//! | 7 | Guard 7, choosing the `equiv_pos` rule by strict check (mutated to a fixed `equiv_pos1`) | STILL PASSED — honest negative: `commit_bridge_fragments`' whole-proof backstop reverts a fragment carrying the wrong rule, so the mutation costs DERIVATIONS, never soundness. Pinned DIRECTLY and TWO-SIDED by `the_lane_picks_the_equiv_rule_the_checker_accepts_and_refuses_the_other` |
//! | 8 | Guard 8, `(= A G)` is a binary `=` application | STILL PASSED — `plan_definitional_bridge` decodes its own goal and declines a non-application, so the two are a pair. Kept as the fast, explicit statement of the property, which `a_constant_goal_is_declined` pins directly |
//! | 9 | Guard 4, the fragment ends on the leaf's clause | STILL PASSED — unfalsifiable by construction: the last step is built with that clause. Pinned directly by `the_replaced_leaf_keeps_its_clause_byte_for_byte` |
//! | 10 | the sort test (`sort(root) == sort(atom)`) | STILL PASSED — every authored assertion and every clause literal is `Bool`, so the comparison is constant on this population. Kept as defence in depth |

use ay_core::{AletheRule, ArraySort, ProofId, ProofStep, Sort, Symbol, TermData, TermId};
use ay_frontend::parse;

use crate::Executor;

/// `three_store_chain.smt2`, verbatim. `VariableSubstitution` folds the chain
/// `d = c = b = (store a i v)`, and the assertion the file actually states as a
/// NEGATION — `(not (= (select d i) v))` — is asserted in its rewritten form
/// `(not (= v (select c i)))`, which is not an authored assertion. Measured on
/// the corpus as one step of this lane's class.
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

/// A solve in the CENSUS REGIME: `set_retain_parsed_assertions(false)`, exactly
/// what the CLI does for `--no-proof`, `--z3-mode` and competition mode.
pub(super) fn solve(text: &str) -> Executor {
    let commands = parse(text).expect("parse");
    let mut exec = Executor::new();
    exec.set_retain_parsed_assertions(false);
    assert_eq!(exec.execute_all(&commands).expect("exec"), vec!["unsat"]);
    exec
}

/// Every premiseless, argument-free `trust` step with a unit clause — of ANY
/// shape, so a test cannot pass by moving a leaf between the two lanes.
fn premiseless_unit_trust_leaves(proof: &ay_core::Proof) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    args,
                } if premises.is_empty() && args.is_empty() && clause.len() == 1
            )
        })
        .count()
}

/// The lane's own entry point, run against the executor's strict scope.
pub(super) fn rerun(exec: &mut Executor, proof: &mut ay_core::Proof) -> usize {
    let scope = exec.complete_problem_assertions_for_strict_proof();
    exec.derive_rewritten_nonequality_assertions(proof, &scope)
}

/// A COMPLETE REFUTATION carrying one premiseless `trust` leaf: the leaf, an
/// `assume` of its negation, and the resolution that closes them.
pub(super) fn leaf_proof(
    exec: &mut Executor,
    atom: TermId,
    premises: Vec<ProofId>,
    args: Vec<TermId>,
) -> ay_core::Proof {
    let negated = exec.ctx.terms.mk_not(atom);
    let mut proof = ay_core::Proof::new();
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![atom],
        premises,
        args,
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

/// The store-chain problem's own symbols, rebuilt from the executor's interned
/// terms.
pub(super) struct ChainTerms {
    pub(super) c: TermId,
    pub(super) d: TermId,
    pub(super) i: TermId,
    pub(super) v: TermId,
}

pub(super) fn chain_terms(exec: &mut Executor) -> ChainTerms {
    let index = Sort::Uninterpreted("Index".to_string());
    let element = Sort::Uninterpreted("Element".to_string());
    let array = Sort::Array(Box::new(ArraySort::new(index.clone(), element.clone())));
    let terms = &mut exec.ctx.terms;
    ChainTerms {
        c: terms.mk_var("c", array.clone()),
        d: terms.mk_var("d", array),
        i: terms.mk_var("i", index),
        v: terms.mk_var("v", element),
    }
}

/// `(not (= v (select c i)))` — the REWRITTEN negated assertion the solve
/// demotes, and this lane's end-to-end target.
pub(super) fn rewritten_negation(exec: &mut Executor) -> TermId {
    let ChainTerms { c, i, v, .. } = chain_terms(exec);
    let element = Sort::Uninterpreted("Element".to_string());
    let terms = &mut exec.ctx.terms;
    let read = terms.mk_app(Symbol::named("select"), vec![c, i], element);
    let equality = terms.mk_eq(v, read);
    terms.mk_not(equality)
}

/// A comparable rendering of a proof's steps. `ProofStep` has no `PartialEq`.
pub(super) fn shape(proof: &ay_core::Proof) -> String {
    format!("{:?}", proof.steps)
}

// ===== the lane, end to end on a REAL SOLVE =====

#[test]
fn the_rewritten_negated_assertion_is_derived_by_the_solve_itself() {
    let exec = solve(STORE_CHAIN);
    let proof = exec.last_proof.clone().expect("a finished proof");
    assert_eq!(
        premiseless_unit_trust_leaves(&proof),
        0,
        "the rewritten negated assertion must not survive as a trust leaf"
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::EquivPos1 | AletheRule::EquivPos2,
                ..
            }
        )),
        "the propositional step this lane contributes must be present"
    );
    exec.check_proof_strict_with_datatypes(&proof)
        .expect("the finished proof must certify under the UNTOUCHED strict checker");
}

#[test]
fn every_rule_the_lane_emits_is_externally_checkable() {
    let exec = solve(STORE_CHAIN);
    let proof = exec.last_proof.clone().expect("a finished proof");
    for step in &proof.steps {
        let ProofStep::Step { rule, .. } = step else {
            continue;
        };
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

/// The WIRE, pinned as exact text.
#[test]
fn the_fragment_prints_equiv_pos_on_the_wire() {
    let exec = solve(STORE_CHAIN);
    let proof = exec.last_proof.clone().expect("a finished proof");
    let document =
        ay_proof::try_export_alethe(&proof, &exec.ctx.terms).expect("the proof must render");
    assert!(
        document.contains(":rule equiv_pos1") || document.contains(":rule equiv_pos2"),
        "the lane's propositional step must print under its own name:\n{document}"
    );
    assert!(
        !document.contains(":rule trust"),
        "no trust step may survive:\n{document}"
    );
    assert!(
        !document.contains(":rule hole"),
        "the lane must not trade a trust step for a hole:\n{document}"
    );
    assert!(
        document.contains(":rule eq_congruent") || document.contains(":rule eq_transitive"),
        "the congruence half must print too:\n{document}"
    );
}

// ===== hand-built leaves: the guards =====

#[test]
fn a_hand_built_negated_leaf_is_derived_and_the_rebuilt_proof_replays() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_negation(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    // The fixture must start REJECTED and must carry the leaf this lane
    // claims, or it proves nothing.
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
    assert_eq!(premiseless_unit_trust_leaves(&proof), 1);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    assert_eq!(premiseless_unit_trust_leaves(&proof), 0);
    // The fixture's own `assume (not atom)` is not an authored assertion, so
    // the closed refutation cannot certify outright; what MUST hold is that
    // every step of the derivation replays and the only unauthorised leaf is
    // the one the fixture introduced on purpose.
    match exec.check_proof_strict_with_datatypes(&proof) {
        Ok(_) => {}
        Err(ay_proof::ProofCheckError::UnauthorizedAssumption { .. }) => {}
        Err(other) => panic!("the rebuilt proof must replay, got {other:?}"),
    }
}

#[test]
fn the_replaced_leaf_keeps_its_clause_byte_for_byte() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_negation(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
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
fn the_lane_assumes_only_authored_roots() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_negation(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    let negated = exec.ctx.terms.mk_not(atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let scope: Vec<TermId> = exec.complete_problem_assertions_for_strict_proof();
    for step in &proof.steps {
        let ProofStep::Assume(term) = step else {
            continue;
        };
        if *term == negated {
            continue; // the fixture's own closing assumption
        }
        assert!(
            scope.contains(term),
            "the lane assumed a term outside the strict scope: {term:?}"
        );
    }
}

#[test]
fn a_proof_carrying_an_anchor_is_left_alone() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_negation(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    proof.steps.push(ProofStep::Anchor {
        end_step: ProofId(0),
        variables: Vec::new(),
    });
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before, "an anchored proof must be untouched");
}

#[test]
fn a_trust_step_with_premises_is_left_alone() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_negation(&mut exec);
    // A `trust` step WITH premises is a FAILED DERIVATION, not a leaf:
    // relabelling it would drop the premises its consumer references. The
    // fixture is a complete refutation whose only `trust` step has one.
    let negated = exec.ctx.terms.mk_not(atom);
    let mut proof = ay_core::Proof::new();
    proof.steps.push(ProofStep::Assume(negated));
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![atom],
        premises: vec![ProofId(0)],
        args: Vec::new(),
    });
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![ProofId(1), ProofId(0)],
        args: Vec::new(),
    });
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(
        shape(&proof),
        before,
        "a premise-bearing trust step must be untouched"
    );
}

#[test]
fn a_trust_step_with_args_is_left_alone() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_negation(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), vec![atom]);
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(
        shape(&proof),
        before,
        "an argument-bearing trust step must be untouched"
    );
}

#[test]
fn an_equality_goal_is_left_to_the_sibling_lane() {
    let mut exec = solve(STORE_CHAIN);
    let ChainTerms { c, d, .. } = chain_terms(&mut exec);
    // `(= d c)` IS an authored assertion, so nothing about it is underivable;
    // what this pins is that a binary `=` goal never enters THIS lane.
    let atom = exec.ctx.terms.mk_eq(d, c);
    assert!(matches!(
        exec.ctx.terms.get(atom),
        TermData::App(Symbol::Named(name), operands) if name == "=" && operands.len() == 2
    ));
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

#[test]
fn an_assertion_outside_the_handed_scope_is_never_assumed() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_negation(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    // The lane is handed a scope that does NOT contain the root it would need.
    // The root is `(not (= (select d i) v))`; hand it every OTHER assertion.
    let ChainTerms { d, i, v, .. } = chain_terms(&mut exec);
    let element = Sort::Uninterpreted("Element".to_string());
    let read = exec
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![d, i], element);
    let equality = exec.ctx.terms.mk_eq(read, v);
    let root = exec.ctx.terms.mk_not(equality);
    let scope: Vec<TermId> = exec
        .complete_problem_assertions_for_strict_proof()
        .into_iter()
        .filter(|term| *term != root)
        .collect();
    assert!(
        !scope.contains(&root),
        "the fixture must actually remove the root"
    );
    let before = shape(&proof);
    let derived = exec.derive_rewritten_nonequality_assertions(&mut proof, &scope);
    assert_eq!(
        derived, 0,
        "the root is out of scope, so nothing may be assumed"
    );
    assert_eq!(shape(&proof), before);
    // TWO-SIDED: with the root back in scope the SAME leaf is derived, so the
    // refusal is about MEMBERSHIP and not about the proof's shape.
    assert_eq!(rerun(&mut exec, &mut proof), 1);
}
