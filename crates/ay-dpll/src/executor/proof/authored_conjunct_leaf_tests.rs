// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Coverage for the AUTHORED-CONJUNCT leaf lane.
//!
//! The lane changes no validator, no checker and no planner: it emits
//! `and_pos` and `th_resolution`, both of which `ay-proof` already validates
//! strictly, from an `assume` of an authored root. This file owns the LANE —
//! which leaves it takes, which it refuses, and what the spliced proof looks
//! like. `authored_conjunct_leaf_negative_tests.rs` owns the adversarial
//! negatives, the exhaustive sweep and the independent evaluator.
//!
//! **Every fixture is a COMPLETE REFUTATION.** A hand-built leaf is closed
//! over the negation of its own clause AND the fixture asserts it starts
//! REJECTED and that the leaf this lane claims is actually present, so a guard
//! mutation cannot come back green on a fragment that was never replayed. The
//! end-to-end fixtures are REAL SOLVES of complete problems in the census
//! regime.
//!
//! # GUARD MUTATION LEDGER
//!
//! Each guard was deleted or weakened, the whole `ay-dpll` `--lib` suite
//! re-run UNFILTERED, the named test observed FAILING, and the guard restored.
//! Honest negatives are recorded rather than hidden.
//!
//! | # | guard | mutation | result |
//! |---|---|---|---|
//! | 1 | no `Anchor` steps | delete the early return | **FAILS** `a_proof_carrying_an_anchor_is_left_alone` |
//! | 2 | `premises.is_empty()` | drop it from `is_conjunct_candidate` | **FAILS** `a_trust_step_with_premises_is_left_alone` |
//! | 3 | `args.is_empty()` | drop it from `is_conjunct_candidate` | **FAILS** `a_trust_step_with_args_is_left_alone` |
//! | 4 | `clause.len() == 1` | accept any non-empty clause | STILL PASSED — HONEST NEGATIVE. `commit_bridge_fragments`' whole-proof `check_proof` backstop reverts the splice, because a fragment ending on `(cl A)` cannot support a consumer that resolves the ORIGINAL `(cl A B)` on both literals. The mutation costs nothing observable, so it can only cost derivations, never soundness. Pinned directly by `a_multi_literal_trust_step_is_left_alone`, which asserts the proof is byte-identical |
//! | 5 | Guard 3, the root is in the STRICT scope | drop the `strict_scope` test | **FAILS** `an_assertion_outside_the_strict_scope_is_never_assumed` |
//! | 6 | Guard 3, the root is in the HANDED scope | walk the strict scope instead of `problem_assertions` | **FAILS** `an_assertion_outside_the_handed_scope_is_never_assumed` (and `..._strict_scope_...`) |
//! | 7 | Guard 3, `descents.is_empty()` | record the root as its own conjunct | STILL PASSED — HONEST NEGATIVE, and unfalsifiable at this site: `push_hypothesis_leaf`'s own postcondition requires its LAST step to be a `Step` whose clause is the hypothesis, and with no descents the last step is the `Assume`, so the emitter returns `None`. Kept as the explicit statement of the property, pinned directly by `the_root_itself_is_never_taken_as_its_own_conjunct` |
//! | 8 | the `and_pos` POSITION | emit `AndPos(0)` for every descent | **FAILS** 7 tests, including `a_conjunct_at_a_later_position_is_derived` and `the_lane_never_emits_an_and_pos_whose_position_the_checker_refuses` — the checker's own `validate_and_pos` refuses the wrong index, so Guard 6 declines the fragment |
//! | 9 | Guard 6, the closed strict check | delete it | STILL PASSED — HONEST NEGATIVE: `commit_bridge_fragments`' whole-proof backstop reverts anything the checker refuses, so the mutation costs DERIVATIONS, never soundness. Pinned DIRECTLY by `the_closed_fragment_is_replayed_by_the_untouched_strict_checker` and by the sweep, which strict-checks EVERY accept |
//! | 10 | Guard 4, the fragment ends on the leaf's clause | delete both checks | STILL PASSED — unfalsifiable by construction: the emitter's last step is built with that clause and it returns `None` otherwise. Pinned directly by `the_replaced_leaf_keeps_its_clause_byte_for_byte` |
//! | 11 | `MAX_CONJUNCT_DEPTH` | set to 0 | **FAILS** 14 tests |
//!
//! **8 of 11 RED, 3 honest negatives**, each with its mechanism named above.

use ay_core::{AletheRule, ProofId, ProofStep, Sort, TermId};
use ay_frontend::parse;

use crate::Executor;

/// `QF_AX/storecomm_t1_np_sf_ai_00003.smt2`, verbatim. The parser expands
/// `(assert (distinct i0 i1 i2))` into ONE authored
/// `(and (not (= i0 i1)) (not (= i0 i2)) (not (= i1 i2)))` and the solver
/// asserts the pairwise disequalities individually; `(not (= i0 i1))` is not
/// itself an authored assertion, so it demotes to a premiseless `trust` step.
/// Measured on the corpus as one step of this lane's class.
pub(super) const DISTINCT_STORECOMM: &str = r#"
    (set-logic QF_AX)
    (set-info :status unsat)
    (declare-sort Index 0)
    (declare-sort Elem 0)
    (declare-fun a0 () (Array Index Elem))
    (declare-fun i0 () Index)
    (declare-fun i1 () Index)
    (declare-fun i2 () Index)
    (declare-fun e0 () Elem)
    (declare-fun e1 () Elem)
    (declare-fun e2 () Elem)
    (assert (distinct i0 i1 i2))
    (define-fun fwd () (Array Index Elem) (store (store (store a0 i0 e0) i1 e1) i2 e2))
    (define-fun rev () (Array Index Elem) (store (store (store a0 i2 e2) i1 e1) i0 e0))
    (assert (not (= (select fwd i0) (select rev i0))))
    (check-sat)
"#;

/// A purely propositional problem whose authored root is a NESTED `and`, so
/// the descent is two levels deep.
pub(super) const NESTED: &str = r#"
    (set-logic QF_UF)
    (declare-fun p () Bool)
    (declare-fun q () Bool)
    (declare-fun r () Bool)
    (assert (and p (and q r)))
    (assert (not r))
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
/// shape, so a test cannot pass by moving a leaf between lanes.
pub(super) fn premiseless_unit_trust_leaves(proof: &ay_core::Proof) -> usize {
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
    exec.derive_authored_conjunct_leaves(proof, &scope)
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

/// A comparable rendering of a proof's steps. `ProofStep` has no `PartialEq`.
pub(super) fn shape(proof: &ay_core::Proof) -> String {
    format!("{:?}", proof.steps)
}

/// `(not (= i0 i1))` — the first `distinct` conjunct the solve demotes.
pub(super) fn first_disequality(exec: &mut Executor) -> TermId {
    let index = Sort::Uninterpreted("Index".to_string());
    let i0 = exec.ctx.terms.mk_var("i0", index.clone());
    let i1 = exec.ctx.terms.mk_var("i1", index);
    let equality = exec.ctx.terms.mk_eq(i0, i1);
    exec.ctx.terms.mk_not(equality)
}

/// `(not (= i1 i2))` — the LAST conjunct of the same authored root, so its
/// descent carries a non-zero `and_pos` position.
pub(super) fn last_disequality(exec: &mut Executor) -> TermId {
    let index = Sort::Uninterpreted("Index".to_string());
    let i1 = exec.ctx.terms.mk_var("i1", index.clone());
    let i2 = exec.ctx.terms.mk_var("i2", index);
    let equality = exec.ctx.terms.mk_eq(i1, i2);
    exec.ctx.terms.mk_not(equality)
}

// ===== the lane, end to end on a REAL SOLVE =====

#[test]
fn the_distinct_expansion_conjunct_is_derived_by_the_solve_itself() {
    let exec = solve(DISTINCT_STORECOMM);
    let proof = exec.last_proof.clone().expect("a finished proof");
    assert_eq!(
        premiseless_unit_trust_leaves(&proof),
        0,
        "the `distinct` conjunct must not survive as a trust leaf"
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::AndPos(_),
                ..
            }
        )),
        "the `and_pos` descent this lane contributes must be present"
    );
    // The whole proof still carries a `Generic` theory lemma this lane knows
    // nothing about, so it cannot certify outright — what MUST hold is that
    // the first offender is no longer a trust step.
    match exec.check_proof_strict_with_datatypes(&proof) {
        Ok(_) => {}
        Err(ay_proof::ProofCheckError::TrustStep { step }) => {
            panic!("a trust step survived at {step:?}")
        }
        Err(_) => {}
    }
}

#[test]
fn every_rule_the_lane_emits_is_externally_checkable() {
    let exec = solve(DISTINCT_STORECOMM);
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
fn the_fragment_prints_and_pos_on_the_wire() {
    let mut exec = solve(DISTINCT_STORECOMM);
    let atom = first_disequality(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let document =
        ay_proof::try_export_alethe(&proof, &exec.ctx.terms).expect("the proof must render");
    assert!(
        document.contains(":rule and_pos"),
        "the lane's descent step must print under its own name:\n{document}"
    );
    assert!(
        document.contains(":rule th_resolution"),
        "the descent's resolution must print too:\n{document}"
    );
    assert!(
        !document.contains(":rule trust"),
        "no trust step may survive:\n{document}"
    );
    assert!(
        !document.contains(":rule hole"),
        "the lane must not trade a trust step for a hole:\n{document}"
    );
}
