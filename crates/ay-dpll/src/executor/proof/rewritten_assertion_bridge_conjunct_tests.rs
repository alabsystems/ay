// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `and`-CONJUNCT pool of the rewritten-assertion bridge LANE — section 2
//! of `rewritten_assertion_bridge_tests.rs`, split out only to keep each file
//! inside the repository's 500-line ceiling.
//!
//! Every fixture here is a REAL SOLVE of a COMPLETE problem, for the reason
//! the parent file's module documentation gives.

use super::{
    leaf_proof, premiseless_equality_trust_leaves, rerun, rewritten_assertion, shape, solve,
    STORE_CHAIN,
};
use crate::Executor;

use ay_core::{AletheRule, ProofId, ProofStep, Sort, Symbol, TermData, TermId};

/// The same three-store chain, but authored as ONE conjunction — the
/// `pointer-safe-5` shape. Measured on that file: its whole problem is a
/// single `(assert (let … (and …)))`, so `bridge_hypothesis_pool` (which
/// admits only problem assertions that are themselves a binary `=`) reported
/// `poolsize 0` for `problem_assertions=2` and the lane declined all five of
/// its leaves.
const AND_CHAIN: &str = r#"
    (set-logic QF_AX)
    (declare-sort Index 0)
    (declare-sort Element 0)
    (declare-fun a () (Array Index Element))
    (declare-fun b () (Array Index Element))
    (declare-fun c () (Array Index Element))
    (declare-fun d () (Array Index Element))
    (declare-fun i () Index)
    (declare-fun v () Element)
    (assert (and (= b (store a i v)) (= c b) (= d c)))
    (assert (not (= (select d i) v)))
    (check-sat)
"#;

/// `(= d (store a i v))` — entailed by the CONJUNCTS of the authored `and`,
/// and by nothing else in the problem scope.
fn and_chain_goal(exec: &mut Executor) -> TermId {
    let index = Sort::Uninterpreted("Index".to_string());
    let element = Sort::Uninterpreted("Element".to_string());
    let array = Sort::Array(Box::new(ay_core::ArraySort::new(
        index.clone(),
        element.clone(),
    )));
    let terms = &mut exec.ctx.terms;
    let a = terms.mk_var("a", array.clone());
    let d = terms.mk_var("d", array.clone());
    let i = terms.mk_var("i", index);
    let v = terms.mk_var("v", element);
    let stored = terms.mk_app(Symbol::named("store"), vec![a, i, v], array);
    terms.mk_eq(d, stored)
}

/// Every `and_pos` step of a proof, as (position, clause).
fn and_pos_steps(proof: &ay_core::Proof) -> Vec<(u32, Vec<TermId>)> {
    proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::AndPos(position),
                clause,
                ..
            } => Some((*position, clause.clone())),
            _ => None,
        })
        .collect()
}

#[test]
fn a_conjunct_hypothesis_is_derived_from_its_authored_root() {
    let mut exec = solve(AND_CHAIN);
    let goal = and_chain_goal(&mut exec);
    let mut proof = leaf_proof(&mut exec, goal);
    // The fixture must start REJECTED, or it proves nothing.
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
    assert_eq!(
        rerun(&mut exec, &mut proof),
        1,
        "the conjunct pool must reach a leaf the base pool cannot"
    );
    assert_eq!(premiseless_equality_trust_leaves(&exec, &proof), 0);
    assert!(
        !and_pos_steps(&proof).is_empty(),
        "the conjunct route descends by and_pos"
    );
    match exec.check_proof_strict_with_datatypes(&proof) {
        Ok(_) => {}
        // The fixture's own closing `assume (not goal)` is not authored.
        Err(ay_proof::ProofCheckError::UnauthorizedAssumption { .. }) => {}
        Err(other) => panic!("the rebuilt proof must replay, got {other:?}"),
    }
}

/// The soundness-critical property of this route: the CONJUNCT is never
/// assumed. Only the authored ROOT is, and the root is an exact member of the
/// strict scope.
#[test]
fn the_conjunct_route_only_ever_assumes_the_authored_root() {
    let mut exec = solve(AND_CHAIN);
    let goal = and_chain_goal(&mut exec);
    let mut proof = leaf_proof(&mut exec, goal);
    let negated = exec.ctx.terms.mk_not(goal);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let scope = exec.complete_problem_assertions_for_strict_proof();
    let mut assumed = 0usize;
    for step in &proof.steps {
        let ProofStep::Assume(term) = step else {
            continue;
        };
        if *term == negated {
            continue; // the fixture's own closing assume
        }
        assert!(
            scope.contains(term),
            "the lane assumed a term the strict scope does not carry"
        );
        assumed += 1;
    }
    assert!(assumed > 0, "the root must actually be assumed");
    // Every `and_pos` gate literal is the RAW negation of a conjunction, so
    // the descent is over the authored `and` tree rather than a De Morgan
    // dual the resolution below could not cancel.
    for (_, clause) in and_pos_steps(&proof) {
        assert_eq!(clause.len(), 2);
        assert!(
            matches!(exec.ctx.terms.get(clause[0]), TermData::Not(inner)
                if matches!(exec.ctx.terms.get(*inner),
                    TermData::App(Symbol::Named(name), _) if name == "and")),
            "the and_pos gate literal must be a RAW (not (and ..))"
        );
    }
}

/// The route the lane does NOT take, and WHY — measured against the real
/// validator rather than inferred. `validate_reachable_assumes_in_problem_scope`
/// admits only EXACT problem-scope membership, so an `Assume` of an
/// `and`-CONJUNCT is refused; the lane therefore derives the conjunct from an
/// `assume` of its ROOT. Both directions are pinned so a future widening of
/// that validator shows up here rather than silently changing what the lane
/// may assume.
#[test]
fn an_assumed_conjunct_is_refused_by_the_exact_membership_validator() {
    let mut exec = solve(AND_CHAIN);
    let scope = exec.complete_problem_assertions_for_strict_proof();
    let root = *scope
        .iter()
        .find(|&&term| {
            matches!(exec.ctx.terms.get(term),
                TermData::App(Symbol::Named(name), _) if name == "and")
        })
        .expect("the fixture's authored assertion is one conjunction");
    let TermData::App(_, conjuncts) = exec.ctx.terms.get(root) else {
        unreachable!()
    };
    let conjunct = conjuncts[0];
    assert!(
        !scope.contains(&conjunct),
        "the fixture depends on the conjunct NOT being an exact scope member"
    );
    let negated = exec.ctx.terms.mk_not(conjunct);
    let mut assumed = ay_core::Proof::new();
    assumed.steps.push(ProofStep::Assume(conjunct));
    assumed.steps.push(ProofStep::Assume(negated));
    assumed.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![ProofId(0), ProofId(1)],
        args: Vec::new(),
    });
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(&assumed, &scope).is_err(),
        "an assumed CONJUNCT is not an exact problem-scope member"
    );
    assert!(
        ay_proof::validate_reachable_assumes_in_problem_scope(&assumed, &[conjunct, negated])
            .is_ok(),
        "the same proof with the conjunct IN scope is accepted — the refusal \
         above is about MEMBERSHIP, not about the proof's shape"
    );
}

/// The extension is STRICT: a leaf the base pool already derives is planned
/// from the base pool, and the fragment carries no `and_pos` at all.
#[test]
fn a_leaf_the_base_pool_derives_is_planned_without_the_conjunct_route() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_assertion(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    assert!(
        and_pos_steps(&proof).is_empty(),
        "the base pool derives this leaf; the conjunct route must not fire"
    );
}

/// A conjunction the STRICT scope does not carry must license nothing — the
/// same guard as `an_assertion_outside_the_strict_scope_is_never_assumed`,
/// re-aimed at the conjunct route. The GHOST conjunction is offered as a
/// problem assertion and its conjunct entails the goal; the lane must still
/// decline, because assuming the ghost root is an authority the mandatory
/// gate refuses.
#[test]
fn a_conjunction_outside_the_strict_scope_is_never_assumed() {
    let mut exec = solve(AND_CHAIN);
    let (goal, ghost_root) = {
        let element = Sort::Uninterpreted("Element".to_string());
        let terms = &mut exec.ctx.terms;
        let g1 = terms.mk_var("ghost_1", element.clone());
        let g2 = terms.mk_var("ghost_2", element.clone());
        let fg1 = terms.mk_app(Symbol::named("f"), vec![g1], element.clone());
        let fg2 = terms.mk_app(Symbol::named("f"), vec![g2], element.clone());
        let goal = terms.mk_eq(fg1, fg2);
        let hypothesis = terms.mk_eq(g1, g2);
        let filler = terms.mk_var("ghost_3", element);
        let filler_eq = terms.mk_eq(filler, filler);
        let ghost_root = terms.mk_app(
            Symbol::named("and"),
            vec![hypothesis, filler_eq],
            Sort::Bool,
        );
        (goal, ghost_root)
    };
    assert!(
        !exec
            .complete_problem_assertions_for_strict_proof()
            .contains(&ghost_root),
        "the fixture depends on the ghost root being OUTSIDE the strict scope"
    );
    let mut proof = leaf_proof(&mut exec, goal);
    let before = shape(&proof);
    assert_eq!(
        exec.derive_rewritten_assertions_by_congruence(&mut proof, &[ghost_root]),
        0,
        "a conjunction the strict scope does not carry must license nothing"
    );
    assert_eq!(shape(&proof), before, "the proof must be byte-identical");
    assert!(
        !proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Assume(term) if *term == ghost_root)),
        "a conjunction outside the strict scope must never be assumed"
    );
}

/// A goal no CONJUNCT entails keeps its byte-identical `trust` step. The
/// falsifying assignment is concrete and CHECKED here: send `unrelated_l` to
/// 0 and `unrelated_r` to 1 and every other term to its own class. Every
/// authored conjunct is satisfied — the check below is that no authored
/// assertion so much as MENTIONS either side, so no congruence class can
/// merge them — while the goal `(= unrelated_l unrelated_r)` is FALSE. No
/// sound derivation from this scope exists, and the lane must decline.
#[test]
fn a_goal_no_conjunct_entails_keeps_its_trust_step() {
    let mut exec = solve(AND_CHAIN);
    let (left, right, unrelated) = {
        let element = Sort::Uninterpreted("Element".to_string());
        let terms = &mut exec.ctx.terms;
        let left = terms.mk_var("unrelated_l", element.clone());
        let right = terms.mk_var("unrelated_r", element);
        (left, right, terms.mk_eq(left, right))
    };
    assert_ne!(left, right, "the two sides must be distinct terms");
    let scope = exec.complete_problem_assertions_for_strict_proof();
    for &assertion in &scope {
        let rendered = ay_proof::format_term_alethe(&exec.ctx.terms, assertion);
        assert!(
            !rendered.contains("unrelated_l") && !rendered.contains("unrelated_r"),
            "the falsifying assignment is only valid if the scope is silent \
             about both sides: {rendered}"
        );
    }
    let mut proof = leaf_proof(&mut exec, unrelated);
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before, "the proof must be byte-identical");
}

/// The wire: the conjunct fragment prints, and prints `and_pos` rather than a
/// `hole`.
#[test]
fn the_conjunct_fragment_prints_its_own_rules_on_the_wire() {
    let mut exec = solve(AND_CHAIN);
    let goal = and_chain_goal(&mut exec);
    let mut proof = leaf_proof(&mut exec, goal);
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
        document.contains(":rule and_pos"),
        "the conjunct descent is an and_pos:\n{document}"
    );
    assert!(
        document.contains(":rule th_resolution"),
        "each descent is discharged by th_resolution:\n{document}"
    );
}

/// Every rule the conjunct route emits is externally checkable — `and_pos`
/// included.
#[test]
fn every_rule_the_conjunct_route_emits_is_externally_checkable() {
    let mut exec = solve(AND_CHAIN);
    let goal = and_chain_goal(&mut exec);
    let mut proof = leaf_proof(&mut exec, goal);
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
        assert_ne!(ay_core::wire_rule_name(rule.name()), "hole");
    }
}

/// GUARD MUTATION LEDGER — the `and`-CONJUNCT route.
///
/// | guard | named test |
/// |---|---|
/// | the conjunct ROOT is in the strict scope | `a_conjunction_outside_the_strict_scope_is_never_assumed` |
/// | the conjunct pool is tried only AFTER the base pool | `a_leaf_the_base_pool_derives_is_planned_without_the_conjunct_route` |
/// | the leaf prefix ends on exactly the hypothesis clause | `a_conjunct_hypothesis_is_derived_from_its_authored_root` |
/// | the `and_pos` gate literal is a RAW `(not (and ..))` | `the_conjunct_route_only_ever_assumes_the_authored_root` |
const CONJUNCT_GUARD_MUTATION_LEDGER: () = ();

#[test]
fn the_conjunct_guard_mutation_ledger_exists() {
    let () = CONJUNCT_GUARD_MUTATION_LEDGER;
}
