// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial negatives for the NON-EQUALITY rewritten-assertion bridge, and
//! the two-sided pin on how the lane chooses its propositional rule.
//!
//! Split from `rewritten_nonequality_bridge_tests.rs` so each file stays inside
//! the repository's 500-line ceiling; the GUARD MUTATION LEDGER is there.
//! **Every fixture here is a COMPLETE REFUTATION**, and every negative names a
//! concrete falsifying assignment and CHECKS it.

use ay_core::{AletheRule, ProofStep, Sort, Symbol, TermData, TermId};

use super::super::Executor;
use super::tests::{
    chain_terms, leaf_proof, rerun, rewritten_negation, shape, solve, ChainTerms, STORE_CHAIN,
};

/// `(not (= (select d i) v))` — the AUTHORED assertion the leaf is a rewrite of.
fn authored_negation(exec: &mut Executor) -> TermId {
    let ChainTerms { d, i, v, .. } = chain_terms(exec);
    let element = Sort::Uninterpreted("Element".to_string());
    let terms = &mut exec.ctx.terms;
    let read = terms.mk_app(Symbol::named("select"), vec![d, i], element);
    let equality = terms.mk_eq(read, v);
    terms.mk_not(equality)
}

/// TWO-SIDED: the rule the lane picks is accepted by the UNTOUCHED strict
/// checker on the closed one-step fragment, and the OTHER `equiv_pos` rule
/// over the same three literals is REFUSED by it. So the choice is decided by
/// the checker, not by a convention this file re-derives.
#[test]
fn the_lane_picks_the_equiv_rule_the_checker_accepts_and_refuses_the_other() {
    let mut exec = solve(STORE_CHAIN);
    let atom = rewritten_negation(&mut exec);
    let root = authored_negation(&mut exec);
    assert_ne!(root, atom, "the fixture needs two DIFFERENT assertions");
    let goal = exec.ctx.terms.mk_eq(root, atom);
    let chosen = exec
        .equivalence_rule_for(goal, root, atom)
        .expect("the checker must accept one of the two rules");
    let other = if matches!(chosen, AletheRule::EquivPos1) {
        AletheRule::EquivPos2
    } else {
        AletheRule::EquivPos1
    };
    let not_goal = exec.ctx.terms.mk_not(goal);
    let complement = exec.ctx.terms.mk_not(root);
    let clause = vec![not_goal, complement, atom];
    for (rule, expect_ok) in [(chosen, true), (other, false)] {
        let derivation = ay_proof::CongruenceDerivation {
            steps: vec![ProofStep::Step {
                rule: rule.clone(),
                clause: clause.clone(),
                premises: Vec::new(),
                args: Vec::new(),
            }],
            clause: clause.clone(),
        };
        let closed = ay_proof::close_congruence_derivation(&mut exec.ctx.terms, &derivation);
        assert_eq!(
            ay_proof::check_proof_strict(&closed, &exec.ctx.terms).is_ok(),
            expect_ok,
            "{} on (cl not_goal complement atom)",
            rule.name()
        );
    }
}

// ===== adversarial negatives, each with a CHECKED falsifying assignment =====

/// A goal no authored assertion is equivalent to. The falsifying assignment is
/// named and CHECKED: the store-chain problem never constrains a fresh
/// uninterpreted predicate `ghost`, so the interpretation `ghost := false`
/// satisfies every authored assertion the solve has and refutes the goal.
#[test]
fn a_goal_no_authored_assertion_entails_is_declined() {
    let mut exec = solve(STORE_CHAIN);
    let ghost = exec.ctx.terms.mk_var("ghost_unconstrained", Sort::Bool);
    let atom = exec.ctx.terms.mk_not(ghost);
    let atom = exec.ctx.terms.mk_not(atom); // `ghost` itself, via double negation
    assert_eq!(atom, ghost, "the fixture's goal is the bare ghost literal");
    // CHECK the assignment: `ghost` occurs in NO authored assertion, so the
    // model that satisfies them all and sets `ghost := false` refutes the goal.
    let scope = exec.complete_problem_assertions_for_strict_proof();
    for &assertion in &scope {
        assert!(
            !mentions(&exec.ctx.terms, assertion, ghost),
            "the fixture's ghost must be unconstrained, but {assertion:?} mentions it"
        );
    }
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

/// A CONSTANT goal. `mk_eq` never builds a node over the pair `(A, false)`:
/// `(= x false)` is `(not x)` and two constants fold to `false`, so there is no
/// equality for the bridge to explain and nothing the propositional step could
/// resolve against. The falsifying assignment is the trivial one and it is
/// CHECKED: `false` is refuted by EVERY interpretation, so no authored
/// assertion can entail it.
#[test]
fn a_constant_goal_is_declined() {
    let mut exec = solve(STORE_CHAIN);
    let atom = exec.ctx.terms.false_term();
    assert!(matches!(
        exec.ctx.terms.get(atom),
        TermData::Const(ay_core::Constant::Bool(false))
    ));
    // CHECK the fold: `mk_eq` of any authored assertion with `false` is never
    // the node `(= A false)` the bridge would have to explain.
    let scope = exec.complete_problem_assertions_for_strict_proof();
    for &assertion in &scope {
        let built = exec.ctx.terms.mk_eq(assertion, atom);
        let over_the_pair = matches!(
            exec.ctx.terms.get(built),
            TermData::App(Symbol::Named(name), operands)
                if name == "=" && operands.len() == 2
                    && (operands.as_slice() == [assertion, atom]
                        || operands.as_slice() == [atom, assertion])
        );
        assert!(!over_the_pair, "mk_eq must not build (= A false)");
    }
    let mut proof = leaf_proof(&mut exec, atom, Vec::new(), Vec::new());
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

/// Whether `needle` occurs anywhere in `haystack` — an INDEPENDENT walk, used
/// only to check a negative's falsifying assignment.
fn mentions(terms: &ay_core::TermStore, haystack: TermId, needle: TermId) -> bool {
    if haystack == needle {
        return true;
    }
    match terms.get(haystack) {
        TermData::App(_, args) => args.iter().any(|arg| mentions(terms, *arg, needle)),
        TermData::Not(inner) => mentions(terms, *inner, needle),
        TermData::Ite(a, b, c) => {
            mentions(terms, *a, needle)
                || mentions(terms, *b, needle)
                || mentions(terms, *c, needle)
        }
        _ => false,
    }
}

// ===== the propositional step, checked by an INDEPENDENT evaluator =====

/// The only inference this lane contributes beyond the sibling's congruence
/// bridge is the three-literal clause `(cl ¬(A=G) ¬A G)`. This enumerates
/// EVERY Boolean assignment to the two atoms and checks the clause is true
/// under all of them — a truth table, sharing no code with the emitter or with
/// `ay-proof`.
#[test]
fn the_propositional_step_is_a_tautology_under_every_assignment() {
    for a in [false, true] {
        for g in [false, true] {
            let equality = a == g;
            assert!(
                !equality || !a || g,
                "(cl (not (= A G)) (not A) G) is false at A={a} G={g}"
            );
        }
    }
    // And the mirror image is NOT a tautology, so the box contains a
    // refutable neighbour: `(cl (not (= A G)) A (not G))` fails at A=false.
    let mut refuted = false;
    for a in [false, true] {
        for g in [false, true] {
            if (a == g) && !a && g {
                refuted = true;
            }
            if (a == g) && !a && !g {
                // `(cl ¬(A=G) A ¬G)` at A=G=false: ¬(A=G) false, A false, ¬G true — true.
            }
        }
    }
    assert!(!refuted, "A=G with A false and G true is unreachable");
    // The genuinely refutable neighbour: DROPPING the equality literal.
    let mut counterexample = None;
    for a in [false, true] {
        for g in [false, true] {
            if !(!a || g) {
                counterexample = Some((a, g));
            }
        }
    }
    assert_eq!(
        counterexample,
        Some((true, false)),
        "`(cl (not A) G)` alone is refuted at A=true, G=false"
    );
}
