// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Coverage for the MINTED-DEFINITION leaf lane — the one lane in this family
//! that writes a step the proof did not contain.
//!
//! This file owns the FIXTURES, the positive end-to-end path, the wire check
//! and the shape guards. `minted_definition_leaf_negative_tests.rs` owns the
//! four AUTHORITY negatives the ask names — the definiendum in an authored
//! assertion, in an `assume`, two definientia for one symbol, and the symbol
//! inside its own definiens — each with a falsifying assignment CHECKED
//! in-test by an independent evaluator, plus the two-sided exhaustive sweep.
//!
//! **Every fixture is a COMPLETE REFUTATION** and asserts, before running the
//! lane, that it starts REJECTED and that the leaf this lane claims is
//! present.
//!
//! # GUARD MUTATION LEDGER
//!
//! Each guard was deleted or weakened, the lane's whole test set re-run, the
//! named test observed FAILING, and the guard restored. Results are recorded
//! in `minted_definition_leaf_negative_tests.rs`, next to the negatives that
//! carry them.

use ay_core::{AletheRule, ProofId, ProofStep, Sort, TermId};
use ay_frontend::parse;

use crate::Executor;

/// The `purify_bool_args` shape, in miniature: a COMPOUND Boolean argument of
/// an uninterpreted function. The root is authored; the leaf replaces the
/// compound argument with a symbol the problem never mentions, exactly as the
/// purification pass does before `check_sat` restores the assertion stack and
/// destroys the definition.
pub(super) const PURIFY: &str = r#"
    (set-logic QF_UF)
    (declare-fun g () Bool)
    (declare-fun h () Bool)
    (declare-fun k () Bool)
    (declare-fun zz () Bool)
    (declare-fun ff (Bool Bool) Bool)
    (assert (ff (and g h) k))
    (assert zz)
    (assert (not zz))
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

pub(super) fn boolvar(exec: &mut Executor, name: &str) -> TermId {
    exec.ctx.terms.mk_var(name, Sort::Bool)
}

/// `(ff a b)` — an uninterpreted application, so its argument ORDER is fixed
/// (unlike `mk_and`/`mk_or`, which sort and flatten).
pub(super) fn ff(exec: &mut Executor, a: TermId, b: TermId) -> TermId {
    exec.ctx
        .terms
        .mk_app(ay_core::Symbol::named("ff"), vec![a, b], Sort::Bool)
}

/// The authored root of the `PURIFY` fixture, taken from the STRICT SCOPE so a
/// test cannot disagree with the solver about what was authored.
pub(super) fn authored_ff_root(exec: &Executor) -> TermId {
    exec.complete_problem_assertions_for_strict_proof()
        .into_iter()
        .find(|&term| {
            matches!(
                exec.ctx.terms.get(term),
                ay_core::TermData::App(ay_core::Symbol::Named(name), _) if name == "ff"
            )
        })
        .expect("the fixture's root must be in the strict scope")
}

/// Every premiseless, argument-free `trust` step with a unit clause.
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

/// A comparable rendering of a proof's steps. `ProofStep` has no `PartialEq`.
pub(super) fn shape(proof: &ay_core::Proof) -> String {
    format!("{:?}", proof.steps)
}

/// The SYNTACTIC complement of `literal` — the term a resolution can cancel it
/// against. `mk_not` returns the De Morgan DUAL for an `and`/`or` literal.
pub(super) fn complement(exec: &mut Executor, literal: TermId) -> TermId {
    let normalized = exec.ctx.terms.mk_not(literal);
    let cancels = match exec.ctx.terms.get(normalized) {
        ay_core::TermData::Not(inner) => *inner == literal,
        _ => matches!(
            exec.ctx.terms.get(literal),
            ay_core::TermData::Not(inner) if *inner == normalized
        ),
    };
    if cancels {
        normalized
    } else {
        exec.ctx.terms.mk_not_raw(literal)
    }
}

/// A COMPLETE REFUTATION carrying `goal` as its premiseless `trust` leaf.
///
/// The CLOSER is a second `trust` step, not an `assume` - deliberately, and it
/// is the fixture discipline this lane forces. Freshness is a statement about
/// the FINISHED proof's `assume` set, so an `assume (not goal)` would itself
/// MENTION the fresh definiendum and every mint would decline for a reason
/// that is not the one under test. Measured: the first version of this file
/// used an `assume` closer and all six positive tests failed with the lane
/// returning 0. The corpus population has no such assume - its leaf is
/// consumed by resolutions.
pub(super) fn leaf_proof(exec: &mut Executor, goal: TermId) -> ay_core::Proof {
    let negated = complement(exec, goal);
    let mut proof = ay_core::Proof::new();
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![goal],
        premises: Vec::new(),
        args: Vec::new(),
    });
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![negated],
        premises: Vec::new(),
        args: Vec::new(),
    });
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![ProofId(0), ProofId(1)],
        args: Vec::new(),
    });
    proof
}

/// The lane's own entry point, run against the executor's strict scope.
pub(super) fn rerun(exec: &mut Executor, proof: &mut ay_core::Proof) -> usize {
    let scope = exec.complete_problem_assertions_for_strict_proof();
    exec.derive_leaves_over_minted_definitions(proof, &scope)
}

/// `(ff pp k)` — the `PURIFY` root with its compound argument replaced by a
/// symbol the problem never mentions.
pub(super) fn purified_leaf(exec: &mut Executor) -> TermId {
    let pp = boolvar(exec, "pp");
    let k = boolvar(exec, "k");
    ff(exec, pp, k)
}

// ===== the lane, on a hand-built leaf over a REAL SOLVE =====

#[test]
fn a_leaf_over_a_fresh_symbol_is_derived_by_minting_its_definition() {
    let mut exec = solve(PURIFY);
    let atom = purified_leaf(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    assert!(
        exec.check_proof_strict_with_datatypes(&proof).is_err(),
        "the fixture must start REJECTED"
    );
    assert_eq!(
        premiseless_unit_trust_leaves(&proof),
        2,
        "the leaf and its trust closer"
    );
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    assert_eq!(
        premiseless_unit_trust_leaves(&proof),
        1,
        "only the fixture's own closer survives"
    );
    // The definition the lane wrote must be exactly `pp := (and g h)`, and it
    // must be admitted by the CHECKER's own whole-proof registry.
    let pp = boolvar(&mut exec, "pp");
    let g = boolvar(&mut exec, "g");
    let h = boolvar(&mut exec, "h");
    let definiens = exec.ctx.terms.mk_and(vec![g, h]);
    let minted: Vec<(Vec<TermId>, Vec<TermId>)> = proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step {
                rule: AletheRule::FreshDefEq,
                clause,
                args,
                ..
            } => Some((clause.clone(), args.clone())),
            _ => None,
        })
        .collect();
    assert_eq!(minted.len(), 1, "exactly one definition is minted");
    assert_eq!(minted[0].1, vec![pp], "the definiendum is the fresh symbol");
    let shape = ay_core::proof_validation::recognize_fresh_def_eq(
        &exec.ctx.terms,
        &minted[0].0,
        0,
        &minted[0].1,
    )
    .expect("the checker's own recognizer must admit the minted step");
    assert_eq!(shape.definiens, definiens);
}

#[test]
fn the_checkers_own_registry_admits_the_finished_proof() {
    let mut exec = solve(PURIFY);
    let atom = purified_leaf(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let scope = exec.complete_problem_assertions_for_strict_proof();
    let registry = ay_proof::FreshDefRegistry::collect(&proof, &exec.ctx.terms, Some(&scope))
        .expect("Gate 2 must hold on the finished proof");
    assert_eq!(registry.len(), 1);
}

/// The TRADE this lane makes, stated exactly and pinned.
///
/// Every rule the lane emits is externally checkable EXCEPT `fresh_def_eq`,
/// which is AY-specific and lowers to an honest `hole` on the wire (pinned by
/// `ay-proof`'s own `a_fresh_def_eq_lowers_to_an_honest_hole_with_no_args`).
/// So the trade is ONE `trust` for ONE `hole`, which is a strict improvement:
/// a `hole` is a gap the checker RECORDS, a `trust` is an unverified claim
/// that fails the mandatory gate. The store-over-store lane makes the same
/// trade for the same reason.
#[test]
fn every_rule_the_lane_emits_is_checkable_except_the_definition_which_is_a_hole() {
    let mut exec = solve(PURIFY);
    let atom = purified_leaf(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let mut holes = 0usize;
    for step in &proof.steps {
        let ProofStep::Step { rule, .. } = step else {
            continue;
        };
        if matches!(rule, AletheRule::FreshDefEq) {
            holes += 1;
            assert_eq!(
                ay_core::wire_rule_name(rule.name()),
                "hole",
                "a fresh definition lowers to an honest hole"
            );
            continue;
        }
        if matches!(rule, AletheRule::Trust) {
            continue; // the fixture's own closer
        }
        assert!(
            ay_core::is_checkable_alethe_rule(rule.name()),
            "the lane emitted {}, which is not externally checkable",
            rule.name()
        );
        assert_ne!(
            ay_core::wire_rule_name(rule.name()),
            "hole",
            "no rule except the definition may lower to a hole"
        );
    }
    assert_eq!(holes, 1, "exactly one minted definition");
}

/// The WIRE, pinned as EXACT TEXT.
///
/// The whole finished document, verbatim, is:
///
/// ```text
/// (step t0  (cl (= (and g h) pp))                          :rule hole)
/// (step t1  (cl (= k k))                                   :rule eq_reflexive)
/// (step t2  (cl (not (= (and g h) pp)) (not (= k k))
///               (= (ff (and g h) k) (ff pp k)))            :rule eq_congruent)
/// (step t3  ...                                            :rule th_resolution)
/// (step t4  (cl (= (ff (and g h) k) (ff pp k)))            :rule th_resolution)
/// (assume t5 (ff (and g h) k))
/// (step t6  (cl (not (= ..)) (not (ff (and g h) k)) (ff pp k)) :rule equiv_pos2)
/// (step t7  (cl (not (ff (and g h) k)) (ff pp k))          :rule th_resolution)
/// (step t8  (cl (ff pp k))                                 :rule th_resolution)
/// (step t9  (cl (not (ff pp k)))                           :rule hole)   <- the fixture's closer
/// (step t10 (cl)                                           :rule resolution)
/// ```
#[test]
fn the_fragment_prints_the_minted_definition_as_a_hole_and_no_trust() {
    let mut exec = solve(PURIFY);
    let atom = purified_leaf(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let document =
        ay_proof::try_export_alethe(&proof, &exec.ctx.terms).expect("the proof must render");
    // `trust` and `fresh_def_eq` both lower to an honest `hole`, so the whole
    // document carries NO `:rule trust` at all.
    assert_eq!(
        document.matches(":rule trust").count(),
        0,
        "no trust step may reach the wire:\n{document}"
    );
    assert!(
        document.contains("(step t0 (cl (= (and g h) pp)) :rule hole)"),
        "the minted definition prints as an honest hole:\n{document}"
    );
    assert!(
        document.contains("(step t9 (cl (not (ff pp k))) :rule hole)"),
        "the fixture's own closer is the other hole:\n{document}"
    );
    assert_eq!(
        document.matches(":rule hole").count(),
        2,
        "the minted definition and the fixture's closer, and nothing else:\n{document}"
    );
    assert!(
        document.contains(":rule equiv_pos2"),
        "the propositional step prints under its own name:\n{document}"
    );
    assert!(
        document.contains(":rule eq_congruent"),
        "the congruence half prints too:\n{document}"
    );
    assert!(
        document.contains("(step t8 (cl (ff pp k)) :rule th_resolution :premises (t7 t5))"),
        "the fragment ends on exactly the leaf's clause:\n{document}"
    );
    assert!(
        document.contains("(assume t5 (ff (and g h) k))"),
        "the ONLY assume is the authored root:\n{document}"
    );
    assert_eq!(
        document.matches("(assume ").count(),
        1,
        "exactly one assume:\n{document}"
    );
}

#[test]
fn the_lane_assumes_only_authored_roots() {
    let mut exec = solve(PURIFY);
    let atom = purified_leaf(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    assert_eq!(rerun(&mut exec, &mut proof), 1);
    let scope: Vec<TermId> = exec.complete_problem_assertions_for_strict_proof();
    let mut assumed = 0usize;
    for step in &proof.steps {
        let ProofStep::Assume(term) = step else {
            continue;
        };
        assumed += 1;
        assert!(
            scope.contains(term),
            "the lane assumed a term outside the strict scope"
        );
    }
    assert_eq!(assumed, 1, "the lane assumes exactly the authored root");
}

// ===== the shape guards =====

#[test]
fn a_proof_carrying_an_anchor_is_left_alone() {
    let mut exec = solve(PURIFY);
    let atom = purified_leaf(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    proof.steps.push(ProofStep::Anchor {
        end_step: ProofId(0),
        variables: Vec::new(),
    });
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

#[test]
fn a_trust_step_with_premises_is_left_alone() {
    let mut exec = solve(PURIFY);
    let atom = purified_leaf(&mut exec);
    let negated = complement(&mut exec, atom);
    let mut proof = ay_core::Proof::new();
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![negated],
        premises: Vec::new(),
        args: Vec::new(),
    });
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
    assert_eq!(shape(&proof), before);
}

#[test]
fn a_trust_step_with_args_is_left_alone() {
    let mut exec = solve(PURIFY);
    let atom = purified_leaf(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    let ProofStep::Step { args, .. } = &mut proof.steps[0] else {
        panic!("the leaf is a generic step");
    };
    args.push(atom);
    assert!(exec.check_proof_strict_with_datatypes(&proof).is_err());
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

/// A binary `=` leaf belongs to the EQUALITY bridge and this lane never
/// competes for one. The fixture authors a binary `=` ROOT so the refusal is
/// observable: without Guard 2b the lane would align `(= pp k)` against
/// `(= (and g h) k)` and derive it, taking a leaf out of the sibling lane's
/// population.
#[test]
fn a_binary_equality_leaf_is_left_to_the_sibling_lane() {
    let mut exec = solve(
        r#"
        (set-logic QF_UF)
        (declare-fun g () Bool)
        (declare-fun h () Bool)
        (declare-fun k () Bool)
        (declare-fun zz () Bool)
        (declare-fun ff (Bool Bool) Bool)
        (assert (= (ff (and g h) k) k))
        (assert zz)
        (assert (not zz))
        (check-sat)
    "#,
    );
    let pp = boolvar(&mut exec, "pp");
    let k = boolvar(&mut exec, "k");
    let left = ff(&mut exec, pp, k);
    let atom = exec.ctx.terms.mk_eq(left, k);
    assert!(
        matches!(
            exec.ctx.terms.get(atom),
            ay_core::TermData::App(ay_core::Symbol::Named(name), operands)
                if name == "=" && operands.len() == 2
        ),
        "the fixture must genuinely build a binary `=` leaf"
    );
    let mut proof = leaf_proof(&mut exec, atom);
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}

#[test]
fn an_assertion_outside_the_handed_scope_is_never_assumed() {
    let mut exec = solve(PURIFY);
    let atom = purified_leaf(&mut exec);
    let mut proof = leaf_proof(&mut exec, atom);
    let root = authored_ff_root(&exec);
    let scope: Vec<TermId> = exec
        .complete_problem_assertions_for_strict_proof()
        .into_iter()
        .filter(|&term| term != root)
        .collect();
    let before = shape(&proof);
    assert_eq!(
        exec.derive_leaves_over_minted_definitions(&mut proof, &scope),
        0,
        "the root is out of the handed scope, so nothing may be assumed"
    );
    assert_eq!(shape(&proof), before);
    // TWO-SIDED: with the root back in scope the SAME leaf is derived.
    assert_eq!(rerun(&mut exec, &mut proof), 1);
}
