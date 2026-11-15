// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mutation differentials over the equality-orientation pivot bridge.
//!
//! The shape is the one measured on
//! `benchmarks/smt/QF_ABV/csplit_repro_indirect_store_unsat.smt2`: an assumed
//! NEGATED equality carrying the problem file's operand order, resolved
//! against the same atom derived in the interned order.

use super::printed_equalities_are_reversed;
use crate::try_export_alethe_with_problem_scope_and_overrides;
use crate::AlethePrintError;
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore};

/// A Boolean premise `p`, the atom `(= x y)` and its negation, in one store.
struct Fixture {
    terms: TermStore,
    positive: TermId,
    atom: TermId,
    negated_atom: TermId,
}

fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let positive = terms.mk_var("p", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    // Built through `mk_app` so the operand order under test is the one this
    // fixture states, not whatever identity order `mk_eq` would choose.
    let atom = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let negated_atom = terms.mk_not_raw(atom);
    Fixture {
        terms,
        positive,
        atom,
        negated_atom,
    }
}

/// `p`, `(not (= x y))`, a lemma `(cl (not p) (= x y))`, and two
/// `th_resolution` steps down to the empty clause.
fn full_proof(fixture: &mut Fixture) -> Proof {
    let not_positive = fixture.terms.mk_not_raw(fixture.positive);
    let mut built = Proof::new();
    built.add_step(ProofStep::Assume(fixture.positive));
    built.add_step(ProofStep::Assume(fixture.negated_atom));
    let lemma = built.add_rule_step(
        AletheRule::Hole,
        vec![not_positive, fixture.atom],
        Vec::new(),
        Vec::new(),
    );
    let derived = built.add_rule_step(
        AletheRule::ThResolution,
        vec![fixture.atom],
        vec![lemma, ProofId(0)],
        Vec::new(),
    );
    built.add_rule_step(
        AletheRule::ThResolution,
        Vec::new(),
        vec![derived, ProofId(1)],
        Vec::new(),
    );
    built
}

fn scope(proof: &Proof) -> Vec<TermId> {
    let mut scope = Vec::new();
    for step in &proof.steps {
        match step {
            ProofStep::Assume(term) => scope.push(*term),
            ProofStep::TheoryLemma { clause, .. } => scope.extend(clause.iter().copied()),
            ProofStep::Step { clause, args, .. } => {
                scope.extend(clause.iter().copied());
                scope.extend(args.iter().copied());
            }
            _ => {}
        }
    }
    scope
}

fn export(
    fixture: &Fixture,
    proof: &Proof,
    overrides: &DetHashMap<TermId, String>,
) -> Result<String, AlethePrintError> {
    try_export_alethe_with_problem_scope_and_overrides(
        proof,
        &fixture.terms,
        &scope(proof),
        Some(overrides),
    )
}

/// THE DEFECT. The authored operand order reaches the assumed literal and
/// nothing else, so one atom prints two ways and no resolution eliminates the
/// pivot. Before the bridge this was a REFUSED EXPORT: `unsat` with no
/// document at all.
#[test]
fn a_reversed_equality_pivot_is_bridged_not_refused() {
    let mut fixture = fixture();
    let proof = full_proof(&mut fixture);
    let mut overrides = DetHashMap::default();
    overrides.insert(fixture.negated_atom, "(not (= y x))".to_string());

    let output = export(&fixture, &proof, &overrides).expect("the bridged step must export");
    assert!(
        output.contains("(assume t1 (not (= y x)))"),
        "the assumed literal must keep the problem's own operand order:\n{output}"
    );
    assert!(
        output.contains("(step t4.sy (cl (= (= x y) (= y x))) :rule eq_symmetric)"),
        "the two orientations must be stated equivalent by the checker's own \
         rule:\n{output}"
    );
    assert!(
        output.contains(
            "(step t4.sy.p (cl (not (= (= x y) (= y x))) (not (= x y)) (= y x)) :rule equiv_pos2)"
        ),
        "the equivalence must be turned into the implication the resolution \
         consumes:\n{output}"
    );
    assert!(
        output.contains("(step t4 (cl) :rule resolution :premises (t3 t4.sy t4.sy.p t1))"),
        "the repaired step must cite the bridge between its original \
         premises:\n{output}"
    );
}

/// The differential. With the override absent both occurrences print the
/// interned order, the printed replay succeeds, and the step must render
/// byte-identically to what it rendered before this bridge existed. A repair
/// that fires on correct steps destroys evidence.
#[test]
fn an_aligned_equality_pivot_renders_unchanged() {
    let mut fixture = fixture();
    let proof = full_proof(&mut fixture);
    let overrides = DetHashMap::default();

    let output = export(&fixture, &proof, &overrides).expect("an aligned pivot must export");
    assert!(
        output.contains("(step t4 (cl) :rule th_resolution :premises (t3 t1))"),
        "an aligned pivot must keep the stock rendering:\n{output}"
    );
    assert!(
        !output.contains("t4.sy"),
        "no bridge may be inserted into a step that already replays:\n{output}"
    );
}

/// A divergence that is NOT an equality re-orientation must still DECLINE.
/// An honest `no` outranks a green flag with nothing behind it.
#[test]
fn a_divergence_that_is_not_a_reorientation_still_declines_the_export() {
    let mut fixture = fixture();
    let proof = full_proof(&mut fixture);
    let mut overrides = DetHashMap::default();
    // Same head, same arity, DIFFERENT content: the printed operands are not a
    // permutation of the atom's own, so there is nothing honest to bridge.
    overrides.insert(fixture.negated_atom, "(not (= y z))".to_string());

    let error = export(&fixture, &proof, &overrides).expect_err("an unbridgeable pivot declines");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { .. }),
        "{error:?}"
    );
}

/// The predicate is read off the TEXT, and it never calls a non-divergence a
/// divergence: `(= x x)` reversed is itself.
#[test]
fn the_reversal_predicate_is_exact() {
    assert!(printed_equalities_are_reversed("(= x y)", "(= y x)"));
    assert!(printed_equalities_are_reversed(
        "(= val (select b idx))",
        "(= (select b idx) val)"
    ));
    // Bit-vector literal spellings the replay already collapses.
    assert!(printed_equalities_are_reversed(
        "(= #b0000 x)",
        "(= x (_ bv0 4))"
    ));
    assert!(!printed_equalities_are_reversed("(= x x)", "(= x x)"));
    assert!(!printed_equalities_are_reversed("(= x y)", "(= x y)"));
    assert!(!printed_equalities_are_reversed("(= x y)", "(= y z)"));
    assert!(!printed_equalities_are_reversed("(= x y z)", "(= z y x)"));
    assert!(!printed_equalities_are_reversed("(<= x y)", "(<= y x)"));
    assert!(!printed_equalities_are_reversed("(= x y)", "(p x y)"));
}
