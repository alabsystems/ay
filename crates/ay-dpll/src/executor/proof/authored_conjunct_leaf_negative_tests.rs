// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial negatives, an INDEPENDENT evaluator, and a two-sided
//! exhaustive sweep for the AUTHORED-CONJUNCT leaf lane.
//!
//! # The independent evaluator
//!
//! [`falsify`] is a Boolean model enumerator that re-reads the term DAG and
//! evaluates `and` / `or` / `not` / Boolean constants under an EXPLICIT
//! assignment to the atoms. It shares no code with the lane, with
//! `ay-proof`'s planner, or with the checker: it is a naive truth-table walk.
//! Every ACCEPT in the sweep below is re-checked by it, and every adversarial
//! negative NAMES the falsifying assignment it returns and asserts, in-test,
//! that the assignment really does satisfy the root and falsify the goal.
//!
//! A `None` from [`falsify`] is only read as evidence after [`decidable`] has
//! confirmed that the enumerator UNDERSTANDS every node of both terms, so a
//! term the evaluator silently does not model fails the test loudly instead of
//! reading as a clean bill of health.

use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, ProofStep, Sort, Symbol, TermData, TermId, TermStore};

use super::tests::{premiseless_unit_trust_leaves, shape, solve};
use crate::Executor;

// ===== the INDEPENDENT evaluator =====

/// Whether every node reachable from `root` is one this evaluator models.
pub(super) fn decidable(terms: &TermStore, root: TermId) -> bool {
    match terms.get(root) {
        TermData::Var(_, _) => *terms.sort(root) == Sort::Bool,
        TermData::Const(ay_core::Constant::Bool(_)) => true,
        TermData::Not(inner) => decidable(terms, *inner),
        TermData::App(Symbol::Named(name), args) if name == "and" || name == "or" => {
            args.iter().all(|&arg| decidable(terms, arg))
        }
        _ => false,
    }
}

/// Every Boolean atom reachable from `root`, in first-seen order.
pub(super) fn atoms(terms: &TermStore, root: TermId, out: &mut Vec<TermId>) {
    match terms.get(root) {
        TermData::Var(_, _) => {
            if !out.contains(&root) {
                out.push(root);
            }
        }
        TermData::Not(inner) => atoms(terms, *inner, out),
        TermData::App(_, args) => {
            for &arg in args {
                atoms(terms, arg, out);
            }
        }
        _ => {}
    }
}

/// Evaluate `term` under `env`. `None` means the evaluator does not model it.
pub(super) fn eval(
    terms: &TermStore,
    term: TermId,
    env: &DetHashMap<TermId, bool>,
) -> Option<bool> {
    match terms.get(term) {
        TermData::Var(_, _) => env.get(&term).copied(),
        TermData::Const(ay_core::Constant::Bool(value)) => Some(*value),
        TermData::Not(inner) => eval(terms, *inner, env).map(|value| !value),
        TermData::App(Symbol::Named(name), args) if name == "and" => {
            let mut all = true;
            for &arg in args {
                all &= eval(terms, arg, env)?;
            }
            Some(all)
        }
        TermData::App(Symbol::Named(name), args) if name == "or" => {
            let mut any = false;
            for &arg in args {
                any |= eval(terms, arg, env)?;
            }
            Some(any)
        }
        _ => None,
    }
}

/// An assignment satisfying `root` and falsifying `goal`, or `None` when
/// `root` entails `goal`. Enumerates EVERY assignment to the atoms of both.
pub(super) fn falsify(
    terms: &TermStore,
    root: TermId,
    goal: TermId,
) -> Option<Vec<(TermId, bool)>> {
    let mut vars: Vec<TermId> = Vec::new();
    atoms(terms, root, &mut vars);
    atoms(terms, goal, &mut vars);
    assert!(vars.len() <= 12, "the truth table must stay enumerable");
    for mask in 0u32..(1u32 << vars.len()) {
        let env: DetHashMap<TermId, bool> = vars
            .iter()
            .enumerate()
            .map(|(bit, &var)| (var, mask & (1 << bit) != 0))
            .collect();
        if eval(terms, root, &env) == Some(true) && eval(terms, goal, &env) == Some(false) {
            return Some(
                vars.iter()
                    .map(|&var| (var, env.get(&var).copied().unwrap_or(false)))
                    .collect(),
            );
        }
    }
    None
}

/// Re-check one named witness explicitly, so the test states the assignment
/// rather than merely trusting the enumerator's search.
fn witness_separates(
    terms: &TermStore,
    root: TermId,
    goal: TermId,
    witness: &[(TermId, bool)],
) -> bool {
    let env: DetHashMap<TermId, bool> = witness.iter().copied().collect();
    eval(terms, root, &env) == Some(true) && eval(terms, goal, &env) == Some(false)
}

// ===== fixtures =====

/// A problem whose ONLY authored non-trivial assertion is `root_text`, made
/// unsat by a contradiction over a variable no root mentions.
pub(super) fn scoped(root_text: &str) -> Executor {
    let text = format!(
        "(set-logic QF_UF)\n\
         (declare-fun b0 () Bool)\n\
         (declare-fun b1 () Bool)\n\
         (declare-fun b2 () Bool)\n\
         (declare-fun b3 () Bool)\n\
         (declare-fun zz () Bool)\n\
         (assert {root_text})\n\
         (assert zz)\n\
         (assert (not zz))\n\
         (check-sat)\n"
    );
    solve(&text)
}

pub(super) fn boolvar(exec: &mut Executor, name: &str) -> TermId {
    exec.ctx.terms.mk_var(name, Sort::Bool)
}

/// The SYNTACTIC complement of `literal` — the term a resolution can actually
/// cancel it against. `mk_not` returns the De Morgan DUAL for an `and`/`or`
/// literal, which is Boolean-equivalent but not a resolution complement, so a
/// fixture built with it would be refused for a reason that is not about the
/// lane. Measured: the first version of the sweep below reported a spurious
/// decline on every `(or b2 b3)` goal for exactly that reason.
pub(super) fn complement(exec: &mut Executor, literal: TermId) -> TermId {
    let normalized = exec.ctx.terms.mk_not(literal);
    let cancels = match exec.ctx.terms.get(normalized) {
        TermData::Not(inner) => *inner == literal,
        _ => matches!(exec.ctx.terms.get(literal), TermData::Not(inner) if *inner == normalized),
    };
    if cancels {
        normalized
    } else {
        exec.ctx.terms.mk_not_raw(literal)
    }
}

/// A COMPLETE REFUTATION carrying exactly `goal` as its one premiseless
/// `trust` leaf, closed against `goal`'s SYNTACTIC complement.
pub(super) fn exact_leaf_proof(exec: &mut Executor, goal: TermId) -> ay_core::Proof {
    let negated = complement(exec, goal);
    let mut proof = ay_core::Proof::new();
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![goal],
        premises: Vec::new(),
        args: Vec::new(),
    });
    proof.steps.push(ProofStep::Assume(negated));
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![ay_core::ProofId(0), ay_core::ProofId(1)],
        args: Vec::new(),
    });
    proof
}

/// Run the lane on a hand-built COMPLETE REFUTATION carrying exactly `goal` as
/// its one premiseless `trust` leaf.
pub(super) fn run(exec: &mut Executor, goal: TermId) -> (usize, ay_core::Proof) {
    let mut proof = exact_leaf_proof(exec, goal);
    assert_eq!(
        premiseless_unit_trust_leaves(&proof),
        1,
        "the fixture must carry the leaf this lane claims"
    );
    assert!(
        exec.check_proof_strict_with_datatypes(&proof).is_err(),
        "the fixture must start REJECTED"
    );
    let scope = exec.complete_problem_assertions_for_strict_proof();
    let derived = exec.derive_authored_conjunct_leaves(&mut proof, &scope);
    (derived, proof)
}

/// The authored root of a `scoped` fixture, taken from the strict scope so the
/// test cannot disagree with the solver about what was authored.
pub(super) fn authored_root(exec: &Executor, head: &str) -> TermId {
    exec.complete_problem_assertions_for_strict_proof()
        .into_iter()
        .find(|&term| {
            matches!(
                exec.ctx.terms.get(term),
                TermData::App(Symbol::Named(name), _) if name == head
            )
        })
        .expect("the fixture's root must be in the strict scope")
}

// ===== adversarial negatives, each naming a CHECKED falsifying assignment =====

#[test]
fn a_disjunct_of_an_authored_or_is_never_derived() {
    let mut exec = scoped("(or b0 b1)");
    let root = authored_root(&exec, "or");
    let b0 = boolvar(&mut exec, "b0");
    let b1 = boolvar(&mut exec, "b1");
    // FALSIFYING ASSIGNMENT: b0 := false, b1 := true. The root holds and the
    // goal does not, so `(or b0 b1) |= b0` is FALSE.
    assert!(decidable(&exec.ctx.terms, root) && decidable(&exec.ctx.terms, b0));
    assert!(
        witness_separates(&exec.ctx.terms, root, b0, &[(b0, false), (b1, true)]),
        "the named witness must satisfy the root and falsify the goal"
    );
    let before = shape(&exact_leaf_proof(&mut exec, b0));
    let (derived, proof) = run(&mut exec, b0);
    assert_eq!(derived, 0, "a DISJUNCT is not a conjunct");
    assert_eq!(shape(&proof), before);
}

#[test]
fn a_term_that_is_no_conjunct_at_all_is_never_derived() {
    let mut exec = scoped("(and b0 b1)");
    let root = authored_root(&exec, "and");
    let b2 = boolvar(&mut exec, "b2");
    let b0 = boolvar(&mut exec, "b0");
    let b1 = boolvar(&mut exec, "b1");
    // FALSIFYING ASSIGNMENT: b0 := true, b1 := true, b2 := false.
    assert!(decidable(&exec.ctx.terms, root) && decidable(&exec.ctx.terms, b2));
    assert!(witness_separates(
        &exec.ctx.terms,
        root,
        b2,
        &[(b0, true), (b1, true), (b2, false)]
    ));
    let (derived, _) = run(&mut exec, b2);
    assert_eq!(derived, 0);
}

#[test]
fn the_positive_atom_under_a_negated_conjunct_is_never_derived() {
    let mut exec = scoped("(and (not b0) b1)");
    let root = authored_root(&exec, "and");
    let b0 = boolvar(&mut exec, "b0");
    let b1 = boolvar(&mut exec, "b1");
    // The conjunct is `(not b0)`; the goal `b0` is its NEGATION.
    // FALSIFYING ASSIGNMENT: b0 := false, b1 := true.
    assert!(decidable(&exec.ctx.terms, root));
    assert!(witness_separates(
        &exec.ctx.terms,
        root,
        b0,
        &[(b0, false), (b1, true)]
    ));
    let (derived, _) = run(&mut exec, b0);
    assert_eq!(derived, 0);
    // TWO-SIDED: the conjunct ITSELF is derived from the same root.
    let not_b0 = exec.ctx.terms.mk_not(b0);
    assert!(falsify(&exec.ctx.terms, root, not_b0).is_none());
    let (derived, _) = run(&mut exec, not_b0);
    assert_eq!(derived, 1);
}

#[test]
fn a_strict_subterm_of_a_conjunct_is_never_derived() {
    let mut exec = scoped("(and (or b0 b1) b2)");
    let root = authored_root(&exec, "and");
    let b0 = boolvar(&mut exec, "b0");
    let b1 = boolvar(&mut exec, "b1");
    let b2 = boolvar(&mut exec, "b2");
    // `b0` is a sub-term of the conjunct `(or b0 b1)`, not a conjunct.
    // FALSIFYING ASSIGNMENT: b0 := false, b1 := true, b2 := true.
    assert!(decidable(&exec.ctx.terms, root));
    assert!(witness_separates(
        &exec.ctx.terms,
        root,
        b0,
        &[(b0, false), (b1, true), (b2, true)]
    ));
    let (derived, _) = run(&mut exec, b0);
    assert_eq!(derived, 0);
}

#[test]
fn a_conjunct_of_an_and_nested_under_an_or_is_never_derived() {
    let mut exec = scoped("(or (and b0 b1) b2)");
    let root = authored_root(&exec, "or");
    let b0 = boolvar(&mut exec, "b0");
    let b1 = boolvar(&mut exec, "b1");
    let b2 = boolvar(&mut exec, "b2");
    // FALSIFYING ASSIGNMENT: b0 := false, b1 := false, b2 := true.
    assert!(decidable(&exec.ctx.terms, root));
    assert!(witness_separates(
        &exec.ctx.terms,
        root,
        b0,
        &[(b0, false), (b1, false), (b2, true)]
    ));
    let (derived, _) = run(&mut exec, b0);
    assert_eq!(derived, 0, "the descent must stop at the first non-`and`");
}
