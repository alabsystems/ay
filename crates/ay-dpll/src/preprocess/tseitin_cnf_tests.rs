// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the `tseitin-cnf` preprocessing pass.
//!
//! Coverage:
//! - STRUCTURE: the output is genuinely clausal (a conjunction of disjunctions
//!   of literals) for non-CNF inputs (DNF, iff, xor, Boolean ite).
//! - HONESTY: the pass reports progress only when it changes the goal (a goal
//!   already in this clausal form is a fixpoint).
//!
//! The end-to-end **equisatisfiability** battery (solve input vs solve CNF over
//! ~40 random formulas, both SAT and UNSAT) lives in the tactics tests
//! (`api::solving::tactics::tests`), where the `Solver` term store is reachable.

use super::{PreprocessingPass, TseitinCnf};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

// ---------------------------------------------------------------------------
// Clausality checker: is `id` a literal / a clause?
// ---------------------------------------------------------------------------

/// A Boolean *connective* (something Tseitin must decompose): `not`, `and`,
/// `or`, `xor`, `=>`/`implies`, `=` between two Booleans (iff), a Boolean `ite`,
/// or a Boolean `distinct`. Everything else Boolean-sorted is an atom.
fn is_bool_connective(terms: &TermStore, id: TermId) -> bool {
    match terms.get(id) {
        TermData::Not(_) => true,
        TermData::Ite(..) => terms.sort(id) == &Sort::Bool,
        TermData::App(sym, args) => match sym.name() {
            "and" | "or" | "xor" | "=>" | "implies" => true,
            "=" => args.len() == 2 && terms.sort(args[0]) == &Sort::Bool,
            "distinct" => args.len() >= 2 && terms.sort(args[0]) == &Sort::Bool,
            _ => false,
        },
        _ => false,
    }
}

/// A *literal*: an atom or a single negation of an atom (no nested Boolean
/// structure).
fn is_literal(terms: &TermStore, id: TermId) -> bool {
    let inner = match terms.get(id) {
        TermData::Not(x) => *x,
        _ => id,
    };
    !is_bool_connective(terms, inner)
}

/// A *clause*: a literal, a flat `or` of literals, or a Boolean constant
/// (`true`/`false` — the trivially-satisfied / empty clause).
fn is_clause(terms: &TermStore, id: TermId) -> bool {
    match terms.get(id) {
        TermData::App(sym, args) if sym.name() == "or" => {
            args.iter().all(|&a| is_literal(terms, a))
        }
        _ => is_literal(terms, id),
    }
}

/// Assert every formula of a goal is a clause (so the goal is genuinely CNF).
fn assert_clausal(terms: &TermStore, goal: &[TermId]) {
    for &f in goal {
        assert!(
            is_clause(terms, f),
            "formula is not a clause: {:?}",
            terms.get(f)
        );
    }
}

// ---------------------------------------------------------------------------
// STRUCTURE: non-CNF inputs become genuinely clausal.
// ---------------------------------------------------------------------------

#[test]
fn dnf_becomes_clausal_with_aux_vars() {
    // (or (and a b) c): distributing would need aux vars for the conjunction.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let ab = terms.mk_and(vec![a, b]);
    let f = terms.mk_or(vec![ab, c]);

    let mut goal = vec![f];
    let changed = TseitinCnf::new().apply(&mut terms, &mut goal);
    assert!(changed, "a DNF formula must be rewritten into CNF");
    assert_clausal(&terms, &goal);
    // A fresh aux definition variable was introduced for the nested `and`.
    let has_aux = goal.iter().any(|&clause| mentions_aux(&terms, clause));
    assert!(has_aux, "the nested conjunction must get a fresh aux var");
}

#[test]
fn iff_becomes_clausal() {
    // (= a b) over Bool is iff — not a clause on its own.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let f = terms.mk_eq(a, b);
    assert!(
        is_bool_connective(&terms, f),
        "sanity: (= a b) over Bool is a connective (iff)"
    );

    let mut goal = vec![f];
    let changed = TseitinCnf::new().apply(&mut terms, &mut goal);
    assert!(changed);
    assert_clausal(&terms, &goal);
}

#[test]
fn xor_and_bool_ite_become_clausal() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let x = terms.mk_xor(a, b);
    let ite = terms.mk_ite(c, a, b);
    // A nested formula combining xor and a Boolean ite under an `or`.
    let f = terms.mk_or(vec![x, ite]);

    let mut goal = vec![f];
    let changed = TseitinCnf::new().apply(&mut terms, &mut goal);
    assert!(changed);
    assert_clausal(&terms, &goal);
}

// ---------------------------------------------------------------------------
// HONESTY: progress reporting is truthful.
// ---------------------------------------------------------------------------

#[test]
fn already_clausal_goal_is_a_fixpoint() {
    // {a, (or b c), ¬d} is already CNF — the pass must make NO progress and
    // leave the goal byte-for-byte unchanged (so `repeat`/solver see a fixpoint).
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let d = terms.mk_var("d", Sort::Bool);
    let bc = terms.mk_or(vec![b, c]);
    let nd = terms.mk_not(d);
    let before = vec![a, bc, nd];

    let mut goal = before.clone();
    let changed = TseitinCnf::new().apply(&mut terms, &mut goal);
    assert!(
        !changed,
        "an already-CNF goal must be a fixpoint (no progress)"
    );
    assert_eq!(goal, before, "a fixpoint goal must be left unchanged");
}

#[test]
fn top_level_conjunction_splits_like_elim_and() {
    // A top-level `and` splits into conjuncts WITHOUT introducing a top gate.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let inner = terms.mk_and(vec![a, b]);
    let outer = terms.mk_and(vec![inner, c]);

    let mut goal = vec![outer];
    let changed = TseitinCnf::new().apply(&mut terms, &mut goal);
    assert!(changed);
    assert_eq!(goal.len(), 3, "top-level and splits into 3 unit clauses");
    assert!(goal.contains(&a) && goal.contains(&b) && goal.contains(&c));
    assert_clausal(&terms, &goal);
    // No aux var needed for a pure top-level conjunction of literals.
    assert!(
        goal.iter().all(|&f| !mentions_aux(&terms, f)),
        "a top-level conjunction of literals needs no aux vars"
    );
}

/// Does `id` (a literal or a clause) mention a `tseitin_*` aux variable?
fn mentions_aux(terms: &TermStore, id: TermId) -> bool {
    let mut stack = vec![id];
    let mut seen = std::collections::HashSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(name, _) => {
                if name.starts_with("tseitin") {
                    return true;
                }
            }
            TermData::Not(x) => stack.push(*x),
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Ite(a, b, c) => {
                stack.push(*a);
                stack.push(*b);
                stack.push(*c);
            }
            _ => {}
        }
    }
    false
}
