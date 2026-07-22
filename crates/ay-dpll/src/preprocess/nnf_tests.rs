// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Structural tests for the `nnf` preprocessing pass (`nnf.rs`).
//!
//! De Morgan pushes negation to atoms; `=>`/iff/`xor`/`ite`-over-Bool are
//! eliminated; double negation collapses; a non-Bool `=` atom and a negated
//! atom survive as literals; a negated quantifier flips kind (pure NNF, no
//! skolemization); and progress is reported honestly. The end-to-end
//! SAT/UNSAT EQUIVALENCE differential over ~30 random formulas lives in
//! `api::solving::tactics_tests` (which can reach the solver's term store).

#![allow(clippy::panic)]

use super::Nnf;
use crate::preprocess::{FlattenAnd, PreprocessingPass};
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn bvar(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Bool)
}

/// True when `id` is an *atom*: not a Boolean connective node that NNF must
/// eliminate or under which a negation may not sit.
fn is_atom(terms: &TermStore, id: TermId) -> bool {
    match terms.get(id) {
        TermData::App(sym, args) => match sym.name() {
            "and" | "or" | "=>" | "xor" => false,
            "=" => args.first().is_none_or(|&a| terms.sort(a) != &Sort::Bool),
            _ => true,
        },
        TermData::Not(_) => false,
        TermData::Ite(..) => terms.sort(id) != &Sort::Bool,
        TermData::Forall(..) | TermData::Exists(..) => false,
        _ => true,
    }
}

/// True when `id` is in negation normal form: negations sit only on atoms and
/// no `=>`/`<->`/`xor`/`ite`-over-Bool connective remains.
fn is_nnf(terms: &TermStore, id: TermId) -> bool {
    match terms.get(id).clone() {
        TermData::Const(_) | TermData::Var(_, _) => true,
        TermData::Not(inner) => is_atom(terms, inner),
        TermData::Ite(..) if terms.sort(id) == &Sort::Bool => false,
        TermData::Ite(..) => true,
        TermData::App(sym, args) => match sym.name() {
            "and" | "or" => args.iter().all(|&a| is_nnf(terms, a)),
            "=>" | "xor" => false,
            "=" if args.first().is_some_and(|&a| terms.sort(a) == &Sort::Bool) => false,
            _ => true,
        },
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => is_nnf(terms, body),
        _ => true,
    }
}

/// True when `id`'s DAG contains any `App` node named `op`.
fn contains_op(terms: &TermStore, id: TermId, op: &str) -> bool {
    match terms.get(id).clone() {
        TermData::App(sym, args) => {
            sym.name() == op || args.iter().any(|&a| contains_op(terms, a, op))
        }
        TermData::Not(inner) => contains_op(terms, inner, op),
        TermData::Ite(c, t, e) => {
            contains_op(terms, c, op) || contains_op(terms, t, op) || contains_op(terms, e, op)
        }
        TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => contains_op(terms, b, op),
        _ => false,
    }
}

/// Run only the NNF rewrite (no flatten) over a single formula.
fn nnf_one(terms: &mut TermStore, f: TermId) -> TermId {
    let mut goal = vec![f];
    Nnf::new().apply(terms, &mut goal);
    assert_eq!(goal.len(), 1, "the bare NNF pass never splits");
    goal[0]
}

// ---------------------------------------------------------------------------
// Structural tests
// ---------------------------------------------------------------------------

#[test]
fn de_morgan_pushes_negation_to_atoms() {
    let mut t = TermStore::new();
    let a = bvar(&mut t, "a");
    let b = bvar(&mut t, "b");
    let and = t.mk_and(vec![a, b]);
    // Build a raw Not so the pass — not the mk_not builder — does the work.
    let not_and = t.mk_not_raw(and);
    let out = nnf_one(&mut t, not_and);
    assert!(is_nnf(&t, out), "result must be NNF: {:?}", t.get(out));
    // ¬(a ∧ b) ≡ ¬a ∨ ¬b — a top-level `or`.
    assert!(matches!(t.get(out), TermData::App(s, _) if s.name() == "or"));
}

#[test]
fn iff_is_eliminated_into_and_of_ors() {
    let mut t = TermStore::new();
    let a = bvar(&mut t, "a");
    let b = bvar(&mut t, "b");
    // Bool `=` is iff; build the App directly (this is how AY elaborates it).
    let iff = t.mk_app(Symbol::named("="), vec![a, b], Sort::Bool);
    let out = nnf_one(&mut t, iff);
    assert!(
        is_nnf(&t, out),
        "iff must be eliminated to NNF: {:?}",
        t.get(out)
    );
    let is_bool_eq = matches!(t.get(out),
        TermData::App(s, args) if s.name() == "=" && t.sort(args[0]) == &Sort::Bool);
    assert!(!is_bool_eq, "the iff `=` node must be eliminated");
}

#[test]
fn xor_is_eliminated() {
    let mut t = TermStore::new();
    let a = bvar(&mut t, "a");
    let b = bvar(&mut t, "b");
    let xor = t.mk_xor(a, b);
    assert!(contains_op(&t, xor, "xor"), "precondition: xor node exists");
    let out = nnf_one(&mut t, xor);
    assert!(!contains_op(&t, out, "xor"), "xor must be eliminated");
    assert!(is_nnf(&t, out), "result must be NNF");
}

#[test]
fn bool_ite_is_eliminated() {
    let mut t = TermStore::new();
    let a = bvar(&mut t, "a");
    let b = bvar(&mut t, "b");
    let c = bvar(&mut t, "c");
    // Raw ite so it survives as an `Ite` node for the pass to eliminate.
    let ite = t.mk_ite_raw(a, b, c);
    assert!(
        matches!(t.get(ite), TermData::Ite(..)),
        "precondition: Ite node"
    );
    let out = nnf_one(&mut t, ite);
    assert!(
        !matches!(t.get(out), TermData::Ite(..)),
        "bool ite must be eliminated: {:?}",
        t.get(out)
    );
    assert!(is_nnf(&t, out), "result must be NNF");
}

#[test]
fn double_negation_collapses() {
    let mut t = TermStore::new();
    let a = bvar(&mut t, "a");
    let na = t.mk_not_raw(a);
    let nn = t.mk_not_raw(na);
    let out = nnf_one(&mut t, nn);
    assert_eq!(out, a, "(not (not a)) must become a");
}

#[test]
fn non_bool_equality_atom_is_preserved_as_a_literal() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let three = t.mk_int(BigInt::from(3));
    let eq = t.mk_app(Symbol::named("="), vec![x, three], Sort::Bool);
    // Positive: the atom is unchanged (nothing to push).
    let pos = nnf_one(&mut t, eq);
    assert_eq!(
        pos, eq,
        "a non-Bool `=` atom must be carried through unchanged"
    );
    // Negated: a single literal (Not over the atom), still NNF.
    let neg = t.mk_not_raw(eq);
    let out = nnf_one(&mut t, neg);
    assert!(is_nnf(&t, out));
    assert!(matches!(t.get(out), TermData::Not(inner) if *inner == eq));
}

#[test]
fn negated_universal_becomes_an_existential_pure_nnf() {
    // ¬∀x. φ ≡ ∃x. ¬φ — AY keeps the quantifier (equivalence-preserving),
    // diverging from z3's nnf, which additionally skolemizes.
    let mut t = TermStore::new();
    let y = t.mk_var("y", Sort::Int);
    let x = t.mk_var("x", Sort::Int);
    let zero = t.mk_int(BigInt::from(0));
    let xgt0 = t.mk_app(Symbol::named(">"), vec![x, zero], Sort::Bool);
    let ygtx = t.mk_app(Symbol::named(">"), vec![y, x], Sort::Bool);
    let body = t.mk_implies(xgt0, ygtx);
    let forall = t.mk_forall(vec![("x".to_string(), Sort::Int)], body);
    let neg = t.mk_not_raw(forall);
    let out = nnf_one(&mut t, neg);
    assert!(
        matches!(t.get(out), TermData::Exists(..)),
        "¬∀ must become ∃ (pure NNF, not skolemized): {:?}",
        t.get(out)
    );
    assert!(is_nnf(&t, out), "the existential body must be in NNF");
}

#[test]
fn progress_is_reported_honestly() {
    let mut t = TermStore::new();
    let a = bvar(&mut t, "a");
    let b = bvar(&mut t, "b");
    // Already-NNF disjunction of literals: no rewrite, no progress.
    let nb = t.mk_not_raw(b);
    let or = t.mk_or(vec![a, nb]);
    let mut goal = vec![or];
    assert!(
        !Nnf::new().apply(&mut t, &mut goal),
        "nnf must report NO progress on an already-NNF formula"
    );
    // An iff must be rewritten: progress.
    let iff = t.mk_app(Symbol::named("="), vec![a, b], Sort::Bool);
    let mut goal = vec![iff];
    assert!(
        Nnf::new().apply(&mut t, &mut goal),
        "nnf must report progress when it eliminates an iff"
    );
}

#[test]
fn nnf_then_flatten_splits_iff_into_two_or_clauses() {
    // The tactic runs NNF then FlattenAnd; confirm the sequence on a bool `=`
    // produces two `or` clauses (like z3's split goal), each in NNF.
    let mut t = TermStore::new();
    let a = bvar(&mut t, "a");
    let b = bvar(&mut t, "b");
    let iff = t.mk_app(Symbol::named("="), vec![a, b], Sort::Bool);
    let mut goal = vec![iff];
    Nnf::new().apply(&mut t, &mut goal);
    FlattenAnd::new().apply(&mut t, &mut goal);
    assert_eq!(goal.len(), 2, "iff splits into two clauses after flatten");
    for &g in &goal {
        assert!(is_nnf(&t, g), "each split clause must be NNF");
        assert!(matches!(t.get(g), TermData::App(s, _) if s.name() == "or"));
    }
}
