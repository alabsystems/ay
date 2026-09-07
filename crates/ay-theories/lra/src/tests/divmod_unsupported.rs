// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Both sides of the residual `div`/`mod` abstraction rule in
//! [`LraSolver::parse_linear_expr`].
//!
//! LRA cannot interpret integer `div`/`mod`; it abstracts the application as a
//! fresh tableau variable, which is a sound OVER-approximation. Whether that
//! abstraction may be reported as `Sat` depends entirely on who consumes the
//! answer:
//!
//! * **standalone** (`combined_theory_mode == false`) — the caller takes LRA's
//!   `Sat` as evidence and nothing downstream re-interprets the term, so the
//!   atom stays marked unsupported and `check()` fails closed to `Unknown`;
//! * **combined** — LRA is one DPLL(T) callback inside a lane whose every
//!   published `sat` must pass the mandatory independent model gate, which
//!   evaluates `div`/`mod` with SMT-LIB Euclidean semantics. Marking there only
//!   deletes verdicts the gate would have confirmed, so the atom is not marked;
//! * **non-binary** `div`/`mod` chains are outside the model evaluator's
//!   two-operand grammar, so they keep the fail-closed marking in both modes.

use super::*;
use num_bigint::BigInt;

/// Standalone LRA keeps the fail-closed marking: nothing else interprets
/// `(div x y)`, so a simplex `Sat` over the abstraction must not be reported.
#[test]
fn standalone_div_atom_still_fails_closed() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let q = terms.mk_intdiv(x, y);
    let four = terms.mk_int(BigInt::from(4));
    let atom = terms.mk_eq(q, four);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(atom, true);
    assert!(
        matches!(solver.check(), TheoryResult::Unknown),
        "standalone LRA must fail closed on an uninterpreted div atom"
    );
}

/// Same for `mod`.
#[test]
fn standalone_mod_atom_still_fails_closed() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let r = terms.mk_mod(x, y);
    let one = terms.mk_int(BigInt::from(1));
    let atom = terms.mk_eq(r, one);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(atom, true);
    assert!(
        matches!(solver.check(), TheoryResult::Unknown),
        "standalone LRA must fail closed on an uninterpreted mod atom"
    );
}

/// In `combined_theory_mode` the binary `div` atom is abstracted without
/// marking, so the simplex `Sat` survives the callback and the DPLL(T) search
/// continues to a candidate model the independent gate can adjudicate.
#[test]
fn combined_binary_div_atom_is_reported_sat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let q = terms.mk_intdiv(x, y);
    let four = terms.mk_int(BigInt::from(4));
    let atom = terms.mk_eq(q, four);

    let mut solver = LraSolver::new(&terms);
    solver.set_combined_theory_mode(true);
    solver.assert_literal(atom, true);
    assert!(
        is_sat_like(&solver.check()),
        "combined-mode LRA must not delete a Sat over an abstracted div atom"
    );
}

/// Same for `mod`.
#[test]
fn combined_binary_mod_atom_is_reported_sat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let r = terms.mk_mod(x, y);
    let one = terms.mk_int(BigInt::from(1));
    let atom = terms.mk_eq(r, one);

    let mut solver = LraSolver::new(&terms);
    solver.set_combined_theory_mode(true);
    solver.assert_literal(atom, true);
    assert!(
        is_sat_like(&solver.check()),
        "combined-mode LRA must not delete a Sat over an abstracted mod atom"
    );
}

/// A non-binary `div` chain is outside the model evaluator's grammar (it
/// requires exactly two operands), so nothing downstream can interpret it and
/// the marking stays even in combined mode.
#[test]
fn combined_nary_div_atom_still_fails_closed() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let chain = terms.mk_app(Symbol::named("div"), vec![x, y, z], Sort::Int);
    let four = terms.mk_int(BigInt::from(4));
    let atom = terms.mk_eq(chain, four);

    let mut solver = LraSolver::new(&terms);
    solver.set_combined_theory_mode(true);
    solver.assert_literal(atom, true);
    assert!(
        matches!(solver.check(), TheoryResult::Unknown),
        "an n-ary div chain has no downstream interpreter and must fail closed"
    );
}

/// The downgrade is counted, so the population can be measured from a release
/// build instead of a `--verbose` log scrape.
#[test]
fn unsupported_sat_downgrade_is_counted() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let q = terms.mk_intdiv(x, y);
    let four = terms.mk_int(BigInt::from(4));
    let atom = terms.mk_eq(q, four);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(atom, true);
    assert!(matches!(solver.check(), TheoryResult::Unknown));
    assert_eq!(
        TheorySolver::collect_statistics(&solver)
            .into_iter()
            .find(|(name, _)| *name == "lra_unsupported_sat_downgrades")
            .map(|(_, v)| v),
        Some(1),
        "the Sat->Unknown downgrade must be visible as a statistic"
    );
}
