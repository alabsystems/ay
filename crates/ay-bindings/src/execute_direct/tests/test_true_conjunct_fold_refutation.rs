// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Constant-`true` conjuncts nested under `and` / `or` / `not`, through the
//! native lane `trust-router::in_process_ay_backend` reads.
//!
//! Measured 2026-10-06 through Trust's in-process backend: over Int `a`, `b`,
//! the violation `Or([And([a<=b, And([true, Not(a<=b)])])])` — plainly UNSAT —
//! came back `unknown (incomplete self-check-rejected)`, while
//! `Or([And([a<=b, Not(a<=b)])])` and the conjunction-spine-flattened
//! `And([a<=b, And([true, Not(a<=b)])])` were both proved. `or_many` of one
//! operand IS that operand, so the failing program asserts
//! `(and (<= a b) (and true (not (<= a b))))`.
//!
//! The elaborator folds that root to `false` with no recorded derivation, and
//! the strict proof rests on the fold-to-`false` rescues. The complement
//! rescue found its argument and then refused its own candidate at the
//! "prints as authored" gate, because a descendant printer override recorded
//! the authored spelling `(and true (not (<= a b)))` against the term
//! `(not (<= a b))` that it FOLDED onto — so every occurrence of that term,
//! including the one inside the spelling, re-printed as the conjunction. The
//! erasure then left a bare `hole`, and mandatory strict certification
//! withheld a correct `unsat`.
//!
//! Every UNSAT row here must be `Verified` with a strict-`Verified` proof
//! artifact — the exact condition the trust backend maps to `Proved` — and
//! every SAT control must stay `sat`, so a green row cannot be explained by a
//! rescue that refutes everything it is shown.

use super::*;
use crate::constraint::Constraint;
use ay_dpll::api::StrictProofVerdict;

/// A QF_LIA program over Int `a`, `b` with proofs on, asserting `build(le)`
/// where `le` is `(<= a b)` — the shape `build_program` emits.
fn solve(build: impl Fn(&Expr) -> Expr) -> ExecuteTypedDetails {
    let mut program = AYProgram::new();
    program.add_constraint(Constraint::set_option(":produce-proofs", "true"));
    program.set_logic("QF_LIA");
    let a = program.declare_const("a", Sort::int());
    let b = program.declare_const("b", Sort::int());
    let le = a.int_le(b);
    program.assert(build(&le));
    program.check_sat();
    execute_typed_with_details(&program).expect("program must execute")
}

fn assert_strictly_proved(label: &str, details: &ExecuteTypedDetails) {
    assert!(
        matches!(details.result, ExecuteTypedResult::Verified),
        "{label}: UNSAT must be published, got {:?}",
        details.result
    );
    let proof = details
        .unsat_proof
        .as_ref()
        .unwrap_or_else(|| panic!("{label}: UNSAT with produce-proofs must carry a proof"));
    assert!(
        matches!(&proof.strict_verdict, StrictProofVerdict::Verified(_)),
        "{label}: the proof must be strictly verified, got {:?}",
        proof.strict_verdict
    );
}

fn t() -> Expr {
    Expr::bool_const(true)
}

fn f() -> Expr {
    Expr::bool_const(false)
}

#[test]
fn true_conjunct_under_a_unary_or_is_strictly_refuted() {
    // The measured Trust row: Or([And([l, And([true, ¬l])])]).
    let details = solve(|l| {
        Expr::or_many(vec![Expr::and_many(vec![
            l.clone(),
            Expr::and_many(vec![t(), l.clone().not()]),
        ])])
    });
    assert_strictly_proved("or(and(l, and(true, ¬l)))", &details);
}

#[test]
fn true_conjuncts_at_every_and_depth_are_strictly_refuted() {
    let rows: Vec<(&str, Box<dyn Fn(&Expr) -> Expr>)> = vec![
        (
            "and(l, true, ¬l)",
            Box::new(|l: &Expr| Expr::and_many(vec![l.clone(), t(), l.clone().not()])),
        ),
        (
            "and(and(true, l), and(true, and(true, ¬l)))",
            Box::new(|l: &Expr| {
                Expr::and_many(vec![
                    Expr::and_many(vec![t(), l.clone()]),
                    Expr::and_many(vec![t(), Expr::and_many(vec![t(), l.clone().not()])]),
                ])
            }),
        ),
        (
            "and(l, and(true, and(true, and(true, ¬l))))",
            Box::new(|l: &Expr| {
                Expr::and_many(vec![
                    l.clone(),
                    Expr::and_many(vec![
                        t(),
                        Expr::and_many(vec![t(), Expr::and_many(vec![t(), l.clone().not()])]),
                    ]),
                ])
            }),
        ),
    ];
    for (label, build) in rows {
        assert_strictly_proved(label, &solve(build));
    }
}

#[test]
fn true_conjuncts_under_or_and_not_are_strictly_refuted() {
    let rows: Vec<(&str, Box<dyn Fn(&Expr) -> Expr>)> = vec![
        (
            "or(and(l, and(true, ¬l)), false)",
            Box::new(|l: &Expr| {
                Expr::or_many(vec![
                    Expr::and_many(vec![l.clone(), Expr::and_many(vec![t(), l.clone().not()])]),
                    f(),
                ])
            }),
        ),
        (
            "or(and(true, l, ¬l), and(¬l, and(true, l)))",
            Box::new(|l: &Expr| {
                Expr::or_many(vec![
                    Expr::and_many(vec![t(), l.clone(), l.clone().not()]),
                    Expr::and_many(vec![l.clone().not(), Expr::and_many(vec![t(), l.clone()])]),
                ])
            }),
        ),
        (
            "¬or(¬l, and(true, l))",
            Box::new(|l: &Expr| {
                Expr::or_many(vec![l.clone().not(), Expr::and_many(vec![t(), l.clone()])]).not()
            }),
        ),
        (
            "and(l, or(and(true, ¬l), false))",
            Box::new(|l: &Expr| {
                Expr::and_many(vec![
                    l.clone(),
                    Expr::or_many(vec![Expr::and_many(vec![t(), l.clone().not()]), f()]),
                ])
            }),
        ),
    ];
    for (label, build) in rows {
        assert_strictly_proved(label, &solve(build));
    }
}

#[test]
fn satisfiable_true_conjunct_shapes_stay_sat() {
    // Each control is one literal away from a refuted row above. A rescue
    // that refuted every fold-shaped root would turn these UNSAT.
    let rows: Vec<(&str, Box<dyn Fn(&Expr) -> Expr>)> = vec![
        (
            "or(and(l, and(true, l)))",
            Box::new(|l: &Expr| {
                Expr::or_many(vec![Expr::and_many(vec![
                    l.clone(),
                    Expr::and_many(vec![t(), l.clone()]),
                ])])
            }),
        ),
        (
            "or(and(l, and(true, ¬l)), and(true, l))",
            Box::new(|l: &Expr| {
                Expr::or_many(vec![
                    Expr::and_many(vec![l.clone(), Expr::and_many(vec![t(), l.clone().not()])]),
                    Expr::and_many(vec![t(), l.clone()]),
                ])
            }),
        ),
        (
            "¬or(¬l, and(true, ¬l))",
            Box::new(|l: &Expr| {
                Expr::or_many(vec![
                    l.clone().not(),
                    Expr::and_many(vec![t(), l.clone().not()]),
                ])
                .not()
            }),
        ),
    ];
    for (label, build) in rows {
        let details = solve(build);
        assert!(
            matches!(details.result, ExecuteTypedResult::Counterexample(_)),
            "{label}: satisfiable, must be sat, got {:?}",
            details.result
        );
    }
}
