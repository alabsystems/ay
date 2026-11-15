// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constant-`true` conjuncts nested under `and` / `or` / `not`: a root the
//! elaborator folds to `false` must keep a strictly checked refutation.
//!
//! Measured 2026-10-06 (Trust's in-process lane, then this text lane): every
//! UNSAT row below except the flat `(and l true (not l))` answered
//! `unknown (incomplete self-check-rejected)` under `:produce-proofs`. The
//! elaborator folds `true` conjuncts, `false` disjuncts, unary `or`s and the
//! complement pair down to the constant `false` and keeps no derivation, so
//! the proof rests on the fold-to-`false` rescues; two defects left each row
//! with the bare `hole` and mandatory strict certification withheld the
//! `unsat`:
//!
//! 1. a descendant printer override recorded `(and true (not (<= a b)))`
//!    against the term `(not (<= a b))` it FOLDED onto, re-spelling every
//!    occurrence of it, so the complement rescue's raw root no longer printed
//!    as authored and the rescue refused its own candidate;
//! 2. no rescue derived a fold through `or` / `(not (or ..))` over theory
//!    atoms (the bounded interpreter only closes finite Bool/BV roots).
//!
//! Every SAT control is one literal away from a refuted row, so a rescue that
//! refuted every fold-shaped root would turn it `unsat`.

#![allow(clippy::panic)]

mod common;

const PREFIX: &str = "(set-option :produce-proofs true)\n(set-logic QF_LIA)\n\
    (declare-const a Int)\n(declare-const b Int)\n(declare-const p Bool)\n";

fn script(assertion: &str) -> String {
    format!("{PREFIX}(assert {assertion})\n(check-sat)\n")
}

const UNSAT_ROWS: &[&str] = &[
    // The measured Trust row, and its `or_many`-collapsed native spelling.
    "(or (and (<= a b) (and true (not (<= a b)))))",
    "(and (<= a b) (and true (not (<= a b))))",
    // `true` at every and-depth.
    "(and (<= a b) true (not (<= a b)))",
    "(and (and true (<= a b)) (and true (and true (not (<= a b)))))",
    "(and (<= a b) (and true (and true (and true (not (<= a b))))))",
    // Under `or`: unary, beside `false`, and every disjunct refuted.
    "(or (and (<= a b) (not (<= a b))))",
    "(or (and (<= a b) (and true (not (<= a b)))) false)",
    "(or (and true (<= a b) (not (<= a b))) (and (not (<= a b)) (and true (<= a b))))",
    "(or (and (<= a b) (not (<= a b))) (and p (not p)))",
    // Under `not`.
    "(not (or (not (<= a b)) (and true (<= a b))))",
    "(not (and true (or (<= a b) (not (<= a b)))))",
    "(not (not (and (<= a b) (and true (not (<= a b))))))",
    // `or` under `and`, where the complement crosses the levels.
    "(and (<= a b) (or (and true (not (<= a b)))))",
    "(and (<= a b) (or false (and true (not (<= a b)))))",
];

const SAT_ROWS: &[&str] = &[
    "(or (and (<= a b) (and true (<= a b))))",
    "(or (and (<= a b) (and true (not (<= a b)))) (and true (<= a b)))",
    "(not (or (not (<= a b)) (and true (not (<= a b)))))",
    "(and (<= a b) (or (and true (not (<= a b))) p))",
];

#[test]
fn true_conjunct_folds_keep_a_strictly_checked_unsat() {
    for row in UNSAT_ROWS {
        let default = common::solve_authored_vec(&script(row));
        assert_eq!(
            default,
            ["unsat"],
            "{row}: a correct `unsat` must not be withheld as self-check-rejected"
        );
        let certified = common::solve_authored_selfcheck_vec(&script(row));
        assert_eq!(
            certified,
            ["unsat"],
            "{row}: --self-check must publish the strictly checked refutation"
        );
    }
}

#[test]
fn true_conjunct_fold_proofs_carry_no_hole() {
    for row in UNSAT_ROWS {
        let output = common::solve_authored_vec(&format!("{}(get-proof)\n", script(row)));
        let [verdict, proof] = output.as_slice() else {
            panic!("{row}: expected a verdict and a proof, got {output:?}");
        };
        assert_eq!(verdict, "unsat", "{row}");
        assert!(
            proof.contains("(cl)") && !proof.contains(":rule hole"),
            "{row}: the exported refutation must be complete and hole-free:\n{proof}"
        );
    }
}

#[test]
fn satisfiable_true_conjunct_shapes_stay_sat() {
    for row in SAT_ROWS {
        let default = common::solve_authored_vec(&script(row));
        assert_eq!(default, ["sat"], "{row}: satisfiable, must stay sat");
        let certified = common::solve_authored_selfcheck_vec(&script(row));
        assert!(
            !certified.iter().any(|line| line == "unsat"),
            "{row}: --self-check must never mint a refutation: {certified:?}"
        );
    }
}
