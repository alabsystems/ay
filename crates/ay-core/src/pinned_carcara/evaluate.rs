// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A Carcara verdict that rests on an `evaluate` step pinned Carcara computes
//! wrongly is not evidence.
//!
//! Pinned carcara 1.1.0 (git 9a352ee) checks `(step _ (cl (= t v)) :rule
//! evaluate)` by computing `t` itself (`carcara/src/ast/evaluate.rs`, the only
//! caller being the `evaluate` rule), and it computes some bit-vector
//! operators WRONGLY:
//!
//! * `Value::as_signed_bitvec` returns `2^w - v` (the magnitude) for a
//!   negative operand instead of `v - 2^w`. Every signed operation reads its
//!   operands through it (`bvslt`/`bvsle`/`bvsgt`/`bvsge`, `bvsdiv`, `bvsrem`,
//!   `bvsmod`, `sign_extend`, `sbv_to_int`), and so does `bvsub`.
//! * `(_ extract i j)` keeps `keep_bits(i)`, the bits BELOW `i`, so it drops
//!   bit `i` itself.
//! * `(_ rotate_left i)` rotates right by `w - i` computed in `usize`, which
//!   wraps for `i > w`: the result is wrong unless `w` is a power of two.
//! * `div` and `mod` use rug's truncating `/` and `%`, not SMT-LIB's
//!   Euclidean division, so both are wrong for a negative dividend.
//!
//! Measured 2026-09-24 with that checker: it prints `valid` for an `evaluate`
//! refutation of the SATISFIABLE `(assert (bvsge #xf #xe))` (-1 >= -2; z3
//! `sat`), and for the refutations of `(not (= (bvsub #xff #xfb) #xfc))` and
//! `(not (= ((_ extract 3 3) #x8) #b0))`, both of which z3 answers `sat`
//! (the equalities are false). On such a step Carcara's verdict is not
//! evidence in either direction, so no gate may count the document as checked.
//! The printer never emits one on purpose (the eq_transitive closed-spelling
//! bridge evaluates only `concat`, `bvadd`, `bvmul`, the bitwise operators,
//! `bvneg` and `zero_extend`); this is the gate-side twin that catches any
//! producer that does.

use super::lexer::{alethe_commands, command_atoms, record_names_applying, step_rule_of};
use std::collections::BTreeSet;

/// The operators pinned Carcara's `evaluate` misjudges (see above).
pub const EVALUATE_OPERATORS_PINNED_CARCARA_MISJUDGES: &[&str] = &[
    "bvsub",
    "bvsdiv",
    "bvsrem",
    "bvsmod",
    "bvslt",
    "bvsle",
    "bvsgt",
    "bvsge",
    "sign_extend",
    "sbv_to_int",
    "extract",
    "rotate_left",
    "div",
    "mod",
];

/// The `evaluate` steps of `proof` that apply one of
/// [`EVALUATE_OPERATORS_PINNED_CARCARA_MISJUDGES`], directly or through a
/// name Carcara expands before any rule runs: a proof-local `define-fun`, or
/// a `:named` label of the problem or the proof. (A problem's `define-fun`,
/// which pinned Carcara does not expand, is recorded too: that can only flag
/// more.)
pub fn evaluate_steps_pinned_carcara_misjudges<'a>(
    problem: &'a str,
    proof: &'a str,
) -> Vec<&'a str> {
    let mut misjudged_names = BTreeSet::new();
    for command in alethe_commands(problem) {
        record_misjudged_names(&command_atoms(command), &mut misjudged_names);
    }
    alethe_commands(proof)
        .into_iter()
        .filter(|command| {
            let atoms = command_atoms(command);
            record_misjudged_names(&atoms, &mut misjudged_names)
                && step_rule_of(&atoms) == Some("evaluate")
        })
        .collect()
}

/// Whether one command applies a misjudged operator or name, recording the
/// names it introduces as misjudged when it does.
fn record_misjudged_names<'a>(atoms: &[(usize, &'a str)], names: &mut BTreeSet<&'a str>) -> bool {
    record_names_applying(atoms, EVALUATE_OPERATORS_PINNED_CARCARA_MISJUDGES, names)
}
