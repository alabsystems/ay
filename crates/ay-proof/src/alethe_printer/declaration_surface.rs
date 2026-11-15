// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The problem side of a certificate's external-recheck surface.

use super::{carcara_sort_gap, carcara_symbol_gap};
use ay_core::Sort;

/// Every word pinned Carcara's lexer reads as structural syntax when it is
/// spelled bare (`carcara/src/parser/lexer.rs`, `Reserved`), in the PROBLEM as
/// well as in the proof.
const CARCARA_RESERVED_WORDS: [&str; 27] = [
    "_",
    "!",
    "as",
    "let",
    "exists",
    "forall",
    "match",
    "choice",
    "lambda",
    "cl",
    "assume",
    "step",
    "anchor",
    "declare-fun",
    "declare-datatype",
    "declare-datatypes",
    "par",
    "declare-const",
    "declare-sort",
    "define-fun",
    "define-fun-rec",
    "define-funs-rec",
    "define-sort",
    "assert",
    "check-sat-assuming",
    "set-logic",
    "declare-rare-rule",
];

/// Why pinned Carcara cannot parse the problem that declares `name` with this
/// signature, if it cannot.
///
/// The certificate an external checker receives is the problem AND the proof,
/// and the checker parses every declaration of the problem whether or not the
/// proof mentions it. [`carcara_proof_surface`] reads only the proof, so a
/// query that declares an unused `(_ FloatingPoint 8 24)` constant, or a
/// constant named `step`, was disclosed `carcara_surface=supported` and
/// published under `--strict-proofs` with a certificate no checker can read.
/// Measured on external-codegen's `FcvtToInt_I32_F32` and `LoopUnroll` obligations:
/// Carcara 9a352ee and Clean 414913cce both stop at the declaration
/// (`sort 'FloatingPoint' is not defined`, `unexpected token: 'step'`).
///
/// A name that is one of Carcara's reserved words is refused whatever its
/// spelling: AY's frontend accepts it bare (`(declare-const step ...)`) and
/// does not retain whether the input quoted it, and only the quoted spelling
/// parses. Undetermined is refused.
#[must_use]
pub fn carcara_declaration_gap(name: &str, arg_sorts: &[Sort], sort: &Sort) -> Option<String> {
    if CARCARA_RESERVED_WORDS.contains(&name) {
        return Some(format!(
            "the problem declares `{name}`, a word pinned Carcara's lexer reserves, so the \
             problem does not parse unless the input quoted it, which AY cannot confirm"
        ));
    }
    carcara_symbol_gap(name)
        .or_else(|| arg_sorts.iter().find_map(carcara_sort_gap))
        .or_else(|| carcara_sort_gap(sort))
        .map(|gap| format!("the problem declares `{name}`: {gap}"))
}
