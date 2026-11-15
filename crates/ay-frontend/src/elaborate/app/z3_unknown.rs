// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Builtin operators this frontend elaborates that z3 4.12.5 does not know.
//!
//! z3 reads an application of an unknown name as an error ("unknown constant
//! min (Int Int)") after its arguments, and drops the command. Under
//! `--z3-mode` this frontend does the same, unless the script declared or
//! defined the name itself (`elaborate_app` resolves those first). Outside it
//! the operator keeps its meaning here, and an authored assertion's labels
//! after it are not taken to be z3's.

use ay_core::TermId;

use super::{Context, ElaborateError, Result};

/// Operator families this frontend adds: no `set.`, `multiset.` or `map.`
/// name is known to z3 4.12.5.
const UNKNOWN_PREFIXES: &[&str] = &["set.", "multiset.", "map."];

/// Single operators z3 4.12.5 does not know. `ubv_to_int`, `sbv_to_int` and
/// `divisible` are handled where they are elaborated.
const UNKNOWN_NAMES: &[&str] = &[
    "min",
    "max",
    "**",
    "seq.in_re",
    "seq.to_re",
    "seq.replace_all",
    "str.to_lower",
    "str.to_upper",
];

fn z3_does_not_know(name: &str) -> bool {
    UNKNOWN_NAMES.contains(&name)
        || UNKNOWN_PREFIXES
            .iter()
            .any(|prefix| name.starts_with(prefix))
}

impl Context {
    /// Reject, under `--z3-mode`, a builtin operator z3 does not know, with
    /// z3's message; outside it, note it for the labels after it.
    pub(super) fn check_builtin_z3_knows(&mut self, name: &str, args: &[TermId]) -> Result<()> {
        if !z3_does_not_know(name) {
            return Ok(());
        }
        if !self.z3_mode {
            self.note_construct_z3_may_reject();
            return Ok(());
        }
        let sorts: Vec<String> = args
            .iter()
            .map(|&arg| self.terms.sort(arg).to_string())
            .collect();
        Err(ElaborateError::IllSorted(format!(
            "unknown constant {name} ({}) ",
            sorts.join(" ")
        )))
    }
}
