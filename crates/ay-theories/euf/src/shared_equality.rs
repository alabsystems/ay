// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Authentication helpers for shared equalities.

use ay_core::term::{TermData, TermId};
use ay_core::{TermStore, TheoryLit};

/// Detect a shared equality justified only by its own true SAT atom.
///
/// Such an edge would reconstruct a tautological proof reason. The direct SAT
/// assignment already queues the same merge with a non-tautological reason, so
/// dropping this redundant shared edge preserves completeness.
pub(crate) fn reason_is_self_evidencing_shared_eq(
    terms: &TermStore,
    lhs: TermId,
    rhs: TermId,
    reason: &[TheoryLit],
) -> bool {
    let [lit] = reason else {
        return false;
    };
    if !lit.value {
        return false;
    }
    match terms.get(lit.term) {
        TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
            (args[0] == lhs && args[1] == rhs) || (args[0] == rhs && args[1] == lhs)
        }
        _ => false,
    }
}
