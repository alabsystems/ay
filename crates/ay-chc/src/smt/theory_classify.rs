// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory atom classification and SAT phase hints.
//!
//! Extracted from check_sat.rs — these methods classify term atoms by
//! theory (BV, array, LIA) and set SAT solver phase hints for splits.

use super::context::SmtContext;
use ay_core::{Sort, TermId, TermStore};

impl SmtContext {
    /// Check if a theory atom involves bitvector operations.
    ///
    /// BV atoms are handled by eager bit-blasting and should NOT be sent to
    /// the LIA theory solver. (#5122)
    pub(crate) fn is_bv_theory_atom(terms: &TermStore, term: TermId) -> bool {
        use ay_core::term::TermData;
        match terms.get(term) {
            TermData::App(sym, args) => {
                let name = sym.name();
                // Explicit BV comparison operators
                if matches!(
                    name,
                    "bvult"
                        | "bvule"
                        | "bvugt"
                        | "bvuge"
                        | "bvslt"
                        | "bvsle"
                        | "bvsgt"
                        | "bvsge"
                        | "bvcomp"
                ) {
                    return true;
                }
                // Equality/distinct with BV-sorted arguments
                if matches!(name, "=" | "distinct") && !args.is_empty() {
                    if matches!(terms.sort(args[0]), Sort::BitVec(_)) {
                        return true;
                    }
                }
                false
            }
            _ => false,
        }
    }

    /// Check if a theory atom involves array operations (#6047).
    ///
    /// Array atoms (select, store, equality over Array sorts) are not handled
    /// by the LIA theory solver. Sending them to LIA marks them as unsupported
    /// via per-atom tracking (#6167), degrading those atoms' Sat to Unknown.
    ///
    /// This filter routes array atoms away from LIA so the arithmetic portion
    /// of the formula can still be solved. Array-containing formulas are
    /// dispatched to ay-dpll's Executor (via executor_adapter) which has full
    /// array theory support. This filter ensures the internal DPLL(T) fallback
    /// path treats array atoms as unconstrained rather than rejecting them.
    ///
    /// Soundness:
    /// - UNSAT from LIA (without array atoms) is sound: LIA over-approximates
    ///   by treating unknown terms as fresh variables.
    /// - SAT from LIA means arithmetic constraints are consistent. Array
    ///   constraints may not hold, but PDR handles this via CEGAR.
    pub(crate) fn is_array_theory_atom(terms: &TermStore, term: TermId) -> bool {
        use ay_core::term::TermData;
        match terms.get(term) {
            TermData::App(sym, args) => {
                let name = sym.name();
                // Direct array operations
                if matches!(name, "select" | "store") {
                    return true;
                }
                // Equality/distinct with Array-sorted arguments
                if matches!(name, "=" | "distinct") && !args.is_empty() {
                    if matches!(terms.sort(args[0]), Sort::Array(_)) {
                        return true;
                    }
                }
                false
            }
            _ => false,
        }
    }
}

#[cfg(test)]
#[path = "theory_classify_tests.rs"]
mod tests;
