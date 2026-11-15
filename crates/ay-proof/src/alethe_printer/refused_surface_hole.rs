// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A surface step no certified bridge spells, declined to the honest `hole`
//! instead of refusing the whole document.
//!
//! The authored spelling can turn a checked internal step into a printed
//! shape pinned Carcara cannot justify — a congruence whose two sides lost
//! the internal operator (`(div -7 2)` beside its value `-4`, `=>` beside its
//! canonical `or`), an `and_pos` over a chained comparison the problem wrote
//! `(< -5 x -3)`. The printer then refuses the step (`InvalidCongruenceStep`,
//! `InvalidSurfaceStep`), and an exporter that refuses refuses the whole
//! document: `--proof FILE` exits with NO verdict for an `unsat` AY derived
//! and checked (#8821). MEASURED 2026-10-02 on main and on the
//! negative-literal branch: seven probe problems (b05, d01, d12, d14, e14,
//! g09 and their kin) z3 answers `unsat` lost their verdict this way.
//!
//! Inside [`with_refused_surface_steps_declined_to_hole`] such a step prints
//! as `(step id CLAUSE :rule hole)` over its own printed clause, exactly the
//! decline the byte judges (`judge_printed_la_generic`,
//! `judge_printed_simplify`) already make: every later step cites the same
//! conclusion, the document is honestly holey (the CLI counts the hole in
//! `unproved_steps` and `--rigor strict` withholds the verdict), and nothing
//! else changes. Outside the scope the refusal stands, so a caller that
//! retries a refused export another way (the API's canonical rescue) and a
//! producer that asks whether a fragment renders
//! (`congruence_derivation_renders`) see exactly what they saw before. An
//! `assume` has no hole and still refuses.

use super::*;
use std::cell::Cell;

thread_local! {
    static DECLINE_TO_HOLE: Cell<bool> = const { Cell::new(false) };
}

/// Run `render` with refused surface steps declined to `hole` on this thread
/// (see the module docs), restoring the previous setting afterwards, also
/// when `render` unwinds.
pub fn with_refused_surface_steps_declined_to_hole<R>(render: impl FnOnce() -> R) -> R {
    struct Restore(bool);
    impl Drop for Restore {
        fn drop(&mut self) {
            DECLINE_TO_HOLE.with(|selected| selected.set(self.0));
        }
    }
    let _restore = Restore(DECLINE_TO_HOLE.with(|selected| selected.replace(true)));
    render()
}

impl AlethePrinter<'_> {
    /// The honest `hole` for a step whose rendering `error` refused, when the
    /// scope asks for it, the refusal is a surface-spelling one, and the step
    /// has a clause to conclude; `None` keeps the refusal.
    pub(super) fn refused_surface_step_hole(
        &self,
        step: &ProofStep,
        id: ProofId,
        error: &AlethePrintError,
    ) -> Option<String> {
        if !DECLINE_TO_HOLE.with(Cell::get) {
            return None;
        }
        if !matches!(
            error,
            AlethePrintError::InvalidCongruenceStep { .. }
                | AlethePrintError::InvalidSurfaceStep { .. }
        ) {
            return None;
        }
        let clause = match step {
            ProofStep::Resolution { clause, .. }
            | ProofStep::TheoryLemma { clause, .. }
            | ProofStep::FiniteFieldLinear { clause, .. }
            | ProofStep::NraSos { clause, .. }
            | ProofStep::Step { clause, .. } => clause,
            _ => return None,
        };
        Some(format!(
            "(step {id} {} :rule {})",
            self.format_clause(clause),
            ay_core::UNPROVED_STEP_RULE
        ))
    }
}

#[cfg(test)]
#[path = "refused_surface_hole_tests.rs"]
mod tests;
