// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Combined theory solvers for Nelson-Oppen theory combination.
//!
//! Production dispatch uses `TheoryCombiner` (generic N-O combiner) for:
//! - QF_AX (EUF + Arrays)
//! - QF_UFLIA (EUF + LIA)
//! - QF_UFLRA (EUF + LRA)
//! - QF_AUFLIA (EUF + Arrays + LIA)
//! - QF_AUFLRA (EUF + Arrays + LRA)
//!
//! Remaining bespoke adapters handle logics not yet covered by the combiner:
//! - UfNiaSolver: EUF + NIA (#4525, AUFNIRA support)
//! - UfNraSolver: EUF + NRA
//! - LiraSolver: LIA + LRA (mixed integer/real)
//! - StringsLiaSolver: Strings + EUF + LIA
//! - AufLiraSolver: Arrays + EUF + LIA + LRA

/// Generates the mechanical `propagate()` delegation that collects theory
/// propagations from each sub-solver field.
macro_rules! delegate_propagate {
    ($first:ident $(, $rest:ident)*) => {
        fn propagate(&mut self) -> Vec<ay_core::TheoryPropagation> {
            let mut props = self.$first.propagate();
            $(props.extend(self.$rest.propagate());)*
            props
        }
        fn has_pending_propagations(&self) -> bool {
            self.$first.has_pending_propagations()
            $(|| self.$rest.has_pending_propagations())*
        }
        fn has_pending_analysis(&self) -> bool {
            self.$first.has_pending_analysis()
            $(|| self.$rest.has_pending_analysis())*
        }
        fn drain_pending_propagations(&mut self) -> Vec<ay_core::TheoryPropagation> {
            let mut props = self.$first.drain_pending_propagations();
            $(props.extend(self.$rest.drain_pending_propagations());)*
            props
        }
    };
}

/// Generates mechanical `push()`, `pop()`, `reset()`, `soft_reset()` delegation to sub-solver fields.
/// Includes always-on scope depth tracking via `self.scope_depth` (#4995).
/// The using struct must have a `scope_depth: usize` field.
macro_rules! delegate_scope_ops {
    ($solver_name:literal, $($field:ident),+ $(,)?) => {
        fn push(&mut self) {
            self.scope_depth += 1;
            $(self.$field.push();)+
        }
        fn pop(&mut self) {
            if self.scope_depth == 0 {
                return;
            }
            self.scope_depth -= 1;
            $(self.$field.pop();)+
        }
        fn reset(&mut self) {
            assert!(
                self.scope_depth == 0,
                concat!("BUG: ", $solver_name, "::reset() called with non-zero scope depth {} (unbalanced push/pop)"),
                self.scope_depth,
            );
            $(self.$field.reset();)+
        }
        fn soft_reset(&mut self) {
            assert!(
                self.scope_depth == 0,
                concat!("BUG: ", $solver_name, "::soft_reset() called with non-zero scope depth {} (unbalanced push/pop)"),
                self.scope_depth,
            );
            $(self.$field.soft_reset();)+
        }
    };
}

pub(crate) mod adapters;
mod check_loops;
pub(crate) mod combiner;
mod combiner_check;
mod combiner_models;
mod combiner_uf_congruence;
mod euf_array_replay;
mod interface_bridge;
mod interface_bridge_eval;
mod models;
pub(crate) mod theory_stats;

pub(crate) use adapters::{
    AufLiraSolver, LiraSolver, StringsLiaSolver, UfMapLiaSolver, UfMultisetLiaSolver, UfNiaSolver,
    UfNraSolver, UfSeqLiaSolver, UfSeqSolver, UfSetLiaSolver,
};
pub use combiner::TheoryCombiner;

#[cfg(test)]
mod interface_bridge_tests;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_combiner;
#[cfg(test)]
mod tests_soft_reset;
