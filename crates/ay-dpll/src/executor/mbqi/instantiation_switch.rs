// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The input's switch for model-based quantifier instantiation.
//!
//! `(set-option :smt.mbqi false)` asks for quantifiers to be instantiated
//! through their triggers only. Program verifiers send it with every query:
//! their axioms carry the patterns that say where each one applies, a goal
//! they cannot prove is expected to end `unknown` as soon as trigger matching
//! stops, and the candidate model of that `unknown` is what they report.
//!
//! The candidate-model refinement is the part of this solver the option
//! names. It evaluates every universal the matcher left open at tuples of
//! ground terms under the ground model and conjoins each instance the model
//! falsifies, whatever the universal's pattern says, then solves again.
//! Measured on such a query (81 patterned axioms, a satisfiable goal): the
//! ground solve ends `sat` on 2,720 theory atoms, the first batch of the
//! refinement makes that 20,928, and the re-solve does not come back; the
//! reference solver, given the same option, answers `unknown` at once.
//!
//! With the option off the refinement ([`Executor::try_mbqi_refinement`])
//! returns before that enumeration. Its callers get `None`, the answer it
//! already gives when no universal is eligible for it, and every one of them
//! fails closed on that: no instance is added, so no refutation comes from
//! here, and no `sat` is claimed on the refinement's word. The certificates
//! that examine the ground model without this refinement still run, behind
//! the gates they always had.
//!
//! The switch stops the enumeration over ground tuples and nothing else. The
//! two lanes the refinement tries first decide a fragment of their own and
//! stay: the bit-vector lane (a problem whose open universals bind
//! bit-vectors only) and the finite-model lane. The reference solver, given
//! the option, still refutes `a >u 5` with `forall x. x <u a` over 32 bits;
//! so does the bit-vector lane, and only it.
//!
//! Only the Boolean `false` switches it off. An absent option, `true`, and a
//! value that is not a Boolean leave the refinement as it was.

use super::*;
use ay_frontend::OptionValue;

/// The option, as the frontend stores it (without the leading colon).
const MODEL_BASED_INSTANTIATION: &str = "smt.mbqi";

/// Statistics key: candidate-model refinements of the last check that did
/// not run because the input switched model-based instantiation off.
/// Statistics only; nothing reads it back.
const REFINEMENTS_SWITCHED_OFF: &str = "quantifier.mbqi.switched_off";

impl Executor {
    /// Whether the input switched model-based quantifier instantiation off.
    pub(in crate::executor) fn model_based_instantiation_is_off(&self) -> bool {
        matches!(
            self.ctx.get_option(MODEL_BASED_INSTANTIATION),
            Some(OptionValue::Bool(false))
        )
    }

    /// Asked by [`Self::try_mbqi_refinement`] when it reaches its generic
    /// candidate path: whether the input keeps that path from running. A
    /// `true` is counted in the statistics of the check.
    pub(super) fn refinement_is_switched_off(&mut self) -> bool {
        if !self.model_based_instantiation_is_off() {
            return false;
        }
        let skipped = self
            .last_statistics
            .get_int(REFINEMENTS_SWITCHED_OFF)
            .unwrap_or(0);
        self.last_statistics
            .set_int(REFINEMENTS_SWITCHED_OFF, skipped + 1);
        true
    }
}

#[cfg(test)]
#[path = "instantiation_switch_tests.rs"]
mod tests;
