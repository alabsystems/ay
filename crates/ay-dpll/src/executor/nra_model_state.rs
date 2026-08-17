// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact NRA algebraic witnesses and their model-print refinement state.

use std::ops::{Deref, DerefMut};

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::TermId;
use ay_nra::RealAlgebraicValue;

use super::Executor;

/// Exact algebraic witnesses for the current SAT model.
///
/// Evaluation and model rendering consume these values directly. The boolean
/// records the one bounded rational-refinement attempt allowed per stored SAT
/// verdict. Installing or clearing a verdict resets the attempt; temporary
/// snapshot/restore operations deliberately preserve it.
#[derive(Clone, Default)]
pub(super) struct NraAlgebraicModel {
    values: HashMap<TermId, RealAlgebraicValue>,
    print_refinement_attempted: bool,
}

impl NraAlgebraicModel {
    pub(super) fn clear(&mut self) {
        self.values.clear();
        self.print_refinement_attempted = false;
    }

    pub(super) fn set(&mut self, values: &mut Vec<(TermId, RealAlgebraicValue)>) {
        self.values = values.drain(..).collect();
        self.print_refinement_attempted = false;
    }

    pub(super) fn values(&self) -> &HashMap<TermId, RealAlgebraicValue> {
        &self.values
    }

    pub(super) fn take_values(&mut self) -> HashMap<TermId, RealAlgebraicValue> {
        std::mem::take(&mut self.values)
    }

    pub(super) fn replace_values(&mut self, values: HashMap<TermId, RealAlgebraicValue>) {
        self.values = values;
    }

    pub(super) fn print_refinement_attempted(&self) -> bool {
        self.print_refinement_attempted
    }

    pub(super) fn mark_print_refinement_attempted(&mut self) {
        self.print_refinement_attempted = true;
    }

    #[cfg(test)]
    pub(super) fn reset_print_refinement_attempted(&mut self) {
        self.print_refinement_attempted = false;
    }
}

impl Deref for NraAlgebraicModel {
    type Target = HashMap<TermId, RealAlgebraicValue>;

    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

impl DerefMut for NraAlgebraicModel {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.values
    }
}

impl Executor {
    /// Replace snapshot values without changing this verdict's one-shot flag.
    pub(super) fn restore_nra_values(&mut self, values: HashMap<TermId, RealAlgebraicValue>) {
        self.nra_algebraic_model.replace_values(values);
    }
}
