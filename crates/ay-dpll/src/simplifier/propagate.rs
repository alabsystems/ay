// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Value propagation over the window's top-level conjuncts (z3's
//! `propagate-values`, `reference/z3/src/ast/simplifiers/propagate_values.cpp`).
//!
//! Flattens top-level conjunctions, then runs the goal-mode
//! [`crate::preprocess::PropagateValues::apply_goal`] the tactic surface
//! already uses: substitutions are harvested from top-level unit facts, never
//! applied under binders, and a conflict collapses the window to `false`.
//! Equivalence-preserving (see that method's soundness contract).

use crate::preprocess::{FlattenAnd, PreprocessingPass, PropagateValues};

use super::{Justification, Pass, PassContext, Preservation};

pub(super) struct Propagate;

impl Pass for Propagate {
    fn name(&self) -> &'static str {
        "propagate-values"
    }

    fn preservation(&self) -> Preservation {
        Preservation::Equivalence
    }

    fn justification(&self) -> Justification {
        Justification::Unjustified
    }

    fn run(&mut self, cx: &mut PassContext<'_, '_>) -> usize {
        // The goal sweeps are linear per round and bounded by
        // `GOAL_MODE_MAX_ROUNDS`; charge the window size once.
        if !cx.budget.charge(cx.window.len() as u64) {
            return 0;
        }
        let before = cx.window.clone();
        FlattenAnd::new().apply(cx.terms, cx.window);
        PropagateValues::new().apply_goal(cx.terms, cx.window);
        FlattenAnd::new().apply(cx.terms, cx.window);
        usize::from(*cx.window != before)
    }
}
