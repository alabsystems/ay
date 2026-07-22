// Copyright 2026 Andrew Yates
// Author: Andrew Yates
//
// Licensed under the Apache License, Version 2.0

//! Denominator simplification for linear arithmetic lemmas.
//!
//! AY's Farkas builder already clears rational denominators to integers, so the
//! remaining win at `HEAD` is to normalize linear inequalities to smaller
//! coefficients (for example `2*x <= 4` to `x <= 2`) before later SMT checks.

use super::{LemmaGeneralizer, TransitionSystemRef};
use crate::{farkas::normalize_linear_inequality_expr, ChcExpr};

/// Normalize linear inequalities to smaller equivalent coefficients.
///
/// This is the closest current-head equivalent to Spacer's `limit_num`
/// generalizer: shrink arithmetic literals only when the rewritten lemma is
/// still inductive at the current level.
pub(crate) struct DenominatorSimplificationGeneralizer;

impl Default for DenominatorSimplificationGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl DenominatorSimplificationGeneralizer {
    /// Create a new denominator simplification generalizer.
    pub(crate) fn new() -> Self {
        Self
    }
}

impl LemmaGeneralizer for DenominatorSimplificationGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let conjuncts = lemma.collect_conjuncts();
        if conjuncts.is_empty() {
            return lemma.clone();
        }

        let mut any_changed = false;
        let rewritten: Vec<ChcExpr> = conjuncts
            .into_iter()
            .map(|conjunct| {
                if let Some(normalized) = normalize_linear_inequality_expr(&conjunct) {
                    any_changed = true;
                    normalized
                } else {
                    conjunct
                }
            })
            .collect();

        if !any_changed {
            return lemma.clone();
        }

        let candidate = ChcExpr::and_all(rewritten);
        if ts.check_inductive(&candidate, level) {
            candidate
        } else {
            lemma.clone()
        }
    }

    fn name(&self) -> &'static str {
        "denominator-simplification"
    }
}
