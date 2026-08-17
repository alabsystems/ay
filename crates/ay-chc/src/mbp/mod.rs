// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-Based Projection (MBP) for quantifier elimination
//!
//! This module implements model-based projection, an efficient technique for
//! quantifier elimination guided by a satisfying model. MBP is used in PDR/IC3
//! to compute more general predecessor states.
//!
//! Based on Golem's implementation (MIT license) and the paper:
//! Bjorner & Janota, "Playing with Quantified Satisfaction", LPAR-20, 2015
//!
//! ## Module structure
//!
//! - `eval`: Tri-valued boolean and arithmetic expression evaluation
//! - `eval_bv`: Bitvector expression evaluation under partial models
//! - `implicant`: Implicant extraction from formulas under partial models
//! - `project`: Core projection orchestration (project, project_with_residuals)
//! - `theory`: Theory-specific variable elimination (LIA and LRA)
//! - `theory_bounds`: Arithmetic bound extraction and linear coefficient normalization
//! - `theory_bv`: BV-specific variable projection (Fourier-Motzkin analogue for bitvectors)
//! - `mbqi`: MBQI-style term substitution for unprojectable variables

// Note: Some methods have &self only for method-call syntax consistency.
// Per-function #[allow(clippy::only_used_in_recursion)] is used where needed.

mod array;
mod datatype;
mod eval;
mod eval_bv;
mod implicant;
mod mbqi;
mod project;
mod project_residuals;
mod theory;
mod theory_bounds;
mod theory_bv;

#[cfg(test)]
mod tests;

use crate::{ChcExpr, ChcVar};

/// A literal in an implicant: (atom, polarity)
/// If polarity is true, the literal is `atom`; otherwise it's `NOT atom`
#[derive(Debug, Clone)]
pub(crate) struct Literal {
    pub(crate) atom: ChcExpr,
    pub(crate) positive: bool,
}

impl Literal {
    pub(crate) fn new(atom: ChcExpr, positive: bool) -> Self {
        Self { atom, positive }
    }

    /// Convert back to a ChcExpr
    pub(crate) fn to_expr(&self) -> ChcExpr {
        if self.positive {
            self.atom.clone()
        } else {
            ChcExpr::not(self.atom.clone())
        }
    }
}

/// Result of MBP projection with residual variable tracking.
///
/// When `force=false`, MBP may not eliminate all variables. This struct
/// returns both the projected formula and any remaining variables that
/// could not be eliminated. The caller can then skolemize or otherwise
/// handle the residuals.
///
/// Matches Z3 Spacer's two-mode MBP: `qe_project(vars, fml, mdl, ..., dont_sub)`.
/// See `reference/z3/src/muz/spacer/spacer_context.cpp:1338-1342`.
pub struct MbpResult {
    /// The projected formula (may still contain residual_vars if force=false)
    pub formula: ChcExpr,
    /// Variables that could not be eliminated by MBP
    pub residual_vars: Vec<ChcVar>,
}

/// MBP projection behavior mode.
///
/// This mirrors Spacer's `force` flag plumbing into `qe_project(..., dont_sub=!force)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MbpMode {
    /// Force full elimination by substituting any remaining vars.
    /// Equivalent to Spacer `force=true` / `dont_sub=false`.
    #[cfg(test)]
    ForceSubstitute,
    /// Allow partially projected formulas and report remaining vars.
    /// Equivalent to Spacer `force=false` / `dont_sub=true`.
    AllowResidual,
}

/// Model-Based Projection engine
pub struct Mbp;

impl Default for Mbp {
    fn default() -> Self {
        Self::new()
    }
}

impl Mbp {
    pub fn new() -> Self {
        Self
    }

    /// Project using explicit Spacer-style MBP mode semantics.
    ///
    /// `ForceSubstitute` guarantees no eliminated vars remain by substituting
    /// leftovers. `AllowResidual` returns the partially projected formula and
    /// the residual variables for caller-side skolemization/substitution.
    pub fn project_with_mode(
        &self,
        formula: &ChcExpr,
        vars_to_eliminate: &[ChcVar],
        model: &ay_core::kani_compat::DetHashMap<String, crate::SmtValue>,
        mode: MbpMode,
    ) -> MbpResult {
        match mode {
            #[cfg(test)]
            MbpMode::ForceSubstitute => MbpResult {
                formula: self.project(formula, vars_to_eliminate, model),
                residual_vars: vec![],
            },
            MbpMode::AllowResidual => {
                self.project_with_residuals(formula, vars_to_eliminate, model)
            }
        }
    }

    /// Return an implicant cube for `formula` under `model` without eliminating variables.
    ///
    /// This is useful when MBP has no auxiliary variables to project out: the implicant
    /// preserves inequalities (e.g., `(< x 1)`) instead of defaulting to point assignments.
    ///
    /// REQUIRES: `model` satisfies `formula` (evaluating `formula` under `model` yields true).
    ///
    /// ENSURES: The returned formula `cube` satisfies:
    ///   - `model |= cube` (the model satisfies the result)
    ///   - `cube` logically implies `formula` (the cube is an implicant)
    ///   - `cube` is a conjunction of literals (cube form)
    pub fn implicant_cube(
        &self,
        formula: &ChcExpr,
        model: &ay_core::kani_compat::DetHashMap<String, crate::SmtValue>,
    ) -> ChcExpr {
        let implicant = self.get_implicant(formula, model);
        self.implicant_to_formula(&implicant)
    }

    /// Project away all variables except those in `keep_vars`.
    ///
    /// This is the complement of `project()`:
    /// - `project(vars_to_eliminate)`: eliminates specified vars
    /// - `keep_only(vars_to_keep)`: eliminates ALL vars except specified
    ///
    /// Equivalent to: `project(&all_vars.difference(keep_vars))`
    ///
    /// REQUIRES: `model` satisfies `formula`
    /// ENSURES: Result contains only variables from `keep_vars`
    pub fn keep_only(
        &self,
        formula: &ChcExpr,
        keep_vars: &[ChcVar],
        model: &ay_core::kani_compat::DetHashMap<String, crate::SmtValue>,
    ) -> ChcExpr {
        // Collect all variables in formula
        let all_vars = formula.vars();
        let keep_set: ay_core::kani_compat::DetHashSet<_> = keep_vars.iter().cloned().collect();

        // Compute vars to eliminate: all_vars - keep_vars
        let vars_to_eliminate: Vec<ChcVar> = all_vars
            .into_iter()
            .filter(|v| !keep_set.contains(v))
            .collect();

        self.project(formula, &vars_to_eliminate, model)
    }

    /// Convert implicant back to a formula
    pub(crate) fn implicant_to_formula(&self, implicant: &[Literal]) -> ChcExpr {
        if implicant.is_empty() {
            return ChcExpr::Bool(true);
        }
        if implicant.len() == 1 {
            return implicant[0].to_expr();
        }
        // Use and_all for flat conjunction instead of right-skewed binary
        // chaining that creates deep trees (#2508).
        ChcExpr::and_all(implicant.iter().map(Literal::to_expr))
    }
}

/// Classification of bounds for variable elimination
#[derive(Debug)]
pub(super) enum BoundKind {
    /// Lower bound: coeff * var >= term (strict if bool is true)
    Lower(i128, ChcExpr, bool),
    /// Upper bound: coeff * var <= term (strict if bool is true)
    Upper(i128, ChcExpr, bool),
    /// Equality: coeff * var = term
    Equality(i128, ChcExpr),
}
