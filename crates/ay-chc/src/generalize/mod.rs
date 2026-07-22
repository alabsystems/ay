// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lemma generalization framework for CHC solving.
//!
//! Trait-based framework for lemma generalization, transforming lemmas into
//! weaker forms while maintaining inductiveness.
//!
//! Based on Z3 Spacer's architecture from `spacer_generalizers.cpp`.
//! See the development design notes for full design.
//!
//! References:
//! - Z3 Spacer: `reference/z3/src/muz/spacer/spacer_generalizers.cpp`
//! - Issue #160

use crate::expr::ChcExpr;
use ay_core::kani_compat::DetHashMap as HashMap;

/// Bounds on initial values for a variable.
///
/// Represents the range `[min, max]` of values a variable can take in the
/// initial state. Used by init-bound-aware generalizers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct InitBounds {
    /// Minimum value in initial state
    pub(crate) min: i64,
    /// Maximum value in initial state
    pub(crate) max: i64,
}

impl InitBounds {
    /// Create bounds for a range.
    pub(crate) fn range(min: i64, max: i64) -> Self {
        Self { min, max }
    }

    /// Check if this represents an exact value (min == max).
    pub(crate) fn is_exact(&self) -> bool {
        self.min == self.max
    }
}

#[cfg(test)]
impl InitBounds {
    /// Create bounds for a single value.
    pub(crate) fn exact(val: i64) -> Self {
        Self { min: val, max: val }
    }

    /// Create unbounded (for variables with no init constraints).
    pub(crate) fn unbounded() -> Self {
        Self {
            min: i64::MIN,
            max: i64::MAX,
        }
    }

    /// Check if a value is within these bounds.
    pub(crate) fn contains(&self, val: i64) -> bool {
        val >= self.min && val <= self.max
    }
}

/// Transition system interface for generalization.
///
/// This abstracts the transition system to allow generalizers to work with
/// both PDR and PDKIND's different internal representations.
///
/// # Mutability
///
/// Methods take `&mut self` because inductiveness checks typically require
/// mutable access to an SMT solver. Implementors should manage their own
/// SMT context internally.
pub(crate) trait TransitionSystemRef {
    /// Check if a formula is k-inductive (relative to frames at level k).
    /// Returns true if the formula is inductive.
    fn check_inductive(&mut self, formula: &ChcExpr, level: u32) -> bool;

    /// Check inductiveness and return the minimal subset of conjuncts needed.
    ///
    /// When the inductiveness check succeeds (UNSAT), this returns the subset
    /// of the input `conjuncts` that were sufficient to prove unsatisfiability.
    /// This enables unsat-core-based generalization.
    ///
    /// # Arguments
    /// * `conjuncts` - The positive conjuncts forming the lemma (e.g., `[x > 0, y < 10]`)
    /// * `level` - Frame level for inductiveness check
    ///
    /// # Returns
    /// * `Some(subset)` - A subset of `conjuncts` sufficient for inductiveness
    /// * `None` - If the check was SAT, unknown, or core extraction failed
    ///
    /// The returned subset contains elements from the input `conjuncts` array.
    /// Implementors should map the internal unsat core back to the original
    /// conjuncts before returning.
    fn check_inductive_with_core(
        &mut self,
        conjuncts: &[ChcExpr],
        level: u32,
    ) -> Option<Vec<ChcExpr>>;

    /// Get initial value bounds for variables.
    ///
    /// Returns a mapping from variable names to their initial value bounds.
    /// This is used by init-bound-aware generalizers to weaken constraints
    /// based on what values are possible in the initial state.
    ///
    /// The default implementation returns an empty map (no bounds information).
    fn init_bounds(&self) -> HashMap<String, InitBounds> {
        HashMap::default()
    }
}

/// A lemma generalizer transforms a lemma into a more general (weaker) form
/// while maintaining inductiveness.
///
/// Generalizers are composable via [`GeneralizerPipeline`].
///
/// # Contracts for Implementors
///
/// REQUIRES: `lemma` is a well-formed CHC expression representing a state formula.
///
/// REQUIRES: `level` is a valid frame level (typically 0 ≤ level ≤ current PDR depth).
///
/// ENSURES: The returned formula `G` satisfies:
///          1. `G` implies `lemma` (G is stronger or equal to input)
///          2. If `ts.check_inductive(&lemma, level)` was true before the call,
///             then `ts.check_inductive(&G, level)` is also true after the call
///          3. vars(G) ⊆ vars(lemma) (no new variables introduced)
///
/// ENSURES: If no generalization is possible, returns `lemma` unchanged.
///
/// INVARIANT: Generalization is monotonic - repeated calls converge to a fixpoint.
pub(crate) trait LemmaGeneralizer: Send + Sync {
    /// Generalize the given lemma at the specified frame level.
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr;

    /// Name for debugging/statistics (verified in tests across 13 impls).
    #[allow(dead_code)] // Used by tests only; retained as part of the trait contract.
    fn name(&self) -> &str;
}

/// A pipeline of generalizers that run in sequence.
///
/// The pipeline runs all generalizers in order until no changes are made
/// (fixpoint). This allows generalizers to build on each other's results.
pub(crate) struct GeneralizerPipeline {
    generalizers: Vec<Box<dyn LemmaGeneralizer>>,
}

impl Default for GeneralizerPipeline {
    fn default() -> Self {
        Self::new()
    }
}

impl GeneralizerPipeline {
    /// Create an empty pipeline.
    pub(crate) fn new() -> Self {
        Self {
            generalizers: Vec::new(),
        }
    }

    /// Add a generalizer to the pipeline.
    pub(crate) fn add(&mut self, g: Box<dyn LemmaGeneralizer>) -> &mut Self {
        self.generalizers.push(g);
        self
    }

    /// Run all generalizers in sequence until fixpoint.
    ///
    /// Returns the fully generalized lemma.
    pub(crate) fn generalize(
        &self,
        lemma: &ChcExpr,
        level: u32,
        ts: &mut dyn TransitionSystemRef,
    ) -> ChcExpr {
        let mut result = lemma.clone();
        let mut iteration = 0;
        const MAX_ITERATIONS: usize = 100; // Prevent infinite loops

        loop {
            let mut changed = false;
            let before = result.clone();

            for g in &self.generalizers {
                result = g.generalize(&result, level, ts);
            }

            // Check if anything changed
            if result != before {
                changed = true;
            }

            iteration += 1;
            if !changed || iteration >= MAX_ITERATIONS {
                break;
            }
        }

        result
    }
}

/// Drop-literal generalizer: drops conjuncts while maintaining inductiveness.
///
/// This is the most important generalizer (Z3's `lemma_bool_inductive_generalizer`).
/// For a lemma `L1 ∧ L2 ∧ ... ∧ Ln`, tries dropping each `Li` and checks if
/// the result is still inductive.
///
/// # Algorithm
///
/// ```text
/// for each literal L in cube:
///     cube[i] = true  // drop L
///     if check_inductive(cube):
///         keep dropped  // L is redundant
///     else:
///         restore L
/// ```
///
/// Reference: `reference/z3/src/muz/spacer/spacer_generalizers.cpp:62`
pub(crate) struct DropLiteralGeneralizer {
    /// Maximum consecutive failures before stopping
    failure_limit: usize,
}

impl Default for DropLiteralGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl DropLiteralGeneralizer {
    /// Create a new drop-literal generalizer with default failure limit.
    pub(crate) fn new() -> Self {
        Self { failure_limit: 10 }
    }

    /// Create a generalizer with a specific failure limit.
    pub(crate) fn with_failure_limit(limit: usize) -> Self {
        Self {
            failure_limit: limit,
        }
    }
}

impl LemmaGeneralizer for DropLiteralGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let literals = lemma.collect_conjuncts();

        if literals.len() <= 1 {
            return lemma.clone();
        }

        let mut kept_literals = Vec::new();
        let mut consecutive_failures = 0;

        for (i, lit) in literals.iter().enumerate() {
            if consecutive_failures >= self.failure_limit {
                // Hit failure limit, keep remaining literals
                kept_literals.extend(literals[i..].iter().cloned());
                break;
            }

            // Try dropping this literal
            let candidate: Vec<_> = kept_literals
                .iter()
                .chain(literals[(i + 1)..].iter())
                .cloned()
                .collect();

            if candidate.is_empty() {
                // Can't drop all literals
                kept_literals.push(lit.clone());
                consecutive_failures += 1;
                continue;
            }

            let candidate_expr = ChcExpr::and_all(candidate.iter().cloned());
            if ts.check_inductive(&candidate_expr, level) {
                // Literal can be dropped
                consecutive_failures = 0;
                continue;
            } else {
                // Must keep the literal
                kept_literals.push(lit.clone());
                consecutive_failures += 1;
            }
        }

        if kept_literals.len() < literals.len() {
            ChcExpr::and_all(kept_literals.iter().cloned())
        } else {
            lemma.clone()
        }
    }

    fn name(&self) -> &'static str {
        "drop-literal"
    }
}

/// Relevant variable projection generalizer: removes irrelevant variable assignments
/// from point lemmas while maintaining inductiveness.
///
/// Reference: Spacer's variable projection in `spacer_generalizers.cpp` (#1872).
pub(crate) struct RelevantVariableProjectionGeneralizer;

impl Default for RelevantVariableProjectionGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl RelevantVariableProjectionGeneralizer {
    /// Create a new relevant variable projection generalizer.
    pub(crate) fn new() -> Self {
        Self
    }

    /// Check if a conjunct is a point assignment (var = constant).
    fn is_point_assignment(expr: &ChcExpr) -> bool {
        match expr {
            ChcExpr::Op(crate::expr::ChcOp::Eq, args) if args.len() == 2 => {
                // Check if one side is a variable and the other is a constant
                // Args are Arc<ChcExpr>, so we need to deref to access the inner ChcExpr
                let (lhs, rhs) = (&*args[0], &*args[1]);
                (matches!(lhs, ChcExpr::Var(_)) && Self::is_constant(rhs))
                    || (matches!(rhs, ChcExpr::Var(_)) && Self::is_constant(lhs))
            }
            // Boolean variable or negated boolean variable
            ChcExpr::Var(_) => true,
            ChcExpr::Op(crate::expr::ChcOp::Not, args) if args.len() == 1 => {
                matches!(&*args[0], ChcExpr::Var(_))
            }
            _ => false,
        }
    }

    /// Check if an expression is a constant (no variables).
    fn is_constant(expr: &ChcExpr) -> bool {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::BitVec(_, _) | ChcExpr::Real(..) => true,
            ChcExpr::Var(_) => false,
            ChcExpr::Op(_, args) => args.iter().all(|a| Self::is_constant(a)),
            ChcExpr::PredicateApp(_, _, _) | ChcExpr::FuncApp(_, _, _) => false,
            ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_)
            | ChcExpr::ConstArray(_, _) => false,
        })
    }
}

impl LemmaGeneralizer for RelevantVariableProjectionGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let conjuncts = lemma.collect_conjuncts();

        // Only apply to lemmas with multiple point assignments
        if conjuncts.len() < 2 {
            return lemma.clone();
        }

        // Check if this is a point lemma (all conjuncts are point assignments)
        let all_point_assignments = conjuncts.iter().all(Self::is_point_assignment);
        if !all_point_assignments {
            return lemma.clone();
        }

        // Greedy removal: try removing each conjunct
        let mut kept: Vec<bool> = vec![true; conjuncts.len()];

        for i in 0..conjuncts.len() {
            // Skip if already removed
            if !kept[i] {
                continue;
            }

            // Build test expression without conjunct i
            let test_conjuncts: Vec<ChcExpr> = conjuncts
                .iter()
                .enumerate()
                .filter(|(j, _)| kept[*j] && *j != i)
                .map(|(_, c)| c.clone())
                .collect();

            // Need at least one conjunct
            if test_conjuncts.is_empty() {
                continue;
            }

            let test_expr = ChcExpr::and_all(test_conjuncts.iter().cloned());

            // If removal maintains inductiveness, the variable is irrelevant
            if ts.check_inductive(&test_expr, level) {
                kept[i] = false;
            }
        }

        // Build result from kept conjuncts
        let result_conjuncts: Vec<ChcExpr> = conjuncts
            .iter()
            .enumerate()
            .filter(|(i, _)| kept[*i])
            .map(|(_, c)| c.clone())
            .collect();

        if result_conjuncts.len() < conjuncts.len() && !result_conjuncts.is_empty() {
            ChcExpr::and_all(result_conjuncts.iter().cloned())
        } else {
            lemma.clone()
        }
    }

    fn name(&self) -> &'static str {
        "relevant-variable-projection"
    }
}

/// Unsat-core based generalizer: uses SMT unsat cores to minimize lemmas.
///
/// Z3 equivalent: `unsat_core_generalizer` in `spacer_generalizers.cpp:151`
///
/// Unlike [`DropLiteralGeneralizer`] which tries literals one-by-one, this
/// uses the SMT solver's ability to extract minimal unsat cores directly.
/// This makes a single SMT call instead of O(n) calls.
///
/// The generalizer works by:
/// 1. Building the inductiveness query with negated conjuncts as assumptions
/// 2. Extracting which assumptions were needed for UNSAT
/// 3. Keeping only the corresponding positive conjuncts
///
/// Reference: `reference/z3/src/muz/spacer/spacer_generalizers.cpp:151-177`
pub(crate) struct UnsatCoreGeneralizer;

impl Default for UnsatCoreGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl UnsatCoreGeneralizer {
    /// Create a new unsat-core generalizer.
    pub(crate) fn new() -> Self {
        Self
    }
}

impl LemmaGeneralizer for UnsatCoreGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let conjuncts = lemma.collect_conjuncts();

        if conjuncts.len() <= 1 {
            return lemma.clone();
        }

        // Use the trait method to get the unsat core.
        // The trait contract guarantees that `check_inductive_with_core` returns
        // a subset of the input `conjuncts` (positive, unmapped), so we can use
        // the result directly without any mapping.
        match ts.check_inductive_with_core(&conjuncts, level) {
            Some(core) if !core.is_empty() && core.len() < conjuncts.len() => {
                ChcExpr::and_all(core.iter().cloned())
            }
            _ => lemma.clone(),
        }
    }

    fn name(&self) -> &'static str {
        "unsat-core"
    }
}

mod array_select_index;
mod array_store_projection;
mod bound_expansion;
mod bv_decompose;
mod bv_flag_guards;
mod bv_group;
mod bv_mask;
mod bv_per_bit_replacement;
mod denominator;
mod relational;
mod weakening;
pub(crate) use array_select_index::ArraySelectIndexGeneralizer;
pub(crate) use array_store_projection::{
    ArrayEqualityDropGeneralizer, ArraySelectValueWeakeningGeneralizer,
    ArrayStoreProjectionGeneralizer,
};
pub(crate) use bound_expansion::{BoundExpansionGeneralizer, FarkasGeneralizer};
pub(crate) use bv_decompose::BvBitDecompositionGeneralizer;
pub(crate) use bv_flag_guards::BvFlagGuardGeneralizer;
pub(crate) use bv_group::BvBitGroupGeneralizer;
pub(crate) use bv_mask::BvMaskGeneralizer;
pub(crate) use bv_per_bit_replacement::BvPerBitReplacementGeneralizer;
pub(crate) use denominator::DenominatorSimplificationGeneralizer;
pub(crate) use relational::{
    ConstantSumGeneralizer, ImplicationGeneralizer, RelationalEqualityGeneralizer,
    TemplateGeneralizer,
};
pub(crate) use weakening::{
    InitBoundWeakeningGeneralizer, LiteralWeakeningGeneralizer, SingleVariableRangeGeneralizer,
};

#[cfg(test)]
mod tests;
