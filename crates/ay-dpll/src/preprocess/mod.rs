// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Preprocessing framework for SMT assertions
//!
//! Provides a framework for preprocessing passes that transform assertions
//! before Tseitin encoding and theory solving. This is essential for:
//!
//! 1. **Soundness** - Variable substitution ensures semantic equivalence
//!    is propagated to CNF encoding (#1708, #1720, #1782)
//! 2. **Performance** - Simplification reduces CNF size
//!
//! # Architecture
//!
//! Each pass implements [`PreprocessingPass`] and operates on assertions.
//! The [`Preprocessor`] orchestrates passes in a fixed-point loop until
//! no pass makes modifications.
//!
//! # Reference
//!
//! Pattern follows Bitwuzla's preprocessing framework:
//! - `reference/bitwuzla/src/preprocess/preprocessor.cpp`
//! - `reference/bitwuzla/src/preprocess/pass/`

mod bit_blast;
mod der;
mod distribute_forall;
mod eq_diffvar;
mod flatten_and;
mod guarded_eq_mining;
mod ite_equality;
mod nnf;
mod normalize_arith_som;
mod normalize_bv_arith;
mod normalize_eq_bv_concat;
mod propagate_ineqs;
mod propagate_values;
pub(crate) mod qe_light;
mod reduce_args;
mod tseitin_cnf;
mod variable_subst;

pub(crate) use bit_blast::BitBlast;
// Apply-surface only (z3's `der` / `distribute-forall` / `reduce-args`
// tactics): plain structs, NOT `PreprocessingPass`, deliberately never enrolled
// in the solve pipeline (so `check-sat`/`get-model` behavior is unchanged).
pub(crate) use der::Der;
pub(crate) use distribute_forall::DistributeForall;
pub(crate) use eq_diffvar::{AtomFold, EqDiffVar};
pub(crate) use flatten_and::FlattenAnd;
pub(crate) use guarded_eq_mining::GuardedEqMining;
pub(crate) use ite_equality::IteEquality;
pub(crate) use nnf::Nnf;
pub(crate) use normalize_arith_som::NormalizeArithSom;
pub(crate) use normalize_bv_arith::NormalizeBvArith;
pub(crate) use normalize_eq_bv_concat::NormalizeEqBvConcat;
// Apply-surface only (z3's `propagate-ineqs` tactic): NOT a
// `PreprocessingPass`, deliberately never enrolled in the solve pipeline.
pub(crate) use propagate_ineqs::PropagateIneqs;
pub(crate) use propagate_values::{
    EqDiffVarAtomRecord, PropagateValues, PropagatedEntrySource, PropagatedRewriteRecord,
    PropagationRecords,
};
pub(crate) use qe_light::QeLight;
pub(crate) use reduce_args::ReduceArgs;
pub(crate) use tseitin_cnf::TseitinCnf;
pub(crate) use variable_subst::{VariableSubstitution, VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT};

use ay_core::{TermId, TermStore};
use std::sync::{Arc, Mutex};

/// Shared-handle wrapper for preprocessing passes whose state is inspected
/// after the fixed-point loop.
struct SharedPass<P>(Arc<Mutex<P>>);

impl<P: PreprocessingPass> PreprocessingPass for SharedPass<P> {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        self.0.lock().unwrap().apply(terms, assertions)
    }

    fn apply_with_sources(
        &mut self,
        terms: &mut TermStore,
        assertions: &mut Vec<TermId>,
        source_sets: &mut Vec<Vec<TermId>>,
    ) -> bool {
        self.0
            .lock()
            .unwrap()
            .apply_with_sources(terms, assertions, source_sets)
    }

    fn reset(&mut self) {
        self.0.lock().unwrap().reset();
    }
}

/// A preprocessing pass that transforms assertions.
///
/// Passes should be idempotent - running a pass twice on the same input
/// should produce the same output (and return false the second time).
pub(crate) trait PreprocessingPass {
    /// Apply the pass to the assertions.
    ///
    /// # Arguments
    /// * `terms` - The term store for creating/inspecting terms
    /// * `assertions` - Mutable list of assertions to transform
    ///
    /// # Returns
    /// `true` if any modifications were made, `false` otherwise.
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool;

    /// Apply the pass while preserving provenance for transformed assertions.
    ///
    /// `source_sets[i]` contains the original assertion roots that produced
    /// `assertions[i]`. One-to-one rewrite passes can rely on the default
    /// positional preservation. Passes that split, add, remove, or reorder roots
    /// must override this method.
    fn apply_with_sources(
        &mut self,
        terms: &mut TermStore,
        assertions: &mut Vec<TermId>,
        source_sets: &mut Vec<Vec<TermId>>,
    ) -> bool {
        debug_assert_eq!(assertions.len(), source_sets.len());
        let old_len = assertions.len();
        let modified = self.apply(terms, assertions);
        if modified && assertions.len() != old_len {
            source_sets.clear();
            source_sets.resize(assertions.len(), Vec::new());
        }
        debug_assert_eq!(assertions.len(), source_sets.len());
        modified
    }

    /// Reset pass state for a new preprocessing round.
    ///
    /// Default implementation does nothing. Override if your pass
    /// maintains state between applications.
    fn reset(&mut self) {}
}

/// Orchestrates preprocessing passes in a fixed-point loop.
///
/// Runs all passes repeatedly until no pass makes modifications,
/// ensuring the assertions reach a stable preprocessed form.
pub(crate) struct Preprocessor {
    passes: Vec<Box<dyn PreprocessingPass>>,
    /// Maximum iterations to prevent infinite loops
    max_iterations: usize,
}

impl Default for Preprocessor {
    fn default() -> Self {
        Self::new()
    }
}

impl Preprocessor {
    /// Create a new preprocessor with default passes.
    ///
    /// Default passes (in order):
    /// 1. [`NormalizeEqBvConcat`] - Split BV concat equalities into component equalities
    /// 2. [`FlattenAnd`] - Flatten nested AND into individual assertions
    /// 3. [`PropagateValues`] - Propagate ground equalities `(= EXPR CONST)` (#5081)
    /// 4. [`IteEquality`] - Derive equalities from ITE-based assignments
    /// 5. [`VariableSubstitution`] - Substitute equivalent variables
    /// 6. [`NormalizeBvArith`] - Canonicalize BV arithmetic (bvadd/bvmul)
    ///
    /// Returns the variable-substitution and `PropagateValues` pass handles so
    /// callers can inspect substitutions and drain producer provenance after
    /// the loop (#ppp-provenance).
    pub(crate) fn new_with_subst_and_propagation() -> (
        Self,
        Arc<Mutex<VariableSubstitution>>,
        Arc<Mutex<PropagateValues>>,
    ) {
        let var_subst = Arc::new(Mutex::new(VariableSubstitution::new()));
        let propagate_values = Arc::new(Mutex::new(PropagateValues::new()));
        let preprocessor = Self {
            passes: vec![
                Box::new(NormalizeEqBvConcat::new()),
                Box::new(FlattenAnd::new()),
                Box::new(SharedPass(propagate_values.clone())),
                Box::new(IteEquality::new()),
                Box::new(SharedPass(var_subst.clone())),
                Box::new(NormalizeBvArith::new()),
            ],
            max_iterations: 100,
        };
        (preprocessor, var_subst, propagate_values)
    }

    /// Create a new preprocessor with default passes.
    pub(crate) fn new() -> Self {
        Self {
            passes: vec![
                Box::new(NormalizeEqBvConcat::new()),
                Box::new(FlattenAnd::new()),
                Box::new(PropagateValues::new()),
                Box::new(IteEquality::new()),
                Box::new(VariableSubstitution::new()),
                Box::new(NormalizeBvArith::new()),
            ],
            max_iterations: 100,
        }
    }

    /// Run all passes until fixed point.
    ///
    /// Returns the number of iterations performed.
    #[allow(dead_code)]
    pub(crate) fn preprocess(
        &mut self,
        terms: &mut TermStore,
        assertions: &mut Vec<TermId>,
    ) -> usize {
        let mut iterations = 0;

        loop {
            iterations += 1;
            if iterations > self.max_iterations {
                // Exceeded max iterations - stop to prevent infinite loop
                break;
            }

            let mut modified = false;
            for pass in &mut self.passes {
                let pass_modified = pass.apply(terms, assertions);
                modified |= pass_modified;
            }

            if !modified {
                break;
            }

            // Reset passes for next iteration
            for pass in &mut self.passes {
                pass.reset();
            }
        }

        iterations
    }

    /// Run all passes until fixed point while carrying assertion provenance.
    pub(crate) fn preprocess_with_sources(
        &mut self,
        terms: &mut TermStore,
        assertions: &mut Vec<TermId>,
        source_sets: &mut Vec<Vec<TermId>>,
    ) -> usize {
        debug_assert_eq!(assertions.len(), source_sets.len());
        let mut iterations = 0;
        // Env-gated per-pass timing (`--phase-trace`): pass index follows the
        // `new_with_subst` order (0 NormalizeEqBvConcat, 1 FlattenAnd,
        // 2 PropagateValues, 3 IteEquality, 4 VariableSubstitution,
        // 5 NormalizeBvArith). Diagnostic-only stderr comment lines.
        let trace = ay_core::misc_cli_flags().phase_trace;

        loop {
            iterations += 1;
            if iterations > self.max_iterations {
                break;
            }

            let mut modified = false;
            for (pass_idx, pass) in self.passes.iter_mut().enumerate() {
                let t0 = trace.then(ay_core::time::Instant::now);
                let pass_modified = pass.apply_with_sources(terms, assertions, source_sets);
                if let Some(t0) = t0 {
                    eprintln!(
                        "c phase-trace preprocess iter={} pass={} modified={} asserts={} took={:.2}s",
                        iterations,
                        pass_idx,
                        pass_modified,
                        assertions.len(),
                        t0.elapsed().as_secs_f64()
                    );
                }
                debug_assert_eq!(assertions.len(), source_sets.len());
                modified |= pass_modified;
            }

            if !modified {
                break;
            }

            for pass in &mut self.passes {
                pass.reset();
            }
        }

        iterations
    }
}

#[cfg(test)]
mod tests;
