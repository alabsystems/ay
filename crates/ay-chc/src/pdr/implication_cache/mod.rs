// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-guided implication caching for PDR push phase.
//!
//! This module implements the LAWI-style implication checking pattern from Golem's
//! ImplicationChecker class. The key insight is that counterexample models from
//! failed implication checks can be cached and reused to quickly reject future
//! implication queries without solver calls.
//!
//! ## Algorithm
//!
//! When checking whether antecedent implies consequent:
//! 1. Fast path: Check if any cached model satisfying antecedent falsifies consequent.
//!    If so, the implication is invalid (O-1 model evaluation vs O-expensive SAT).
//! 2. Slow path: Call SMT solver. If SAT (counterexample found), cache the model.
//!
//! ## Reference
//!
//! Golem LAWI engine: reference/golem/src/engine/Lawi.cc:199-272
//!
//! ## Related Issues
//!
//! - #2126: Model-guided implication caching (this implementation)
//! - #428: Full LAWI engine
//! - #1178: Spacer lemma clustering

use crate::chc_statistics::NativeCodeHelperStatistics;
use crate::{ChcExpr, ChcOp, ChcSort, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_jit::expr_eval::{compile_expr, CompiledExprEval, ExprLike, VarMapping};
use std::{env, sync::OnceLock};

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;

/// Result of an implication check.
///
/// Part of the full LAWI-style API (check_with_hints, record_result).
/// The blocking-focused API uses the simpler blocking_rejected_by_cache which returns bool.
/// Production integration tracked in #428 (full LAWI engine).
#[cfg(test)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ImplicationResult {
    /// The implication holds (antecedent implies consequent is valid).
    Valid,
    /// The implication does not hold (there exists a model satisfying antecedent but not consequent).
    Invalid,
}

/// A compact model representation for fast evaluation.
///
/// Uses variable names as keys and integer/boolean values.
/// More memory-efficient than storing full ChcExpr models.
#[derive(Debug, Clone)]
pub(crate) struct SmallModel {
    /// Stable identity used by the dense projection cache.
    projection_id: u64,
    /// Variable name to integer value assignments.
    int_assignments: FxHashMap<String, i128>,
    /// Variable name to boolean value assignments.
    bool_assignments: FxHashMap<String, bool>,
}

impl SmallModel {
    /// Create a SmallModel from an SMT solver model.
    pub(crate) fn from_smt_model(model: &FxHashMap<String, SmtValue>) -> Self {
        Self::from_smt_model_with_projection_id(model, 0)
    }

    /// Create a SmallModel with an explicit dense projection identity.
    fn from_smt_model_with_projection_id(
        model: &FxHashMap<String, SmtValue>,
        projection_id: u64,
    ) -> Self {
        let mut int_assignments = FxHashMap::default();
        let mut bool_assignments = FxHashMap::default();

        for (name, value) in model {
            match value {
                SmtValue::Int(n) => {
                    int_assignments.insert(name.clone(), *n);
                }
                SmtValue::Bool(b) => {
                    bool_assignments.insert(name.clone(), *b);
                }
                SmtValue::Real(r) => {
                    // Convert rational to integer if denominator is 1.
                    use num_traits::{One, ToPrimitive};
                    if r.denom().is_one() {
                        if let Some(n) = r.numer().to_i64() {
                            int_assignments.insert(name.clone(), i128::from(n));
                        }
                    }
                }
                SmtValue::BitVec(n, _width) => {
                    // Convert bitvector to integer for evaluation purposes.
                    if let Ok(int_val) = i128::try_from(*n) {
                        int_assignments.insert(name.clone(), int_val);
                    }
                }
                // Beyond-i128 witnesses: skip (i128 cache boundary; the
                // evaluator abstains on the missing var — fail-closed).
                // Array/DT values have no scalar representation.
                SmtValue::BigInt(_)
                | SmtValue::Opaque(_)
                | SmtValue::ConstArray(_)
                | SmtValue::ArrayMap { .. }
                | SmtValue::Datatype(..) => {}
            }
        }

        Self {
            projection_id,
            int_assignments,
            bool_assignments,
        }
    }

    /// Evaluate a boolean expression under this model.
    pub(crate) fn evaluate(&self, expr: &ChcExpr) -> Option<bool> {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Bool(b) => Some(*b),

            ChcExpr::Var(v) => self.bool_assignments.get(&v.name).copied(),

            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => self.evaluate(&args[0]).map(|b| !b),

            ChcExpr::Op(ChcOp::And, args) => {
                // Short-circuit evaluation with single pass (O(N) not O(2N))
                let mut all_determined = true;
                for arg in args {
                    match self.evaluate(arg) {
                        Some(false) => return Some(false),
                        Some(true) => {}
                        None => all_determined = false,
                    }
                }
                if all_determined {
                    Some(true)
                } else {
                    None
                }
            }

            ChcExpr::Op(ChcOp::Or, args) => {
                // Short-circuit evaluation with single pass (O(N) not O(2N))
                let mut all_determined = true;
                for arg in args {
                    match self.evaluate(arg) {
                        Some(true) => return Some(true),
                        Some(false) => {}
                        None => all_determined = false,
                    }
                }
                if all_determined {
                    Some(false)
                } else {
                    None
                }
            }

            ChcExpr::Op(ChcOp::Implies, args) if args.len() == 2 => {
                match (self.evaluate(&args[0]), self.evaluate(&args[1])) {
                    (Some(false), _) | (_, Some(true)) => Some(true),
                    (Some(true), Some(false)) => Some(false),
                    _ => None,
                }
            }

            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                self.compare_values(&args[0], &args[1], |a, b| a == b)
            }

            ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
                self.compare_values(&args[0], &args[1], |a, b| a != b)
            }

            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                self.compare_ints(&args[0], &args[1], |a, b| a < b)
            }

            ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                self.compare_ints(&args[0], &args[1], |a, b| a <= b)
            }

            ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
                self.compare_ints(&args[0], &args[1], |a, b| a > b)
            }

            ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                self.compare_ints(&args[0], &args[1], |a, b| a >= b)
            }

            _ => None,
        })
    }

    fn evaluate_int(&self, expr: &ChcExpr) -> Option<i128> {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Int(n) => Some(*n),
            // #5523: Treat BV constants as integers for cache evaluation.
            ChcExpr::BitVec(v, _w) => i128::try_from(*v).ok(),
            ChcExpr::Var(v) => self.int_assignments.get(&v.name).copied(),
            ChcExpr::Op(ChcOp::Add, args) => {
                let mut sum: i128 = 0;
                for arg in args {
                    sum = sum.checked_add(self.evaluate_int(arg)?)?;
                }
                Some(sum)
            }
            ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
                let first = self.evaluate_int(&args[0])?;
                if args.len() == 1 {
                    return first.checked_neg();
                }
                let mut result = first;
                for arg in &args[1..] {
                    result = result.checked_sub(self.evaluate_int(arg)?)?;
                }
                Some(result)
            }
            ChcExpr::Op(ChcOp::Mul, args) => {
                let mut product: i128 = 1;
                for arg in args {
                    product = product.checked_mul(self.evaluate_int(arg)?)?;
                }
                Some(product)
            }
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                self.evaluate_int(&args[0])?.checked_neg()
            }
            ChcExpr::Op(ChcOp::Div, args) if args.len() == 2 => {
                let a = self.evaluate_int(&args[0])?;
                let b = self.evaluate_int(&args[1])?;
                if b == 0 {
                    None
                } else {
                    // SMT-LIB div is Euclidean (remainder always non-negative), not truncation
                    a.checked_div_euclid(b)
                }
            }
            ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
                let a = self.evaluate_int(&args[0])?;
                let b = self.evaluate_int(&args[1])?;
                if b == 0 {
                    None
                } else {
                    a.checked_rem_euclid(b)
                }
            }
            _ => None,
        })
    }

    /// Fill a flat `i64` array with variable values from this model, indexed by `VarMapping`.
    ///
    /// Boolean variables are stored as 0 (false) or 1 (true). Returns `false`
    /// when the model is missing a required variable; callers should deopt to
    /// `SmallModel::evaluate` so partial models retain three-valued semantics.
    pub(crate) fn fill_var_array(&self, mapping: &VarMapping, out: &mut [i64]) -> bool {
        let mut complete = true;
        for (name, &idx) in mapping.iter() {
            let idx = idx as usize;
            if idx >= out.len() {
                complete = false;
                continue;
            }
            if let Some(&v) = self.int_assignments.get(name) {
                // i128-lockstep: the JIT lane operates on i64 arrays; deopt to
                // the interpreter (complete=false) when a value exceeds i64.
                match i64::try_from(v) {
                    Ok(v64) => out[idx] = v64,
                    Err(_) => complete = false,
                }
            } else if let Some(&b) = self.bool_assignments.get(name) {
                out[idx] = i64::from(b);
            } else {
                complete = false;
            }
        }
        complete
    }

    fn covers_jit_formula_vars(&self, expr: &ChcExpr) -> bool {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Bool(_) | ChcExpr::Int(_) => true,
            ChcExpr::Var(var) => match var.sort {
                ChcSort::Int => self.int_assignments.contains_key(&var.name),
                ChcSort::Bool => self.bool_assignments.contains_key(&var.name),
                _ => false,
            },
            ChcExpr::Op(_, args) => args.iter().all(|arg| self.covers_jit_formula_vars(arg)),
            _ => false,
        })
    }

    fn compare_ints<F>(&self, a: &ChcExpr, b: &ChcExpr, cmp: F) -> Option<bool>
    where
        F: Fn(i128, i128) -> bool,
    {
        Some(cmp(self.evaluate_int(a)?, self.evaluate_int(b)?))
    }

    fn compare_values<F>(&self, a: &ChcExpr, b: &ChcExpr, cmp: F) -> Option<bool>
    where
        F: Fn(i128, i128) -> bool,
    {
        if let (Some(a_val), Some(b_val)) = (self.evaluate_int(a), self.evaluate_int(b)) {
            return Some(cmp(a_val, b_val));
        }
        if let (Some(a_val), Some(b_val)) = (self.evaluate(a), self.evaluate(b)) {
            return Some(if cmp(1, 1) {
                a_val == b_val
            } else {
                a_val != b_val
            });
        }
        None
    }
}

/// Maximum distinct (predicate, level) keys before eviction (#3077 finding 4).
/// With P predicates and L levels, worst case is P*L*8 SmallModels. Cap total
/// keys to bound memory. When exceeded, clear and start fresh (same pattern as
/// bounded_cache_insert in core.rs).
const MAX_BLOCKING_COUNTERMODEL_KEYS: usize = 10_000;

/// Minimum evaluations before JIT-compiling an expression (#8274).
///
/// x86_64 is the CHC-COMP target in this factory. Same-binary proxy runs show
/// that compiling scalar helpers on first model scan can spend more time in
/// native codegen than it saves. Require a short reuse signal before admitting
/// a cache-rejection helper.
#[cfg(target_arch = "x86_64")]
pub(crate) const JIT_COMPILE_THRESHOLD: usize = 4;

/// Minimum evaluations before JIT-compiling an expression (#8274).
#[cfg(not(target_arch = "x86_64"))]
pub(crate) const JIT_COMPILE_THRESHOLD: usize = 4;

/// Maximum cached JIT-compiled expressions to bound memory.
const MAX_JIT_CACHE_ENTRIES: usize = 1_000;

/// Maximum cached dense model projections to bound memory.
const MAX_DENSE_PROJECTION_CACHE_ENTRIES: usize = 16_384;

/// Maximum record-time native-helper compile admissions per implication cache.
///
/// Record-time validation is useful for refreshing a saturated countermodel
/// slot, but it is not on the cache-rejection hot path. It only runs once the
/// slot is saturated, must first pass a row-local reuse signal, then this cap
/// bounds admitted formulas so `current` mode does not spend CHC time compiling
/// many one-shot helper formulas.
const MAX_RECORD_TIME_NATIVE_HELPER_COMPILE_ADMISSIONS: usize = 32;

struct CachedJitExpr {
    compiled: CompiledExprEval,
    mapping_id: u64,
    trusted_native_true: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct DenseProjectionCacheKey {
    model_id: u64,
    mapping_id: u64,
}

#[derive(Debug, Clone)]
enum DenseProjection {
    Complete(Vec<i64>),
    MissingVariable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DenseProjectionEval {
    Evaluated(Option<bool>),
    MissingVariable,
}

#[derive(Debug, Clone)]
enum DenseProjectionForEval {
    Complete(Vec<i64>),
    MissingVariable,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TrustedRawTermSort {
    Bool,
    Int,
}

/// Conservative grammar for native `true` results that can be trusted without
/// a SmallModel oracle confirmation.
fn trusted_native_true_formula(expr: &ChcExpr) -> bool {
    let mut vars = FxHashMap::default();
    trusted_native_true_formula_impl(expr, &mut vars)
}

fn trusted_native_true_formula_impl(
    expr: &ChcExpr,
    vars: &mut FxHashMap<String, TrustedRawTermSort>,
) -> bool {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Bool(_) => true,
        ChcExpr::Var(v) if v.sort == ChcSort::Bool => {
            trusted_var(&v.name, TrustedRawTermSort::Bool, vars)
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            trusted_native_true_formula_impl(&args[0], vars)
        }
        ChcExpr::Op(ChcOp::And | ChcOp::Or, args) => args
            .iter()
            .all(|arg| trusted_native_true_formula_impl(arg, vars)),
        ChcExpr::Op(ChcOp::Implies | ChcOp::Iff, args) if args.len() == 2 => {
            trusted_native_true_formula_impl(&args[0], vars)
                && trusted_native_true_formula_impl(&args[1], vars)
        }
        ChcExpr::Op(ChcOp::Eq | ChcOp::Ne, args) if args.len() == 2 => {
            trusted_raw_same_sort_terms(&args[0], &args[1], vars)
        }
        ChcExpr::Op(ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge, args) if args.len() == 2 => {
            trusted_raw_int_term(&args[0], vars) && trusted_raw_int_term(&args[1], vars)
        }
        _ => false,
    })
}

fn trusted_raw_same_sort_terms(
    left: &ChcExpr,
    right: &ChcExpr,
    vars: &mut FxHashMap<String, TrustedRawTermSort>,
) -> bool {
    match (
        trusted_raw_term_sort(left, vars),
        trusted_raw_term_sort(right, vars),
    ) {
        (Some(left_sort), Some(right_sort)) => left_sort == right_sort,
        _ => false,
    }
}

fn trusted_raw_int_term(expr: &ChcExpr, vars: &mut FxHashMap<String, TrustedRawTermSort>) -> bool {
    trusted_raw_term_sort(expr, vars) == Some(TrustedRawTermSort::Int)
}

fn trusted_raw_term_sort(
    expr: &ChcExpr,
    vars: &mut FxHashMap<String, TrustedRawTermSort>,
) -> Option<TrustedRawTermSort> {
    match expr {
        ChcExpr::Bool(_) => Some(TrustedRawTermSort::Bool),
        ChcExpr::Int(_) => Some(TrustedRawTermSort::Int),
        ChcExpr::Var(v) => match &v.sort {
            ChcSort::Bool => trusted_var(&v.name, TrustedRawTermSort::Bool, vars)
                .then_some(TrustedRawTermSort::Bool),
            ChcSort::Int => trusted_var(&v.name, TrustedRawTermSort::Int, vars)
                .then_some(TrustedRawTermSort::Int),
            _ => None,
        },
        _ => None,
    }
}

fn trusted_var(
    name: &str,
    sort: TrustedRawTermSort,
    vars: &mut FxHashMap<String, TrustedRawTermSort>,
) -> bool {
    match vars.get(name) {
        Some(existing) => *existing == sort,
        None => {
            vars.insert(name.to_string(), sort);
            true
        }
    }
}

fn native_code_helpers_enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| {
        let explicit = env::var("AY_CHC_NATIVE_CODE_HELPERS").ok();
        let competition_mode = env::var("AY_COMPETITION_JIT_CANDIDATE_MODE")
            .ok()
            .or_else(|| env::var("AY_COMPETITION_JIT_MODE").ok());
        native_code_helpers_enabled_for_modes(explicit.as_deref(), competition_mode.as_deref())
    })
}

fn native_code_helper_candidate_formula(expr: &ChcExpr) -> bool {
    expr.is_boolean() && expr.is_jit_compilable()
}

fn native_code_helpers_enabled_for_modes(
    explicit: Option<&str>,
    competition_mode: Option<&str>,
) -> bool {
    if let Some(mode) = competition_mode {
        return parse_competition_native_helper_mode(mode);
    }

    if let Some(mode) = explicit {
        return parse_native_helper_mode(mode);
    }

    // Default ON. The #18 crash class (deterministic pc==lr==fp instruction
    // aborts on reve/010-horn and rust-horn/bmc-2 with helpers enabled) was
    // root-caused to the aarch64 expression-evaluator codegen, NOT to JIT
    // ownership: its register-"spill" fallback emitted an unmatched `stp`
    // once an expression pushed more values than the scratch register file,
    // and the epilogue then popped that orphaned slot as the frame record,
    // so `ret` branched into a data value. The generator now assigns
    // registers by operand-stack position (reusing popped positions) and
    // fails closed to the interpreter when the peak operand depth exceeds
    // the scratch file (`ay_jit::expr_eval::peak_operand_stack_depth`).
    // Verified post-fix: both ex-crashers run clean with helpers ON.
    true
}

fn parse_native_helper_mode(value: &str) -> bool {
    match value.trim().to_ascii_lowercase().as_str() {
        "1" | "true" | "yes" | "on" | "enabled" | "current" => true,
        "0" | "false" | "no" | "off" | "disabled" | "profile-only" | "solver-program" => false,
        _ => false,
    }
}

fn parse_competition_native_helper_mode(value: &str) -> bool {
    match value.trim().to_ascii_lowercase().as_str() {
        "current" => true,
        "off" | "profile-only" | "solver-program" => false,
        _ => false,
    }
}

/// Cache for implication checking with model-guided fast rejection.
pub(crate) struct ImplicationCache {
    /// LAWI-style result cache. Production integration tracked in #428.
    #[cfg(test)]
    result_cache: FxHashMap<(u64, u64), ImplicationResult>,
    /// LAWI-style implication countermodels. Production integration tracked in #428.
    #[cfg(test)]
    implication_countermodels: FxHashMap<u64, Vec<SmallModel>>,
    blocking_countermodels: FxHashMap<(usize, usize), Vec<SmallModel>>,
    /// Frame-state epoch the blocking countermodels were recorded against.
    ///
    /// A cached countermodel is a head-predicate state that was one-step
    /// reachable from the frame constraints *at record time*. Frames only
    /// strengthen as lemmas are added, so a recorded state can become
    /// unreachable — a stale cache rejection then permanently blocks a lemma
    /// that has become inductive. This is exactly what stalled multi-predicate
    /// chains: blocking the head POB first records a countermodel, then the
    /// predecessor gets its own lemma, and the retried head lemma was
    /// fast-rejected by the stale model at every level until max_frames
    /// (#pdr-chain). Callers must publish the current frame epoch via
    /// [`Self::note_frame_epoch`] before recording or querying; on any epoch
    /// change all countermodels are dropped (conservative: frame changes that
    /// only weaken frames also clear, which costs reuse but never soundness).
    frame_epoch: u64,
    max_models_per_key: usize,
    pub(crate) cache_hits: usize,
    pub(crate) model_rejections: usize,
    pub(crate) solver_calls: usize,
    /// JIT-compiled expression cache: structural_hash -> compiled evaluator (#8274).
    /// Only populated on native-supported architectures. Non-compilable
    /// expressions get a `None` sentinel to avoid repeated compilation attempts.
    jit_cache: FxHashMap<u64, Option<CachedJitExpr>>,
    /// Evaluation count per expression hash for JIT compilation triggering.
    jit_eval_counts: FxHashMap<u64, usize>,
    /// Stable signature-to-id table for compiled expression variable mappings.
    dense_projection_mapping_ids: FxHashMap<Box<[(String, u32)]>, u64>,
    /// Cached dense model projections keyed by model and variable mapping identity.
    dense_projection_cache: FxHashMap<DenseProjectionCacheKey, DenseProjection>,
    next_dense_projection_mapping_id: u64,
    next_model_projection_id: u64,
    /// Stats: number of JIT-accelerated evaluations.
    pub(crate) jit_evaluations: usize,
    /// Stats: number of native helper compile attempts.
    pub(crate) jit_compile_attempts: usize,
    /// Stats: number of successful native helper compilations.
    pub(crate) jit_compile_successes: usize,
    /// Stats: number of failed or unsupported native helper compilations.
    pub(crate) jit_compile_failures: usize,
    /// Stats: number of conservative native-helper deopts.
    pub(crate) jit_deopts: usize,
    /// Stats: number of fallbacks to the SmallModel interpreter.
    pub(crate) jit_fallbacks: usize,
    /// Stats: interpreter fallbacks caused by missing model variables.
    /// Native helper scans now skip incomplete dense projections instead of
    /// falling back through the interpreter, so this should stay zero in
    /// competition current mode unless another validation path is added.
    pub(crate) jit_missing_var_fallbacks: usize,
    /// Stats: native true results confirmed by the interpreter oracle.
    pub(crate) jit_interpreter_confirmations: usize,
    /// Stats: native true results accepted by the conservative trust grammar.
    pub(crate) jit_trusted_true_results: usize,
    /// Stats: accepted native true helper applications.
    pub(crate) native_helper_applications: usize,
    record_time_native_helper_compile_admissions: usize,
    record_time_native_helper_row_eval_counts: FxHashMap<(usize, usize, u64), usize>,
}

impl Default for ImplicationCache {
    fn default() -> Self {
        Self::new()
    }
}

impl ImplicationCache {
    pub(crate) fn new() -> Self {
        Self {
            #[cfg(test)]
            result_cache: FxHashMap::default(),
            #[cfg(test)]
            implication_countermodels: FxHashMap::default(),
            blocking_countermodels: FxHashMap::default(),
            frame_epoch: 0,
            max_models_per_key: 8,
            cache_hits: 0,
            model_rejections: 0,
            solver_calls: 0,
            jit_cache: FxHashMap::default(),
            jit_eval_counts: FxHashMap::default(),
            dense_projection_mapping_ids: FxHashMap::default(),
            dense_projection_cache: FxHashMap::default(),
            next_dense_projection_mapping_id: 1,
            next_model_projection_id: 1,
            jit_evaluations: 0,
            jit_compile_attempts: 0,
            jit_compile_successes: 0,
            jit_compile_failures: 0,
            jit_deopts: 0,
            jit_fallbacks: 0,
            jit_missing_var_fallbacks: 0,
            jit_interpreter_confirmations: 0,
            jit_trusted_true_results: 0,
            native_helper_applications: 0,
            record_time_native_helper_compile_admissions: 0,
            record_time_native_helper_row_eval_counts: FxHashMap::default(),
        }
    }

    /// Publish the current frame-state epoch (see `frame_epoch` field docs).
    ///
    /// Cached blocking countermodels are only valid relative to the frame
    /// state they were recorded against. When the epoch changes (any lemma
    /// added to or removed from any frame), all cached countermodels are
    /// dropped so stale states cannot fast-reject lemmas that have become
    /// inductive under the strengthened frames (#pdr-chain).
    ///
    /// Every production record/query path must call this first with
    /// `PdrSolver::frames_lemma_epoch()`.
    pub(crate) fn note_frame_epoch(&mut self, epoch: u64) {
        if epoch != self.frame_epoch {
            self.frame_epoch = epoch;
            self.blocking_countermodels.clear();
        }
    }

    /// Check if any cached countermodel for (predicate, level) satisfies the blocking formula.
    /// Returns true if blocking_formula is satisfied by a cached model (lemma is NOT inductive).
    ///
    /// On native-supported architectures, frequently-evaluated expressions are
    /// JIT-compiled to native code after `JIT_COMPILE_THRESHOLD` evaluations.
    /// JIT-compiled expressions use flat array indexing instead of HashMap
    /// lookups for variable resolution (#8274).
    pub(crate) fn blocking_rejected_by_cache(
        &mut self,
        predicate_idx: usize,
        level: usize,
        blocking_formula: &ChcExpr,
    ) -> bool {
        let key = (predicate_idx, level);
        if self
            .blocking_countermodels
            .get(&key)
            .is_none_or(|m| m.is_empty())
        {
            return false;
        }

        if !native_code_helpers_enabled() {
            let models = self
                .blocking_countermodels
                .get(&key)
                .expect("checked above");
            for model in models {
                if model.evaluate(blocking_formula) == Some(true) {
                    self.model_rejections += 1;
                    return true;
                }
            }
            return false;
        }

        // Native helpers may evaluate a wider boolean JIT surface than the
        // trusted-true grammar. For composite arithmetic, native true results
        // are confirmed through the SmallModel oracle before rejecting from the
        // cache, so machine-overflow mismatches fail closed.
        if !native_code_helper_candidate_formula(blocking_formula) {
            let models = self
                .blocking_countermodels
                .get(&key)
                .expect("checked above");
            for model in models {
                if model.evaluate(blocking_formula) == Some(true) {
                    self.model_rejections += 1;
                    return true;
                }
            }
            return false;
        }

        let expr_hash = blocking_formula.structural_hash();

        // Track evaluation count.
        let count = self.jit_eval_counts.entry(expr_hash).or_insert(0);
        *count += 1;
        let eval_count = *count;

        // Try JIT compilation if threshold reached and not yet cached.
        if eval_count >= JIT_COMPILE_THRESHOLD && !self.jit_cache.contains_key(&expr_hash) {
            self.try_jit_compile(expr_hash, blocking_formula);
        }

        // JIT fast path: use compiled evaluator if available.
        // Use a match on jit_cache to determine the path, then drop the borrow
        // before accessing other fields.
        let jit_path = match self.jit_cache.get(&expr_hash) {
            Some(Some(_)) => true, // JIT compiled
            Some(None) => false,   // Not compilable, use interpreter
            None => false,         // Not yet compiled, use interpreter
        };

        if jit_path {
            let mut cached = self
                .jit_cache
                .remove(&expr_hash)
                .expect("checked above")
                .expect("checked above");
            let models = self
                .blocking_countermodels
                .remove(&key)
                .expect("checked above");
            let rejected = self.evaluate_cached_native_helper_over_models(
                &mut cached,
                blocking_formula,
                &models,
            );

            self.blocking_countermodels.insert(key, models);
            self.jit_cache.insert(expr_hash, Some(cached));

            if rejected {
                self.model_rejections += 1;
            }
            return rejected;
        }

        // Interpreter fallback for non-JIT-compilable or below-threshold expressions.
        if matches!(self.jit_cache.get(&expr_hash), Some(None)) {
            self.jit_fallbacks += 1;
        }
        let models = self
            .blocking_countermodels
            .get(&key)
            .expect("checked above");
        for model in models {
            if model.evaluate(blocking_formula) == Some(true) {
                self.model_rejections += 1;
                return true;
            }
        }
        false
    }

    fn evaluate_cached_native_helper_over_models(
        &mut self,
        cached: &mut CachedJitExpr,
        formula: &ChcExpr,
        models: &[SmallModel],
    ) -> bool {
        self.evaluate_cached_scalar_helper_over_models(cached, formula, models)
    }

    fn evaluate_cached_scalar_helper_over_models(
        &mut self,
        cached: &CachedJitExpr,
        formula: &ChcExpr,
        models: &[SmallModel],
    ) -> bool {
        for model in models {
            match self.evaluate_dense_projection(model, cached) {
                DenseProjectionEval::MissingVariable => {
                    // A partial model cannot drive this native projection.
                    // Skipping it is sound: at worst we miss a cache
                    // rejection and fall through to the normal SMT query.
                    // Avoiding interpreter fallback here keeps native
                    // helper mode from adding work on model slices that are
                    // not eligible for the compiled formula.
                }
                DenseProjectionEval::Evaluated(result) => {
                    self.jit_evaluations += 1;
                    if self.handle_native_bool_result(
                        cached.trusted_native_true,
                        formula,
                        model,
                        result,
                    ) {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn handle_native_bool_result(
        &mut self,
        trusted_native_true: bool,
        formula: &ChcExpr,
        model: &SmallModel,
        result: Option<bool>,
    ) -> bool {
        match result {
            Some(true) => {
                if self.accept_native_true(trusted_native_true, formula, model) {
                    self.native_helper_applications += 1;
                    true
                } else {
                    false
                }
            }
            Some(false) => false,
            None => {
                self.jit_deopts += 1;
                self.jit_fallbacks += 1;
                model.evaluate(formula) == Some(true)
            }
        }
    }

    fn evaluate_dense_projection(
        &mut self,
        model: &SmallModel,
        cached: &CachedJitExpr,
    ) -> DenseProjectionEval {
        match self.dense_projection_for_eval(
            model,
            cached.compiled.var_mapping(),
            cached.mapping_id,
        ) {
            DenseProjectionForEval::Complete(vars) => {
                DenseProjectionEval::Evaluated(cached.compiled.evaluate_bool_checked(&vars))
            }
            DenseProjectionForEval::MissingVariable => DenseProjectionEval::MissingVariable,
        }
    }

    fn dense_projection_for_eval(
        &mut self,
        model: &SmallModel,
        mapping: &VarMapping,
        mapping_id: u64,
    ) -> DenseProjectionForEval {
        let key = DenseProjectionCacheKey {
            model_id: model.projection_id,
            mapping_id,
        };

        if !self.dense_projection_cache.contains_key(&key) {
            if self.dense_projection_cache.len() >= MAX_DENSE_PROJECTION_CACHE_ENTRIES {
                self.dense_projection_cache.clear();
            }

            let mut vars = vec![0i64; mapping.total_vars() as usize];
            let projection = if model.fill_var_array(mapping, &mut vars) {
                DenseProjection::Complete(vars)
            } else {
                DenseProjection::MissingVariable
            };
            self.dense_projection_cache.insert(key, projection);
        }

        match self
            .dense_projection_cache
            .get(&key)
            .expect("projection inserted above")
        {
            DenseProjection::Complete(vars) => DenseProjectionForEval::Complete(vars.clone()),
            DenseProjection::MissingVariable => DenseProjectionForEval::MissingVariable,
        }
    }

    fn clear_jit_cache(&mut self) {
        self.jit_cache.clear();
        self.jit_eval_counts.clear();
        self.record_time_native_helper_row_eval_counts.clear();
        self.clear_dense_projection_cache();
        self.dense_projection_mapping_ids.clear();
        self.next_dense_projection_mapping_id = 1;
    }

    fn clear_dense_projection_cache(&mut self) {
        self.dense_projection_cache.clear();
    }

    fn var_mapping_signature(mapping: &VarMapping) -> Box<[(String, u32)]> {
        let mut entries: Vec<_> = mapping
            .iter()
            .map(|(name, idx)| (name.to_string(), *idx))
            .collect();
        entries.sort_by(|(left_name, left_idx), (right_name, right_idx)| {
            left_idx
                .cmp(right_idx)
                .then_with(|| left_name.cmp(right_name))
        });
        entries.into_boxed_slice()
    }

    fn dense_projection_mapping_id(&mut self, mapping: &VarMapping) -> u64 {
        let signature = Self::var_mapping_signature(mapping);
        if let Some(&id) = self.dense_projection_mapping_ids.get(signature.as_ref()) {
            return id;
        }

        let id = self.next_dense_projection_mapping_id;
        self.next_dense_projection_mapping_id =
            self.next_dense_projection_mapping_id.saturating_add(1);
        self.dense_projection_mapping_ids.insert(signature, id);
        id
    }

    fn accept_native_true(
        &mut self,
        trusted_native_true: bool,
        formula: &ChcExpr,
        model: &SmallModel,
    ) -> bool {
        if trusted_native_true {
            self.jit_trusted_true_results += 1;
            return true;
        }

        // The general native evaluator is two-valued and uses machine
        // arithmetic. Confirm non-trusted true cache rejections with the
        // conservative SmallModel evaluator so overflow or other indeterminate
        // cases deopt instead of rejecting.
        self.jit_interpreter_confirmations += 1;
        if model.evaluate(formula) == Some(true) {
            true
        } else {
            self.jit_deopts += 1;
            self.jit_fallbacks += 1;
            false
        }
    }

    fn apply_validated_native_helper_once_with_hash(
        &mut self,
        expr_hash: u64,
        formula: &ChcExpr,
        model: &SmallModel,
    ) -> bool {
        if !self.jit_cache.contains_key(&expr_hash) {
            self.try_jit_compile(expr_hash, formula);
        }

        let native_helper_ready = matches!(self.jit_cache.get(&expr_hash), Some(Some(_)));
        if !native_helper_ready {
            if matches!(self.jit_cache.get(&expr_hash), Some(None)) {
                self.jit_fallbacks += 1;
            }
            return false;
        }

        let cached = self
            .jit_cache
            .remove(&expr_hash)
            .expect("checked above")
            .expect("checked above");

        let mut accepted_native_true = false;
        self.jit_evaluations += 1;
        match self.evaluate_dense_projection(model, &cached) {
            DenseProjectionEval::MissingVariable => {}
            DenseProjectionEval::Evaluated(native_result) => match native_result {
                Some(true) => {
                    if !self.accept_native_true(cached.trusted_native_true, formula, model) {
                        self.jit_cache.insert(expr_hash, Some(cached));
                        return false;
                    }
                    self.native_helper_applications += 1;
                    accepted_native_true = true;
                }
                _ => {
                    self.jit_deopts += 1;
                    self.jit_fallbacks += 1;
                }
            },
        }

        self.jit_cache.insert(expr_hash, Some(cached));
        accepted_native_true
    }

    fn apply_record_time_native_helper_once(
        &mut self,
        key: (usize, usize),
        formula: &ChcExpr,
        model: &SmallModel,
    ) -> bool {
        if !native_code_helper_candidate_formula(formula) {
            return false;
        }
        if !model.covers_jit_formula_vars(formula) {
            return false;
        }

        let expr_hash = formula.structural_hash();

        if !self.jit_cache.contains_key(&expr_hash) {
            let row_eval_count = {
                let count = self
                    .record_time_native_helper_row_eval_counts
                    .entry((key.0, key.1, expr_hash))
                    .or_insert(0);
                *count += 1;
                *count
            };
            if row_eval_count < JIT_COMPILE_THRESHOLD {
                return false;
            }
            self.jit_eval_counts
                .entry(expr_hash)
                .and_modify(|count| *count = (*count).max(row_eval_count))
                .or_insert(row_eval_count);
            if self.record_time_native_helper_compile_admissions
                >= MAX_RECORD_TIME_NATIVE_HELPER_COMPILE_ADMISSIONS
            {
                return false;
            }
            self.record_time_native_helper_compile_admissions += 1;
        }

        self.apply_validated_native_helper_once_with_hash(expr_hash, formula, model)
    }

    fn small_model_from_smt_model(&mut self, model: &FxHashMap<String, SmtValue>) -> SmallModel {
        let projection_id = self.next_model_projection_id;
        self.next_model_projection_id = self.next_model_projection_id.saturating_add(1);
        SmallModel::from_smt_model_with_projection_id(model, projection_id)
    }

    /// Attempt to JIT-compile an expression and cache the result.
    fn try_jit_compile(&mut self, expr_hash: u64, expr: &ChcExpr) {
        self.jit_compile_attempts += 1;
        // Evict if cache is full.
        if self.jit_cache.len() >= MAX_JIT_CACHE_ENTRIES {
            self.clear_jit_cache();
        }

        match compile_expr(expr) {
            Ok(Some(compiled)) => {
                let mapping_id = self.dense_projection_mapping_id(compiled.var_mapping());
                self.jit_compile_successes += 1;
                self.jit_cache.insert(
                    expr_hash,
                    Some(CachedJitExpr {
                        compiled,
                        mapping_id,
                        trusted_native_true: trusted_native_true_formula(expr),
                    }),
                );
            }
            _ => {
                // Not compilable or compilation error: insert None sentinel.
                self.jit_compile_failures += 1;
                self.jit_cache.insert(expr_hash, None);
            }
        }
    }

    /// Snapshot native helper profile counters.
    pub(crate) fn native_code_helper_statistics(&self) -> NativeCodeHelperStatistics {
        NativeCodeHelperStatistics {
            compile_attempts: self.jit_compile_attempts as u64,
            compile_successes: self.jit_compile_successes as u64,
            compile_failures: self.jit_compile_failures as u64,
            evaluations: self.jit_evaluations as u64,
            deopts: self.jit_deopts as u64,
            fallbacks: self.jit_fallbacks as u64,
            missing_var_fallbacks: self.jit_missing_var_fallbacks as u64,
            interpreter_confirmations: self.jit_interpreter_confirmations as u64,
            trusted_true_results: self.jit_trusted_true_results as u64,
            applications: self.native_helper_applications as u64,
        }
    }

    /// Record a countermodel for (predicate, level) from a SAT result.
    /// Evicts all entries when key count exceeds cap (#3077 finding 4).
    pub(crate) fn record_blocking_countermodel(
        &mut self,
        predicate_idx: usize,
        level: usize,
        model: &FxHashMap<String, SmtValue>,
    ) {
        self.record_blocking_countermodel_impl(predicate_idx, level, model, None);
    }

    /// Record a countermodel and run one validated native-helper application.
    ///
    /// A helper-confirmed true result may refresh a saturated cache slot. Any
    /// unsupported expression, missing binding, or oracle mismatch leaves the
    /// solver on the existing cached model fallback path.
    pub(crate) fn record_blocking_countermodel_with_native_helper_validation(
        &mut self,
        predicate_idx: usize,
        level: usize,
        model: &FxHashMap<String, SmtValue>,
        blocking_formula: &ChcExpr,
    ) {
        self.record_blocking_countermodel_impl(predicate_idx, level, model, Some(blocking_formula));
    }

    fn record_blocking_countermodel_impl(
        &mut self,
        predicate_idx: usize,
        level: usize,
        model: &FxHashMap<String, SmtValue>,
        native_helper_formula: Option<&ChcExpr>,
    ) {
        let key = (predicate_idx, level);
        // Evict when key count exceeds cap (same pattern as bounded_cache_insert)
        if self.blocking_countermodels.len() >= MAX_BLOCKING_COUNTERMODEL_KEYS
            && !self.blocking_countermodels.contains_key(&key)
        {
            self.blocking_countermodels.clear();
            // Also clear JIT and dense projection caches since models changed (#8274, #9044).
            self.clear_jit_cache();
        }
        let small_model = self.small_model_from_smt_model(model);

        let saturated_model_slot = self.max_models_per_key > 0
            && self
                .blocking_countermodels
                .get(&key)
                .is_some_and(|models| models.len() >= self.max_models_per_key);

        let accepted_native_true = if saturated_model_slot {
            native_helper_formula
                .filter(|_| native_code_helpers_enabled())
                .is_some_and(|formula| {
                    self.apply_record_time_native_helper_once(key, formula, &small_model)
                })
        } else {
            false
        };

        if self.max_models_per_key > 0 {
            let models = self.blocking_countermodels.entry(key).or_default();
            if models.len() < self.max_models_per_key {
                models.push(small_model);
            } else if accepted_native_true {
                // Keep saturated blocking caches fed with helper-confirmed
                // countermodels instead of letting record-time native work stay
                // telemetry-only. The replacement is conservative: every stored
                // model still came from an SMT SAT result for this exact key, and
                // composite native true results have already been oracle-checked.
                models.rotate_left(1);
                if let Some(slot) = models.last_mut() {
                    *slot = small_model;
                }
            }
        }
        self.solver_calls += 1;
    }
}

/// LAWI-style implication API — test-only until #428 (full LAWI engine) is integrated.
#[cfg(test)]
#[derive(Debug, Clone)]
pub(crate) struct ImplicationCacheStats {
    pub(crate) countermodel_count: usize,
    pub(crate) cache_hits: usize,
    pub(crate) model_rejections: usize,
    pub(crate) solver_calls: usize,
    pub(crate) native_helper_applications: usize,
}

#[cfg(test)]
impl ImplicationCache {
    /// Create cache with custom model limit.
    pub(crate) fn with_max_models(max_models: usize) -> Self {
        Self {
            max_models_per_key: max_models,
            ..Self::new()
        }
    }

    /// Check if implication is cached or rejected by a cached model.
    /// Returns None if solver call is needed.
    pub(crate) fn check_with_hints(
        &mut self,
        antecedent: &ChcExpr,
        consequent: &ChcExpr,
    ) -> Option<ImplicationResult> {
        let ant_hash = antecedent.structural_hash();
        let cons_hash = consequent.structural_hash();
        if let Some(&result) = self.result_cache.get(&(ant_hash, cons_hash)) {
            self.cache_hits += 1;
            return Some(result);
        }
        if let Some(models) = self.implication_countermodels.get(&ant_hash) {
            for model in models {
                if model.evaluate(consequent) == Some(false) {
                    self.model_rejections += 1;
                    self.result_cache
                        .insert((ant_hash, cons_hash), ImplicationResult::Invalid);
                    return Some(ImplicationResult::Invalid);
                }
            }
        }
        None
    }

    /// Record implication result and optionally cache countermodel.
    pub(crate) fn record_result(
        &mut self,
        antecedent: &ChcExpr,
        consequent: &ChcExpr,
        result: ImplicationResult,
        countermodel: Option<&FxHashMap<String, SmtValue>>,
    ) {
        let ant_hash = antecedent.structural_hash();
        let cons_hash = consequent.structural_hash();
        self.solver_calls += 1;
        self.result_cache.insert((ant_hash, cons_hash), result);
        if result == ImplicationResult::Invalid {
            if let Some(model) = countermodel {
                let small_model = self.small_model_from_smt_model(model);
                let models = self.implication_countermodels.entry(ant_hash).or_default();
                if models.len() < self.max_models_per_key {
                    models.push(small_model);
                }
            }
        }
    }

    /// Clear all cached results and models.
    pub(crate) fn clear(&mut self) {
        self.result_cache.clear();
        self.implication_countermodels.clear();
        self.blocking_countermodels.clear();
        self.clear_jit_cache();
        self.next_model_projection_id = 1;
    }

    pub(crate) fn stats(&self) -> ImplicationCacheStats {
        let implication_countermodel_count: usize =
            self.implication_countermodels.values().map(Vec::len).sum();
        let blocking_countermodel_count: usize =
            self.blocking_countermodels.values().map(Vec::len).sum();

        ImplicationCacheStats {
            countermodel_count: implication_countermodel_count + blocking_countermodel_count,
            cache_hits: self.cache_hits,
            model_rejections: self.model_rejections,
            solver_calls: self.solver_calls,
            native_helper_applications: self.native_helper_applications,
        }
    }
}
