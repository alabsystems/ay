// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model and counterexample verification for PDR solver.
//!
//! This module contains methods for verifying that a model satisfies all CHC clauses
//! and that counterexamples are valid.
//!
//! ## Submodules
//!
//! - `model`: Model verification core (verify_model, verify_model_fast, verify_model_impl)
//! - `concrete`: Concrete transition checking (Monte Carlo, exhaustive enumeration)
//! - `mod_div`: Mod/div fallback strategies (ITE case-split, mod-free fragment, mod substitution)
//! - `cex`: Counterexample verification (verify_counterexample)
//! - `transition`: Transition system encoding for reachability checking
//! - `helpers`: Shared helper methods (clause body/head under model, state extraction)

mod cex;
mod cex_entries;
mod cex_query;
mod concrete;
mod helpers;
mod mod_div;
mod model;
mod model_fast;
mod model_inductive;
mod model_inductive_unknown;
mod model_recheck;
mod model_safety;
mod transition;

use crate::expr::evaluate_expr;
use crate::smt::{SmtContext, SmtResult, SmtValue};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

use super::counterexample::Counterexample;
use super::cube;
use super::model::InvariantModel;
use super::model::PredicateInterpretation;
use super::solver::PdrSolver;

/// Query clause info: (predicate_info, invariant_body, bad_state_constraint)
type QueryClauseInfo = (Option<(PredicateId, Vec<ChcExpr>)>, ChcExpr, ChcExpr);

/// Initial SMT timeout for verification queries. Short to avoid getting stuck
/// on mod-heavy or array queries. If the query is mod-free and array-free (pure
/// QF_LIA), the solver retries with `VERIFY_RETRY_TIMEOUT`.
const VERIFY_INITIAL_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(2);

/// Extended SMT timeout for verification retries on pure QF_LIA queries.
///
/// QF_LIA is decidable: the solver MUST return SAT or UNSAT, not UNKNOWN.
/// The previous 10s retry was insufficient for some benchmarks (e.g., dillig03_m
/// verification queries with complex implications). 30s gives the branch-and-bound
/// procedure enough time to complete on realistic verification queries.
///
/// Part of #2472 / #2475: QF_LIA completeness.
const VERIFY_RETRY_TIMEOUT: std::time::Duration = std::time::Duration::from_secs(30);

/// Per-branch timeout for verification-only recursive ITE/OR/DISEQ splitting.
///
/// This is intentionally much smaller than the monolithic QF_LIA retry: case
/// splitting is a fail-closed fallback, so an inconclusive branch must not spend
/// the whole model-validation budget.
const VERIFY_CASE_SPLIT_TIMEOUT: std::time::Duration = std::time::Duration::from_millis(200);

/// Result of counterexample verification.
///
/// Using a tri-state result prevents unsound UNSAFE returns when SMT verification
/// is inconclusive (Unknown). This ensures AY only returns Unsafe when the
/// counterexample is definitively proven valid.
///
/// Soundness fix for #1288.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[non_exhaustive]
pub enum CexVerificationResult {
    /// Counterexample is definitely valid (all SMT checks returned Sat).
    Valid,
    /// Counterexample is definitely spurious (some SMT check returned Unsat).
    Spurious,
    /// Verification inconclusive (some SMT check returned Unknown).
    Unknown,
}

fn sort_from_smt_value(value: &SmtValue) -> ChcSort {
    match value {
        SmtValue::Bool(_) => ChcSort::Bool,
        SmtValue::Int(_) | SmtValue::BigInt(_) => ChcSort::Int,
        SmtValue::Real(_) => ChcSort::Real,
        SmtValue::BitVec(_, w) | SmtValue::BigBitVec(_, w) => ChcSort::BitVec(*w),
        SmtValue::Opaque(_) => ChcSort::Int,
        SmtValue::ConstArray(default) => {
            let val_sort = sort_from_smt_value(default);
            ChcSort::Array(Box::new(ChcSort::Int), Box::new(val_sort))
        }
        SmtValue::ArrayMap { default, entries } => {
            let val_sort = sort_from_smt_value(default);
            let idx_sort = entries
                .first()
                .map(|(k, _)| sort_from_smt_value(k))
                .unwrap_or(ChcSort::Int);
            ChcSort::Array(Box::new(idx_sort), Box::new(val_sort))
        }
        // DT sort info not stored in SmtValue; use uninterpreted as placeholder.
        SmtValue::Datatype(ctor, _) => ChcSort::Uninterpreted(ctor.clone()),
    }
}

fn canonical_datatype_field_sort(
    parent_sort: &ChcSort,
    ctor: &str,
    field_index: usize,
) -> Option<ChcSort> {
    let ChcSort::Datatype {
        name: parent_name,
        constructors,
    } = parent_sort
    else {
        return None;
    };
    let field_sort = constructors
        .iter()
        .find(|c| c.name == ctor)
        .and_then(|c| c.selectors.get(field_index))
        .map(|sel| sel.sort.clone())?;

    match &field_sort {
        ChcSort::Uninterpreted(name) | ChcSort::Datatype { name, .. } if name == parent_name => {
            Some(parent_sort.clone())
        }
        _ => Some(field_sort),
    }
}

fn smt_value_to_chc_expr_for_sort(value: &SmtValue, expected_sort: &ChcSort) -> Option<ChcExpr> {
    Some(match (expected_sort, value) {
        (ChcSort::Bool, SmtValue::Bool(value)) => ChcExpr::Bool(*value),
        (ChcSort::Int, SmtValue::Int(value)) => ChcExpr::Int(*value),
        (ChcSort::Int, SmtValue::BigInt(value)) => ChcExpr::from_bigint(value.as_ref().clone()),
        (ChcSort::Real, SmtValue::Real(value)) => {
            use num_traits::ToPrimitive;
            ChcExpr::Real(value.numer().to_i64()?, value.denom().to_i64()?)
        }
        (ChcSort::BitVec(width), SmtValue::Int(n)) => {
            SmtValue::bitvec_from_bigint((*n).into(), *width).bitvec_to_chc_expr()?
        }
        (ChcSort::BitVec(width), SmtValue::BigInt(n)) => {
            SmtValue::bitvec_from_bigint(n.as_ref().clone(), *width).bitvec_to_chc_expr()?
        }
        (
            ChcSort::BitVec(expected_width),
            value @ (SmtValue::BitVec(_, actual_width) | SmtValue::BigBitVec(_, actual_width)),
        ) if expected_width == actual_width => value.bitvec_to_chc_expr()?,
        (ChcSort::Array(index_sort, element_sort), SmtValue::ConstArray(default)) => {
            ChcExpr::ConstArray(
                index_sort.as_ref().clone(),
                Arc::new(smt_value_to_chc_expr_for_sort(
                    default,
                    element_sort.as_ref(),
                )?),
            )
        }
        (ChcSort::Array(index_sort, element_sort), SmtValue::ArrayMap { default, entries }) => {
            let mut arr = ChcExpr::ConstArray(
                index_sort.as_ref().clone(),
                Arc::new(smt_value_to_chc_expr_for_sort(
                    default,
                    element_sort.as_ref(),
                )?),
            );
            for (idx, val) in entries {
                arr = ChcExpr::store(
                    arr,
                    smt_value_to_chc_expr_for_sort(idx, index_sort.as_ref())?,
                    smt_value_to_chc_expr_for_sort(val, element_sort.as_ref())?,
                );
            }
            arr
        }
        // DT constructor: use expected sort for correct ChcSort::Datatype
        // instead of Uninterpreted placeholder. Recurse with field sorts from
        // the constructor definition when available (#7045 Gap B).
        (ChcSort::Datatype { constructors, .. }, SmtValue::Datatype(ctor, fields)) => {
            let constructor = constructors
                .iter()
                .find(|candidate| candidate.name == *ctor)?;
            if constructor.selectors.len() != fields.len() {
                return None;
            }
            let field_exprs: Vec<Arc<ChcExpr>> = fields
                .iter()
                .enumerate()
                .map(|(i, f)| -> Option<Arc<ChcExpr>> {
                    let field_sort = canonical_datatype_field_sort(expected_sort, ctor, i)?;
                    let expr = smt_value_to_chc_expr_for_sort(f, &field_sort)?;
                    Some(Arc::new(expr))
                })
                .collect::<Option<_>>()?;
            ChcExpr::FuncApp(ctor.clone(), expected_sort.clone(), field_exprs)
        }
        (_, SmtValue::Opaque(name)) => {
            ChcExpr::var(ChcVar::new(name.clone(), expected_sort.clone()))
        }
        _ => return None,
    })
}

/// Build a substitution pair from a variable name and SMT value.
///
/// When `declared_sort` is provided, the `ChcVar` uses that sort instead of
/// inferring from `value`. This is critical for BV-to-Int abstraction: the
/// SmtValue may be `Int` but the predicate declares the argument as `BitVec(w)`.
/// Since `ChcVar` equality includes sort, a sort mismatch causes substitution
/// lookups to silently fail (#6249).
fn instance_subst_var_and_value(
    name: &str,
    value: &SmtValue,
    declared_sort: Option<&ChcSort>,
    _verbose: bool,
    saw_unknown: &mut bool,
) -> (ChcVar, ChcExpr) {
    let sort = declared_sort
        .cloned()
        .unwrap_or_else(|| sort_from_smt_value(value));
    if matches!(value, SmtValue::Opaque(_)) {
        *saw_unknown = true;
    }
    if matches!(sort, ChcSort::Array(_, _)) && smt_value_contains_opaque(value) {
        *saw_unknown = true;
    }
    let var = ChcVar::new(name.to_owned(), sort.clone());
    let expr = smt_value_to_chc_expr_for_sort(value, &sort).unwrap_or_else(|| {
        // Leave the variable unconcretized and force the enclosing replay to
        // return Unknown. This is fail-closed for a hostile/out-of-range model
        // width and avoids either a panic or a fabricated zero assignment.
        *saw_unknown = true;
        ChcExpr::var(var.clone())
    });
    (var, expr)
}

fn smt_value_contains_opaque(value: &SmtValue) -> bool {
    match value {
        SmtValue::Opaque(_) => true,
        SmtValue::ConstArray(default) => smt_value_contains_opaque(default),
        SmtValue::ArrayMap { default, entries } => {
            smt_value_contains_opaque(default)
                || entries.iter().any(|(idx, val)| {
                    smt_value_contains_opaque(idx) || smt_value_contains_opaque(val)
                })
        }
        SmtValue::Datatype(_, fields) => fields.iter().any(smt_value_contains_opaque),
        SmtValue::Bool(_)
        | SmtValue::Int(_)
        | SmtValue::BigInt(_)
        | SmtValue::Real(_)
        | SmtValue::BitVec(_, _)
        | SmtValue::BigBitVec(_, _) => false,
    }
}

/// Decide a counterexample replay query by direct ground evaluation (FM2b).
///
/// Replay queries are conjunctions of `var = ground-value` bindings (witness
/// instances) plus instantiated clause constraints over those same variables.
/// When the bindings pin every variable, the query is decidable by
/// substitution + concrete evaluation: `true` means the bindings themselves
/// are a satisfying witness.
///
/// Used to cross-check backend UNSAT results on array-bearing replays: the
/// array extensionality fragment can produce false UNSATs on ground
/// const-array/store disequalities (heap__swaparray-class cex rejections,
/// where every engine found Unsafe but validation replied "spurious").
/// Overriding an UNSAT with a concretely evaluated witness is sound — ground
/// evaluation is a decision procedure for variable-free formulas.
///
/// Returns `false` (no override) when bindings are absent, variables remain
/// after substitution, or evaluation is indeterminate.
fn ground_query_witness_evaluates_true(query: &ChcExpr) -> bool {
    let conjuncts = query.collect_conjuncts();
    let mut bindings: Vec<(ChcVar, ChcExpr)> = Vec::new();
    for conjunct in &conjuncts {
        let ChcExpr::Op(ChcOp::Eq, args) = conjunct else {
            continue;
        };
        if args.len() != 2 {
            continue;
        }
        let (var, value) = match (args[0].as_ref(), args[1].as_ref()) {
            (ChcExpr::Var(var), value) if value.vars().is_empty() => (var, value),
            (value, ChcExpr::Var(var)) if value.vars().is_empty() => (var, value),
            _ => continue,
        };
        // First binding wins; a conflicting duplicate becomes a ground
        // disequality after substitution and evaluation returns false.
        if !bindings.iter().any(|(bound, _)| bound.name == var.name) {
            bindings.push((var.clone(), value.clone()));
        }
    }
    // No bail-out on empty bindings: the query may already be fully ground
    // (instances substituted upstream), in which case direct evaluation
    // decides it without any bindings.
    let ground = query
        .substitute(&bindings)
        .simplify_array_ops()
        .simplify_constants()
        .simplify_array_ops()
        .simplify_constants();
    matches!(
        evaluate_expr(&ground, &FxHashMap::default()),
        Some(SmtValue::Bool(true))
    )
}

/// Whether a witness-instance key is a canonical predicate-argument name
/// (`__p{pred}_a{arg}`).
///
/// Engine models leak clause-local variable names (e.g. `E`, `I`, `v_9`) into
/// witness instances. On the problem the witness was produced for those keys
/// are meaningful, but when a transform-space witness is replayed against the
/// ORIGINAL clauses (FM2b re-resolution) they collide with original clause
/// variables that have entirely different positional meanings. Re-resolved
/// replays therefore restrict substitutions to canonical names, which are
/// positional and transform-stable (after predicate-id remapping).
fn is_canonical_arg_name(name: &str) -> bool {
    let Some(rest) = name.strip_prefix("__p") else {
        return false;
    };
    let Some((pred_idx, arg_idx)) = rest.split_once("_a") else {
        return false;
    };
    !pred_idx.is_empty()
        && pred_idx.bytes().all(|b| b.is_ascii_digit())
        && !arg_idx.is_empty()
        && arg_idx.bytes().all(|b| b.is_ascii_digit())
}

fn ground_exprs_semantically_equal(lhs: &ChcExpr, rhs: &ChcExpr) -> Option<bool> {
    let equality = ChcExpr::eq(lhs.clone(), rhs.clone())
        .simplify_array_ops()
        .simplify_constants();
    match evaluate_expr(&equality, &FxHashMap::default()) {
        Some(SmtValue::Bool(value)) => Some(value),
        _ => None,
    }
}

fn array_sat_cross_check_result(
    smt: &mut SmtContext,
    query: &ChcExpr,
    verbose: bool,
    context: &str,
) -> Option<CexVerificationResult> {
    if !query.contains_array_ops() {
        return None;
    }

    let simplified = query
        .simplify_array_ops()
        .simplify_constants()
        .simplify_array_ops()
        .simplify_constants();
    match evaluate_expr(&simplified, &FxHashMap::default()) {
        Some(SmtValue::Bool(true)) => return None,
        Some(SmtValue::Bool(false)) => {
            if verbose {
                safe_eprintln!(
                    "PDR: Counterexample verification failed at {context}: \
                    concrete array evaluation returned false"
                );
            }
            return Some(CexVerificationResult::Spurious);
        }
        _ => {}
    }
    if !simplified.contains_array_ops() {
        return None;
    }

    let propagated = FxHashMap::default();
    match smt.check_sat_via_executor(&simplified, &propagated, VERIFY_INITIAL_TIMEOUT) {
        SmtResult::Sat(_) => None,
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
            // FM2b: the executor's array extensionality fragment can produce
            // false UNSATs on ground const-array/store disequalities; a
            // concretely evaluated witness is a sound override.
            if ground_query_witness_evaluates_true(&simplified) {
                return None;
            }
            if verbose {
                safe_eprintln!(
                    "PDR: Counterexample verification failed at {context}: \
                    array SAT cross-check returned UNSAT"
                );
            }
            Some(CexVerificationResult::Spurious)
        }
        SmtResult::Unknown => {
            if verbose {
                safe_eprintln!(
                    "PDR: Counterexample verification inconclusive at {context}: \
                    array SAT cross-check returned Unknown"
                );
            }
            Some(CexVerificationResult::Unknown)
        }
    }
}

#[cfg(test)]
mod ground_witness_eval_tests;

#[cfg(test)]
mod array_cross_check_tests {
    use super::*;

    #[test]
    fn accepts_ground_query_when_array_normalization_removes_array_ops() {
        let array = ChcExpr::store(
            ChcExpr::const_array(ChcSort::Int, ChcExpr::Int(0)),
            ChcExpr::Int(1),
            ChcExpr::Int(2),
        );
        let array_ok = ChcExpr::eq(ChcExpr::select(array, ChcExpr::Int(1)), ChcExpr::Int(2));
        let overflow_for_concrete_evaluator = ChcExpr::le(
            ChcExpr::Int(0),
            ChcExpr::mul(ChcExpr::Int(4_000_000_000), ChcExpr::Int(4_000_000_000)),
        );
        let query = ChcExpr::and(array_ok, overflow_for_concrete_evaluator);
        let mut smt = SmtContext::new();

        assert_eq!(
            array_sat_cross_check_result(&mut smt, &query, false, "test"),
            None
        );
    }
}

#[cfg(test)]
mod case_split_budget_tests {
    use super::*;

    /// `try_verification_case_split` must bound the WHOLE split by `timeout`,
    /// not just each check inside it.
    ///
    /// `smt.scoped_check_timeout` is a PER-CHECK bound, and
    /// `check_sat_with_ite_case_split` issues one check per leaf, so without a
    /// wall-clock deadline the bound multiplies by the leaf count. Measured on
    /// the extra-small-lia corpus at a 20 s adaptive budget before the fix:
    /// 7 of 250 calls ran past their `timeout`, worst 680 ms against 200 ms.
    /// Every caller derives `timeout` from the remainder of the enclosing
    /// per-clause verification budget, so the multiplier is exactly how that
    /// budget is exceeded.
    ///
    /// The recursion already polls the thread SMT deadline; this asserts the
    /// deadline is ARMED, which is what makes those polls enforce `timeout`.
    #[test]
    fn verification_case_split_arms_the_thread_smt_deadline() {
        let x = ChcVar::new("x", ChcSort::Int);
        // ITE-bearing so the recursion actually runs (and so the pre-split
        // reaches `check_sat_with_ite_case_split_recursive`, where the
        // observation is recorded).
        let query = ChcExpr::eq(
            ChcExpr::var(x.clone()),
            ChcExpr::ite(
                ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(0)),
                ChcExpr::Int(1),
                ChcExpr::Int(2),
            ),
        );
        let mut smt = SmtContext::new();
        let timeout = std::time::Duration::from_millis(250);

        assert!(
            crate::smt::deadline::smt_deadline_remaining().is_none(),
            "test must start with no ambient thread SMT deadline"
        );
        PdrSolver::reset_case_split_deadline_observation_for_tests();
        let _ = PdrSolver::try_verification_case_split(&mut smt, false, &query, timeout);

        let observed = PdrSolver::observed_case_split_deadline_for_tests()
            .expect("case-split recursion must run under a thread SMT deadline");
        assert!(
            observed <= timeout,
            "thread SMT deadline inside the split must not exceed the requested \
             {timeout:?}; observed {observed:?}"
        );
        assert!(
            crate::smt::deadline::smt_deadline_remaining().is_none(),
            "the split's deadline scope must be released when it returns"
        );
    }
}

#[cfg(test)]
#[path = "../verification_tests/mod.rs"]
#[allow(clippy::unwrap_used)]
mod tests;
