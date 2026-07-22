// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::conjoin;
use crate::expr::{maybe_grow_expr_stack, MAX_EXPR_RECURSION_DEPTH};
use crate::pdr::cube::is_trivial_contradiction;
use crate::pdr::model::InvariantModel;
use crate::smt::{SmtContext, SmtResult};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseHead, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::time::Instant;
use std::time::Duration;

/// Per-query SMT timeout used during algebraic validation.
///
/// Clauses with nonlinear constraints (modular arithmetic, multiplication)
/// can cause LRA/NIA dual simplex loops that exceed any reasonable budget.
/// Capping each check at 500 ms forces Unknown on hard queries so the
/// outer deadline check in the validation loop can preempt synthesis.
///
/// Part of #8753.
const ALGEBRAIC_QUERY_TIMEOUT: Duration = Duration::from_millis(500);

/// Result of algebraic model validation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum AlgebraicValidationResult {
    /// Model is valid: all clauses satisfied.
    Valid,
    /// Model is invalid but concrete evaluation proved the system is UNSAFE:
    /// the algebraically-derived invariant admits bad states.
    #[allow(dead_code)]
    // Retained for future original-trace-validated recurrence UNSAFE results.
    UnsafeDetected,
    /// Model is invalid for other reasons.
    Invalid,
    /// Validation bailed out because the outer deadline elapsed (#8753).
    /// The caller should treat this as `NotApplicable` so the portfolio can
    /// proceed to the next engine (PDR/IMC/TPA/LAWI).
    DeadlineExceeded,
}

/// Original-clause validation counters for the algebraic pre-strategy.
///
/// These mirror the PDR affine firewall counters, but are collected in the
/// algebraic pre-strategy before a PDR solver exists.
///
/// The field names are retained for telemetry compatibility with the earlier
/// Sally/LRA guard, but as of #9402 they count all algebraic original-clause
/// validation. `unknowns` means an SMT `Unknown` was demoted instead of being
/// accepted as implication success.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct AlgebraicValidationStats {
    pub(crate) lra_affine_original_clause_validation_attempts: u64,
    pub(crate) lra_affine_original_clause_validation_queries: u64,
    pub(crate) lra_affine_original_clause_validation_successes: u64,
    pub(crate) lra_affine_original_clause_validation_failures: u64,
    pub(crate) lra_affine_original_clause_validation_unknowns: u64,
    /// Profile-only accelerated-summary candidate count for modular predicate-chain summaries.
    ///
    /// These candidates are never accepted directly from synthesis. They only
    /// influence an answer if the complete algebraic model is accepted by the
    /// existing original-clause validator.
    pub(crate) accelerated_summary_modular_chain_summary_candidates: u64,
    pub(crate) accelerated_summary_modular_chain_family_summary_candidates: u64,
}

impl AlgebraicValidationStats {
    pub(crate) fn merge(&mut self, other: &Self) {
        self.lra_affine_original_clause_validation_attempts = self
            .lra_affine_original_clause_validation_attempts
            .saturating_add(other.lra_affine_original_clause_validation_attempts);
        self.lra_affine_original_clause_validation_queries = self
            .lra_affine_original_clause_validation_queries
            .saturating_add(other.lra_affine_original_clause_validation_queries);
        self.lra_affine_original_clause_validation_successes = self
            .lra_affine_original_clause_validation_successes
            .saturating_add(other.lra_affine_original_clause_validation_successes);
        self.lra_affine_original_clause_validation_failures = self
            .lra_affine_original_clause_validation_failures
            .saturating_add(other.lra_affine_original_clause_validation_failures);
        self.lra_affine_original_clause_validation_unknowns = self
            .lra_affine_original_clause_validation_unknowns
            .saturating_add(other.lra_affine_original_clause_validation_unknowns);
        self.accelerated_summary_modular_chain_summary_candidates = self
            .accelerated_summary_modular_chain_summary_candidates
            .saturating_add(other.accelerated_summary_modular_chain_summary_candidates);
        self.accelerated_summary_modular_chain_family_summary_candidates = self
            .accelerated_summary_modular_chain_family_summary_candidates
            .saturating_add(other.accelerated_summary_modular_chain_family_summary_candidates);
    }

    fn record_attempt(&mut self) {
        self.lra_affine_original_clause_validation_attempts = self
            .lra_affine_original_clause_validation_attempts
            .saturating_add(1);
    }

    fn record_query(&mut self) {
        self.lra_affine_original_clause_validation_queries = self
            .lra_affine_original_clause_validation_queries
            .saturating_add(1);
    }

    fn record_success(&mut self) {
        self.lra_affine_original_clause_validation_successes = self
            .lra_affine_original_clause_validation_successes
            .saturating_add(1);
    }

    fn record_failure(&mut self) {
        self.lra_affine_original_clause_validation_failures = self
            .lra_affine_original_clause_validation_failures
            .saturating_add(1);
    }

    fn record_unknown(&mut self) {
        self.lra_affine_original_clause_validation_unknowns = self
            .lra_affine_original_clause_validation_unknowns
            .saturating_add(1);
    }

    pub(super) fn record_accelerated_summary_modular_chain_summary_candidate(&mut self) {
        self.accelerated_summary_modular_chain_summary_candidates = self
            .accelerated_summary_modular_chain_summary_candidates
            .saturating_add(1);
        self.accelerated_summary_modular_chain_family_summary_candidates = self
            .accelerated_summary_modular_chain_family_summary_candidates
            .saturating_add(1);
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ValidationInterval {
    lower: Option<i128>,
    upper: Option<i128>,
}

impl ValidationInterval {
    fn top() -> Self {
        Self {
            lower: None,
            upper: None,
        }
    }

    fn exact(value: i128) -> Self {
        Self {
            lower: Some(value),
            upper: Some(value),
        }
    }

    fn lower(value: i128) -> Self {
        Self {
            lower: Some(value),
            upper: None,
        }
    }

    fn upper(value: i128) -> Self {
        Self {
            lower: None,
            upper: Some(value),
        }
    }

    fn has_bound(self) -> bool {
        self.lower.is_some() || self.upper.is_some()
    }

    fn is_empty(self) -> bool {
        matches!((self.lower, self.upper), (Some(lower), Some(upper)) if lower > upper)
    }

    fn intersect(self, other: Self) -> Self {
        Self {
            lower: match (self.lower, other.lower) {
                (Some(a), Some(b)) => Some(a.max(b)),
                (Some(a), None) | (None, Some(a)) => Some(a),
                (None, None) => None,
            },
            upper: match (self.upper, other.upper) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (Some(a), None) | (None, Some(a)) => Some(a),
                (None, None) => None,
            },
        }
    }

    fn checked_add(self, other: Self) -> Self {
        Self {
            lower: match (self.lower, other.lower) {
                (Some(a), Some(b)) => a.checked_add(b),
                _ => None,
            },
            upper: match (self.upper, other.upper) {
                (Some(a), Some(b)) => a.checked_add(b),
                _ => None,
            },
        }
    }

    fn checked_neg(self) -> Self {
        Self {
            lower: self.upper.and_then(i128::checked_neg),
            upper: self.lower.and_then(i128::checked_neg),
        }
    }

    fn checked_sub(self, other: Self) -> Self {
        self.checked_add(other.checked_neg())
    }

    fn checked_scale(self, factor: i128) -> Self {
        if factor == 0 {
            return Self::exact(0);
        }
        let lower = self.lower.and_then(|value| value.checked_mul(factor));
        let upper = self.upper.and_then(|value| value.checked_mul(factor));
        if factor > 0 {
            Self { lower, upper }
        } else {
            Self {
                lower: upper,
                upper: lower,
            }
        }
    }
}

fn validation_formula_proves_unsat(formula: &ChcExpr) -> bool {
    let raw_conjuncts: Vec<ChcExpr> = formula.conjuncts().into_iter().cloned().collect();
    if bool_encoded_exclusions_are_syntactically_unsat(&raw_conjuncts) {
        return true;
    }

    let simplified = formula.simplify_constants();
    if matches!(simplified, ChcExpr::Bool(false)) || is_trivial_contradiction(&simplified) {
        return true;
    }

    let conjuncts: Vec<ChcExpr> = simplified.conjuncts().into_iter().cloned().collect();
    if active_diff_query_formula_is_syntactically_unsat(&conjuncts) {
        return true;
    }
    if bool_encoded_exclusions_are_syntactically_unsat(&conjuncts) {
        return true;
    }

    let mut int_env = FxHashMap::default();
    if !collect_validation_interval_bounds(&conjuncts, &mut int_env) {
        return true;
    }
    let Some(residue_env) = collect_validation_mod_residues(&conjuncts) else {
        return true;
    };
    if !refine_validation_intervals_with_residues(&mut int_env, &residue_env) {
        return true;
    }

    let Some(bool_env) = collect_validation_bool_assignments(&conjuncts) else {
        return true;
    };

    conjuncts.iter().any(|conjunct| {
        matches!(
            validation_bool_result(conjunct, &int_env, &bool_env, &residue_env),
            Some(false)
        )
    })
}

#[derive(Default)]
struct ActiveDiffContradictions {
    diff_guards: FxHashSet<String>,
    positive_epsilons: FxHashSet<String>,
}

fn active_diff_query_formula_is_syntactically_unsat(conjuncts: &[ChcExpr]) -> bool {
    let mut facts = ActiveDiffContradictions::default();
    for conjunct in conjuncts {
        if let Some((active_a, active_b, epsilon, value_a, value_b)) =
            parse_active_diff_invariant_clause(conjunct)
        {
            facts.diff_guards.insert(active_diff_fact_key(
                &active_a, &active_b, &epsilon, &value_a, &value_b,
            ));
            continue;
        }
        if let Some(epsilon) = parse_positive_epsilon_fact(conjunct) {
            facts.positive_epsilons.insert(epsilon.name);
        }
    }

    if facts.diff_guards.is_empty() && facts.positive_epsilons.is_empty() {
        return false;
    }

    conjuncts
        .iter()
        .any(|conjunct| active_diff_query_expr_is_unsat(conjunct, &mut Vec::new(), &facts))
}

fn bool_encoded_exclusions_are_syntactically_unsat(conjuncts: &[ChcExpr]) -> bool {
    let mut facts: FxHashMap<String, BoolEncodedDomainFacts> = FxHashMap::default();
    for conjunct in conjuncts {
        if let Some((key, value)) = bool_encoded_equality_key(conjunct) {
            let entry = facts.entry(key).or_default();
            if entry.required.is_some_and(|old| old != value) {
                return true;
            }
            entry.required = Some(value);
            if entry.excluded & bool_encoded_value_bit(value) != 0 {
                return true;
            }
        }
        if let Some((key, value)) = bool_encoded_exclusion_key(conjunct) {
            let bit = bool_encoded_value_bit(value);
            let entry = facts.entry(key).or_default();
            entry.excluded |= bit;
            if entry.required == Some(value) || entry.excluded == 0b11 {
                return true;
            }
        }
    }
    false
}

#[derive(Default)]
struct BoolEncodedDomainFacts {
    required: Option<i64>,
    excluded: u8,
}

fn bool_encoded_value_bit(value: i64) -> u8 {
    match value {
        0 => 0b01,
        1 => 0b10,
        _ => 0,
    }
}

fn bool_encoded_equality_key(expr: &ChcExpr) -> Option<(String, i64)> {
    if let Some(key) = bool_encoded_equality_key_raw(expr) {
        return Some(key);
    }
    let simplified = expr.simplify_constants();
    bool_encoded_equality_key_raw(&simplified)
}

fn bool_encoded_equality_key_raw(expr: &ChcExpr) -> Option<(String, i64)> {
    match expr {
        ChcExpr::Op(ChcOp::Eq, eq_args) => bool_encoded_eq_key(eq_args),
        _ => None,
    }
}

fn bool_encoded_eq_key(args: &[std::sync::Arc<ChcExpr>]) -> Option<(String, i64)> {
    if args.len() != 2 {
        return None;
    }
    if let Some(value @ (0 | 1)) = args[1].as_i64() {
        if validation_expr_has_bool_domain(args[0].as_ref()) {
            return Some((validation_expr_key(args[0].as_ref()), value));
        }
    }
    if let Some(value @ (0 | 1)) = args[0].as_i64() {
        if validation_expr_has_bool_domain(args[1].as_ref()) {
            return Some((validation_expr_key(args[1].as_ref()), value));
        }
    }
    None
}

fn bool_encoded_exclusion_key(expr: &ChcExpr) -> Option<(String, i64)> {
    if let Some(key) = bool_encoded_exclusion_key_raw(expr) {
        return Some(key);
    }
    let simplified = expr.simplify_constants();
    bool_encoded_exclusion_key_raw(&simplified)
}

fn bool_encoded_exclusion_key_raw(expr: &ChcExpr) -> Option<(String, i64)> {
    match expr {
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            let ChcExpr::Op(ChcOp::Eq, eq_args) = args[0].as_ref() else {
                return None;
            };
            bool_encoded_neq_key(eq_args)
        }
        ChcExpr::Op(ChcOp::Ne, args) => bool_encoded_neq_key(args),
        _ => None,
    }
}

fn bool_encoded_neq_key(args: &[std::sync::Arc<ChcExpr>]) -> Option<(String, i64)> {
    if args.len() != 2 {
        return None;
    }
    if let Some(value @ (0 | 1)) = args[1].as_i64() {
        if validation_expr_has_bool_domain(args[0].as_ref()) {
            return Some((validation_expr_key(args[0].as_ref()), value));
        }
    }
    if let Some(value @ (0 | 1)) = args[0].as_i64() {
        if validation_expr_has_bool_domain(args[1].as_ref()) {
            return Some((validation_expr_key(args[1].as_ref()), value));
        }
    }
    None
}

fn validation_expr_has_bool_domain(expr: &ChcExpr) -> bool {
    if validation_expr_has_bool_domain_raw(expr) {
        return true;
    }
    let simplified = expr.simplify_constants();
    validation_expr_key(&simplified) != validation_expr_key(expr)
        && validation_expr_has_bool_domain_raw(&simplified)
}

fn validation_expr_has_bool_domain_raw(expr: &ChcExpr) -> bool {
    if let Some((payload, width)) = signed_bv_to_int_payload_and_width(expr) {
        return width > 1 && validation_expr_has_bool_domain(payload);
    }
    if let Some((payload, _)) = unsigned_bv_to_int_payload(expr) {
        return validation_expr_has_bool_domain(payload);
    }
    match expr {
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            matches!(
                (args[1].as_i64(), args[2].as_i64()),
                (Some(0), Some(1)) | (Some(1), Some(0))
            ) || bool_bitvec_ite_payload(expr).is_some()
        }
        ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
            eval_validation_nonnegative_const_u128(args[1].as_ref(), 0)
                .is_some_and(|modulus| modulus > 1)
                && validation_expr_has_bool_domain(args[0].as_ref())
        }
        _ => false,
    }
}

fn active_diff_query_expr_is_unsat(
    expr: &ChcExpr,
    active_context: &mut Vec<ChcVar>,
    facts: &ActiveDiffContradictions,
) -> bool {
    if matches!(expr, ChcExpr::Bool(false)) {
        return true;
    }
    if matches!(expr, ChcExpr::Bool(true)) {
        return false;
    }
    if let Some(epsilon) = parse_epsilon_nonpositive_guard(expr) {
        return facts.positive_epsilons.contains(&epsilon.name);
    }
    if let Some((epsilon, value_a, value_b)) = parse_epsilon_distance_guard(expr) {
        return active_context.iter().enumerate().any(|(idx, active_a)| {
            active_context.iter().skip(idx + 1).any(|active_b| {
                facts.diff_guards.contains(&active_diff_fact_key(
                    active_a, active_b, &epsilon, &value_a, &value_b,
                ))
            })
        });
    }

    let ChcExpr::Op(op, args) = expr else {
        return false;
    };
    match op {
        ChcOp::And => {
            let original_len = active_context.len();
            for arg in args {
                if let Some(var) = positive_validation_bool_var(arg) {
                    if !active_context.iter().any(|active| active.name == var.name) {
                        active_context.push(var);
                    }
                }
            }
            let unsat = args
                .iter()
                .any(|arg| active_diff_query_expr_is_unsat(arg, active_context, facts));
            active_context.truncate(original_len);
            unsat
        }
        ChcOp::Or => {
            !args.is_empty()
                && args
                    .iter()
                    .all(|arg| active_diff_query_expr_is_unsat(arg, active_context, facts))
        }
        _ => false,
    }
}

fn active_diff_fact_key(
    active_a: &ChcVar,
    active_b: &ChcVar,
    epsilon: &ChcVar,
    value_a: &ChcVar,
    value_b: &ChcVar,
) -> String {
    let (left_active, right_active) = if active_a.name <= active_b.name {
        (&active_a.name, &active_b.name)
    } else {
        (&active_b.name, &active_a.name)
    };
    format!(
        "{left_active}|{right_active}|{}|{}|{}",
        epsilon.name, value_a.name, value_b.name
    )
}

fn positive_validation_bool_var(expr: &ChcExpr) -> Option<ChcVar> {
    match expr {
        ChcExpr::Var(var) if matches!(var.sort, ChcSort::Bool) => Some(var.clone()),
        _ => None,
    }
}

fn parse_positive_epsilon_fact(expr: &ChcExpr) -> Option<ChcVar> {
    let ChcExpr::Op(ChcOp::Not, args) = expr else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    parse_epsilon_nonpositive_guard(args[0].as_ref())
}

fn parse_epsilon_nonpositive_guard(expr: &ChcExpr) -> Option<ChcVar> {
    let ChcExpr::Op(ChcOp::Le, args) = expr else {
        return None;
    };
    if args.len() != 2 || !is_validation_zero(args[1].as_ref()) {
        return None;
    }
    let ChcExpr::Var(epsilon) = args[0].as_ref() else {
        return None;
    };
    if matches!(epsilon.sort, ChcSort::Real | ChcSort::Int) {
        Some(epsilon.clone())
    } else {
        None
    }
}

fn is_validation_zero(expr: &ChcExpr) -> bool {
    matches!(expr, ChcExpr::Int(0) | ChcExpr::Real(0, 1))
}

fn collect_validation_interval_bounds(
    conjuncts: &[ChcExpr],
    env: &mut FxHashMap<String, ValidationInterval>,
) -> bool {
    let max_rounds = conjuncts.len().saturating_add(4).clamp(1, 32);
    for _ in 0..max_rounds {
        let before = env.clone();
        for conjunct in conjuncts {
            if !collect_validation_interval_bound(conjunct, env) {
                return false;
            }
        }
        for conjunct in conjuncts {
            if !propagate_validation_var_bound(conjunct, env) {
                return false;
            }
        }
        for conjunct in conjuncts {
            if !propagate_validation_linear_bound(conjunct, env) {
                return false;
            }
        }
        for conjunct in conjuncts {
            if !propagate_validation_implication_bound(conjunct, env) {
                return false;
            }
        }
        if *env == before {
            return true;
        }
    }
    true
}

fn collect_validation_interval_bound(
    conjunct: &ChcExpr,
    env: &mut FxHashMap<String, ValidationInterval>,
) -> bool {
    let simplified = conjunct.simplify_constants();
    if let Some((op, lhs, rhs)) = validation_interval_atom(&simplified) {
        return collect_validation_direct_bound(op, lhs, rhs, env);
    }
    if let ChcExpr::Op(ChcOp::Not, args) = &simplified {
        if args.len() == 1 {
            if let Some((op, lhs, rhs)) = validation_interval_atom(args[0].as_ref()) {
                return collect_validation_direct_bound(
                    negated_validation_comparison(op),
                    lhs,
                    rhs,
                    env,
                );
            }
        }
    }
    true
}

fn collect_validation_direct_bound(
    op: ChcOp,
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    env: &mut FxHashMap<String, ValidationInterval>,
) -> bool {
    match op {
        ChcOp::Eq => {
            if let (Some((name, coeff, offset)), Some(value)) =
                (validation_single_var_affine(lhs), rhs.as_i128())
            {
                if let Some(interval) = validation_affine_exact_interval(coeff, offset, value) {
                    return add_validation_interval(env, name, interval);
                }
            }
            if let (Some(value), Some((name, coeff, offset))) =
                (lhs.as_i128(), validation_single_var_affine(rhs))
            {
                if let Some(interval) = validation_affine_exact_interval(coeff, offset, value) {
                    return add_validation_interval(env, name, interval);
                }
            }
            if let (Some(name), Some(value)) = (int_var_name(lhs), rhs.as_i128()) {
                return add_validation_interval(env, name, ValidationInterval::exact(value));
            }
            if let (Some(value), Some(name)) = (lhs.as_i128(), int_var_name(rhs)) {
                return add_validation_interval(env, name, ValidationInterval::exact(value));
            }
            if let Some(name) = int_var_name(lhs) {
                if let Some(interval) = validation_expr_interval(rhs, env) {
                    if interval.has_bound() {
                        return add_validation_interval(env, name, interval);
                    }
                }
            }
            if let Some(name) = int_var_name(rhs) {
                if let Some(interval) = validation_expr_interval(lhs, env) {
                    if interval.has_bound() {
                        return add_validation_interval(env, name, interval);
                    }
                }
            }
        }
        ChcOp::Le => {
            if let (Some((name, coeff, offset)), Some(value)) =
                (validation_single_var_affine(lhs), rhs.as_i128())
            {
                if let Some(interval) = validation_affine_upper_interval(coeff, offset, value) {
                    return add_validation_interval(env, name, interval);
                }
            }
            if let (Some(value), Some((name, coeff, offset))) =
                (lhs.as_i128(), validation_single_var_affine(rhs))
            {
                if let Some(interval) = validation_affine_lower_interval(coeff, offset, value) {
                    return add_validation_interval(env, name, interval);
                }
            }
            if let (Some(name), Some(value)) = (int_var_name(lhs), rhs.as_i128()) {
                return add_validation_interval(env, name, ValidationInterval::upper(value));
            }
            if let (Some(value), Some(name)) = (lhs.as_i128(), int_var_name(rhs)) {
                return add_validation_interval(env, name, ValidationInterval::lower(value));
            }
        }
        ChcOp::Lt => {
            if let (Some(name), Some(value)) = (int_var_name(lhs), rhs.as_i128()) {
                return value.checked_sub(1).is_some_and(|upper| {
                    add_validation_interval(env, name, ValidationInterval::upper(upper))
                });
            }
            if let (Some(value), Some(name)) = (lhs.as_i128(), int_var_name(rhs)) {
                return value.checked_add(1).is_some_and(|lower| {
                    add_validation_interval(env, name, ValidationInterval::lower(lower))
                });
            }
        }
        ChcOp::Ge => return collect_validation_direct_bound(ChcOp::Le, rhs, lhs, env),
        ChcOp::Gt => return collect_validation_direct_bound(ChcOp::Lt, rhs, lhs, env),
        _ => {}
    }
    true
}

fn propagate_validation_var_bound(
    conjunct: &ChcExpr,
    env: &mut FxHashMap<String, ValidationInterval>,
) -> bool {
    let simplified = conjunct.simplify_constants();
    if let Some((op, lhs, rhs)) = validation_interval_atom(&simplified) {
        return propagate_validation_var_bound_atom(op, lhs, rhs, env);
    }
    if let ChcExpr::Op(ChcOp::Not, args) = &simplified {
        if args.len() == 1 {
            if let Some((op, lhs, rhs)) = validation_interval_atom(args[0].as_ref()) {
                return propagate_validation_var_bound_atom(
                    negated_validation_comparison(op),
                    lhs,
                    rhs,
                    env,
                );
            }
        }
    }
    true
}

fn propagate_validation_var_bound_atom(
    op: ChcOp,
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    env: &mut FxHashMap<String, ValidationInterval>,
) -> bool {
    match op {
        ChcOp::Le | ChcOp::Lt => {
            let (Some(lhs_name), Some(rhs_name)) = (int_var_name(lhs), int_var_name(rhs)) else {
                return true;
            };
            let strict = matches!(op, ChcOp::Lt);
            if let Some(rhs_upper) = env.get(rhs_name).and_then(|interval| interval.upper) {
                let Some(lhs_upper) = (if strict {
                    rhs_upper.checked_sub(1)
                } else {
                    Some(rhs_upper)
                }) else {
                    return false;
                };
                if !add_validation_interval(env, lhs_name, ValidationInterval::upper(lhs_upper)) {
                    return false;
                }
            }
            if let Some(lhs_lower) = env.get(lhs_name).and_then(|interval| interval.lower) {
                let Some(rhs_lower) = (if strict {
                    lhs_lower.checked_add(1)
                } else {
                    Some(lhs_lower)
                }) else {
                    return false;
                };
                if !add_validation_interval(env, rhs_name, ValidationInterval::lower(rhs_lower)) {
                    return false;
                }
            }
            true
        }
        ChcOp::Ge => propagate_validation_var_bound_atom(ChcOp::Le, rhs, lhs, env),
        ChcOp::Gt => propagate_validation_var_bound_atom(ChcOp::Lt, rhs, lhs, env),
        _ => true,
    }
}

fn propagate_validation_implication_bound(
    conjunct: &ChcExpr,
    env: &mut FxHashMap<String, ValidationInterval>,
) -> bool {
    let simplified = conjunct.simplify_constants();
    let ChcExpr::Op(op, args) = &simplified else {
        return true;
    };
    if matches!(op, ChcOp::Implies) && args.len() == 2 {
        if validation_atom_is_true(args[0].as_ref(), env) {
            return collect_validation_interval_bound(args[1].as_ref(), env);
        }
        return true;
    }
    if !matches!(op, ChcOp::Or) || args.len() != 2 {
        return true;
    }
    if let Some((antecedent, consequent)) =
        validation_or_implication_parts(args[0].as_ref(), args[1].as_ref())
    {
        if validation_atom_is_true(antecedent, env) {
            return collect_validation_interval_bound(consequent, env);
        }
    }
    if let Some((antecedent, consequent)) =
        validation_or_implication_parts(args[1].as_ref(), args[0].as_ref())
    {
        if validation_atom_is_true(antecedent, env) {
            return collect_validation_interval_bound(consequent, env);
        }
    }
    true
}

#[derive(Clone, Debug)]
struct ValidationLinearExpr {
    coeffs: FxHashMap<String, i128>,
    constant: i128,
}

fn propagate_validation_linear_bound(
    conjunct: &ChcExpr,
    env: &mut FxHashMap<String, ValidationInterval>,
) -> bool {
    let simplified = conjunct.simplify_constants();
    let Some((op, lhs, rhs)) = validation_interval_atom(&simplified) else {
        return true;
    };
    let Some(expr) = validation_linear_expr_sub(lhs, rhs) else {
        return true;
    };
    match op {
        ChcOp::Eq => {
            propagate_validation_linear_le(&expr, env)
                && propagate_validation_linear_le(&validation_linear_expr_scale(&expr, -1), env)
        }
        ChcOp::Le => propagate_validation_linear_le(&expr, env),
        ChcOp::Ge => propagate_validation_linear_le(&validation_linear_expr_scale(&expr, -1), env),
        ChcOp::Lt => {
            let expr = validation_linear_expr_add_constant(&expr, 1);
            propagate_validation_linear_le(&expr, env)
        }
        ChcOp::Gt => {
            let expr =
                validation_linear_expr_add_constant(&validation_linear_expr_scale(&expr, -1), 1);
            propagate_validation_linear_le(&expr, env)
        }
        _ => true,
    }
}

fn propagate_validation_linear_le(
    expr: &ValidationLinearExpr,
    env: &mut FxHashMap<String, ValidationInterval>,
) -> bool {
    for (target, coeff) in &expr.coeffs {
        if *coeff == 0 {
            continue;
        }
        let Some(other_min) = validation_linear_min_without(expr, target, env) else {
            continue;
        };
        let rhs = match other_min.checked_neg() {
            Some(value) => value,
            None => return false,
        };
        let interval = if *coeff > 0 {
            ValidationInterval::upper(div_floor_i128(rhs, *coeff))
        } else {
            ValidationInterval::lower(div_ceil_i128(rhs, *coeff))
        };
        if !add_validation_interval(env, target, interval) {
            return false;
        }
    }
    true
}

fn validation_linear_min_without(
    expr: &ValidationLinearExpr,
    target: &str,
    env: &FxHashMap<String, ValidationInterval>,
) -> Option<i128> {
    let mut acc = expr.constant;
    for (name, coeff) in &expr.coeffs {
        if name == target || *coeff == 0 {
            continue;
        }
        let interval = env
            .get(name)
            .copied()
            .unwrap_or_else(ValidationInterval::top);
        let value = if *coeff > 0 {
            interval.lower?
        } else {
            interval.upper?
        };
        acc = acc.checked_add(coeff.checked_mul(value)?)?;
    }
    Some(acc)
}

fn validation_linear_expr_sub(lhs: &ChcExpr, rhs: &ChcExpr) -> Option<ValidationLinearExpr> {
    let lhs = validation_linear_expr(lhs)?;
    let rhs = validation_linear_expr(rhs)?;
    Some(validation_linear_expr_add(
        &lhs,
        &validation_linear_expr_scale(&rhs, -1),
    ))
}

fn validation_linear_expr(expr: &ChcExpr) -> Option<ValidationLinearExpr> {
    match expr {
        ChcExpr::Int(value) => Some(ValidationLinearExpr {
            coeffs: FxHashMap::default(),
            constant: *value,
        }),
        ChcExpr::Var(var) if var.sort == ChcSort::Int => {
            let mut coeffs = FxHashMap::default();
            coeffs.insert(var.name.clone(), 1);
            Some(ValidationLinearExpr {
                coeffs,
                constant: 0,
            })
        }
        ChcExpr::Op(ChcOp::Add, args) => {
            let mut result = ValidationLinearExpr {
                coeffs: FxHashMap::default(),
                constant: 0,
            };
            for arg in args {
                result = validation_linear_expr_add(&result, &validation_linear_expr(arg)?);
            }
            Some(result)
        }
        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            let mut iter = args.iter();
            let mut result = validation_linear_expr(iter.next()?.as_ref())?;
            for arg in iter {
                result = validation_linear_expr_add(
                    &result,
                    &validation_linear_expr_scale(&validation_linear_expr(arg)?, -1),
                );
            }
            Some(result)
        }
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => Some(validation_linear_expr_scale(
            &validation_linear_expr(args[0].as_ref())?,
            -1,
        )),
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => match (&*args[0], &*args[1]) {
            (ChcExpr::Int(coeff), expr) | (expr, ChcExpr::Int(coeff)) => Some(
                validation_linear_expr_scale(&validation_linear_expr(expr)?, *coeff),
            ),
            _ => None,
        },
        _ => None,
    }
}

fn validation_linear_expr_add(
    lhs: &ValidationLinearExpr,
    rhs: &ValidationLinearExpr,
) -> ValidationLinearExpr {
    let mut coeffs = lhs.coeffs.clone();
    for (name, coeff) in &rhs.coeffs {
        let next = coeffs
            .get(name)
            .copied()
            .unwrap_or(0)
            .saturating_add(*coeff);
        if next == 0 {
            coeffs.remove(name);
        } else {
            coeffs.insert(name.clone(), next);
        }
    }
    ValidationLinearExpr {
        coeffs,
        constant: lhs.constant.saturating_add(rhs.constant),
    }
}

fn validation_linear_expr_scale(expr: &ValidationLinearExpr, scale: i128) -> ValidationLinearExpr {
    let coeffs = expr
        .coeffs
        .iter()
        .filter_map(|(name, coeff)| {
            let scaled = coeff.saturating_mul(scale);
            (scaled != 0).then_some((name.clone(), scaled))
        })
        .collect();
    ValidationLinearExpr {
        coeffs,
        constant: expr.constant.saturating_mul(scale),
    }
}

fn validation_linear_expr_add_constant(
    expr: &ValidationLinearExpr,
    constant: i128,
) -> ValidationLinearExpr {
    ValidationLinearExpr {
        coeffs: expr.coeffs.clone(),
        constant: expr.constant.saturating_add(constant),
    }
}

fn div_floor_i128(numerator: i128, denominator: i128) -> i128 {
    debug_assert!(denominator > 0);
    numerator.div_euclid(denominator)
}

fn div_ceil_i128(numerator: i128, denominator: i128) -> i128 {
    debug_assert!(denominator < 0);
    let positive = denominator.saturating_neg();
    numerator.div_euclid(positive).saturating_neg()
}

fn validation_or_implication_parts<'a>(
    negated_antecedent: &'a ChcExpr,
    consequent: &'a ChcExpr,
) -> Option<(&'a ChcExpr, &'a ChcExpr)> {
    let ChcExpr::Op(ChcOp::Not, args) = negated_antecedent else {
        return None;
    };
    if args.len() == 1 {
        Some((args[0].as_ref(), consequent))
    } else {
        None
    }
}

fn validation_atom_is_true(expr: &ChcExpr, env: &FxHashMap<String, ValidationInterval>) -> bool {
    let bool_env = FxHashMap::default();
    let residue_env = FxHashMap::default();
    matches!(
        validation_bool_result(expr, env, &bool_env, &residue_env),
        Some(true)
    )
}

fn add_validation_interval(
    env: &mut FxHashMap<String, ValidationInterval>,
    name: &str,
    interval: ValidationInterval,
) -> bool {
    let merged = env
        .get(name)
        .copied()
        .map_or(interval, |current| current.intersect(interval));
    if merged.is_empty() {
        return false;
    }
    env.insert(name.to_string(), merged);
    true
}

fn collect_validation_mod_residues(
    conjuncts: &[ChcExpr],
) -> Option<FxHashMap<String, (i128, i128)>> {
    let mut residues = FxHashMap::default();
    for conjunct in conjuncts {
        let simplified = conjunct.simplify_constants();
        let Some((name, modulus, residue)) = validation_mod_residue_atom(&simplified) else {
            continue;
        };
        add_validation_mod_residue(&mut residues, &name, modulus, residue)?;
    }
    propagate_validation_mod_residue_equalities(conjuncts, &mut residues)?;
    Some(residues)
}

fn add_validation_mod_residue(
    residues: &mut FxHashMap<String, (i128, i128)>,
    name: &str,
    modulus: i128,
    residue: i128,
) -> Option<bool> {
    if modulus <= 1 {
        return Some(false);
    }
    let residue = residue.rem_euclid(modulus);
    let Some((old_modulus, old_residue)) = residues.get(name).copied() else {
        residues.insert(name.to_string(), (modulus, residue));
        return Some(true);
    };

    if old_modulus == modulus {
        return (old_residue == residue).then_some(false);
    }

    let gcd = validation_gcd_i128(old_modulus, modulus);
    if old_residue.rem_euclid(gcd) != residue.rem_euclid(gcd) {
        return None;
    }

    if old_modulus % modulus == 0 {
        return Some(false);
    }
    if modulus % old_modulus == 0 {
        residues.insert(name.to_string(), (modulus, residue));
        return Some(true);
    }

    Some(false)
}

fn propagate_validation_mod_residue_equalities(
    conjuncts: &[ChcExpr],
    residues: &mut FxHashMap<String, (i128, i128)>,
) -> Option<()> {
    let max_rounds = conjuncts.len().saturating_add(4).clamp(1, 32);
    for _ in 0..max_rounds {
        let before = residues.clone();
        for conjunct in conjuncts {
            let simplified = conjunct.simplify_constants();
            let Some((ChcOp::Eq, lhs, rhs)) = validation_interval_atom(&simplified) else {
                continue;
            };
            propagate_validation_mod_residue_equality(lhs, rhs, residues)?;
        }
        if *residues == before {
            break;
        }
    }
    Some(())
}

struct ValidationUnitAffineEquality {
    lhs_name: String,
    lhs_coeff: i128,
    rhs_name: String,
    rhs_coeff: i128,
    constant: i128,
}

fn propagate_validation_mod_residue_equality(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    residues: &mut FxHashMap<String, (i128, i128)>,
) -> Option<()> {
    let Some(expr) = validation_unit_affine_equality(lhs, rhs) else {
        return Some(());
    };
    let vars = [
        (expr.lhs_name.as_str(), expr.lhs_coeff),
        (expr.rhs_name.as_str(), expr.rhs_coeff),
    ];

    let mut inferred = Vec::new();
    for target_idx in 0..2 {
        let (target, target_coeff) = vars[target_idx];
        let (source, source_coeff) = vars[1 - target_idx];
        if !matches!(target_coeff, -1 | 1) || !matches!(source_coeff, -1 | 1) {
            continue;
        }
        let Some((modulus, source_residue)) = residues.get(source).copied() else {
            continue;
        };
        let Some(target_residue) = validation_unit_equality_residue(
            target_coeff,
            source_coeff,
            expr.constant,
            modulus,
            source_residue,
        ) else {
            continue;
        };
        inferred.push((target.to_string(), modulus, target_residue));
    }

    for (target, modulus, residue) in inferred {
        add_validation_mod_residue(residues, &target, modulus, residue)?;
    }
    Some(())
}

fn validation_unit_affine_equality(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
) -> Option<ValidationUnitAffineEquality> {
    let (lhs_name, lhs_coeff, lhs_offset) = validation_single_var_affine(lhs)?;
    let (rhs_name, rhs_coeff, rhs_offset) = validation_single_var_affine(rhs)?;
    if lhs_name == rhs_name {
        return None;
    }
    Some(ValidationUnitAffineEquality {
        lhs_name: lhs_name.to_string(),
        lhs_coeff,
        rhs_name: rhs_name.to_string(),
        rhs_coeff: rhs_coeff.checked_neg()?,
        constant: lhs_offset.checked_sub(rhs_offset)?,
    })
}

fn validation_unit_equality_residue(
    target_coeff: i128,
    source_coeff: i128,
    constant: i128,
    modulus: i128,
    source_residue: i128,
) -> Option<i128> {
    let source_multiplier = if target_coeff == 1 {
        source_coeff.checked_neg()?
    } else {
        source_coeff
    };
    let offset = if target_coeff == 1 {
        constant.checked_neg()?
    } else {
        constant
    };
    source_multiplier
        .checked_mul(source_residue)?
        .checked_add(offset)
        .map(|value| value.rem_euclid(modulus))
}

fn validation_gcd_i128(mut a: i128, mut b: i128) -> i128 {
    a = a.abs();
    b = b.abs();
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

fn validation_mod_residue_atom(expr: &ChcExpr) -> Option<(String, i128, i128)> {
    let ChcExpr::Op(ChcOp::Eq, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    match (&*args[0], &*args[1]) {
        (ChcExpr::Op(ChcOp::Mod, mod_args), ChcExpr::Int(residue)) if mod_args.len() == 2 => {
            validation_mod_residue_from_parts(mod_args[0].as_ref(), mod_args[1].as_ref(), *residue)
        }
        (ChcExpr::Int(residue), ChcExpr::Op(ChcOp::Mod, mod_args)) if mod_args.len() == 2 => {
            validation_mod_residue_from_parts(mod_args[0].as_ref(), mod_args[1].as_ref(), *residue)
        }
        _ => None,
    }
}

fn validation_mod_residue_from_parts(
    term: &ChcExpr,
    modulus_expr: &ChcExpr,
    residue: i128,
) -> Option<(String, i128, i128)> {
    let modulus = modulus_expr.as_i128()?;
    if modulus <= 1 {
        return None;
    }
    let (name, offset) = validation_single_var_offset(term)?;
    Some((name.to_string(), modulus, residue - offset))
}

fn validation_single_var_offset(expr: &ChcExpr) -> Option<(&str, i128)> {
    let (name, coeff, offset) = validation_single_var_affine(expr)?;
    (coeff == 1).then_some((name, offset))
}

fn validation_single_var_affine(expr: &ChcExpr) -> Option<(&str, i128, i128)> {
    if let Some(name) = int_var_name(expr) {
        return Some((name, 1, 0));
    }
    let ChcExpr::Op(op, args) = expr else {
        return None;
    };
    match op {
        ChcOp::Add => {
            let mut name = None;
            let mut coeff = 0i128;
            let mut offset = 0i128;
            for arg in args {
                if let Some(value) = arg.as_i128() {
                    offset = offset.checked_add(value)?;
                } else if let Some((arg_name, arg_coeff, arg_offset)) =
                    validation_single_var_affine(arg.as_ref())
                {
                    if let Some(existing) = name {
                        if existing != arg_name {
                            return None;
                        }
                    } else {
                        name = Some(arg_name);
                    }
                    coeff = coeff.checked_add(arg_coeff)?;
                    offset = offset.checked_add(arg_offset)?;
                    if !matches!(coeff, -1..=1) {
                        return None;
                    }
                } else {
                    return None;
                }
            }
            name.and_then(|name| (coeff != 0).then_some((name, coeff, offset)))
        }
        ChcOp::Sub if args.len() == 2 => {
            let (lhs_name, lhs_coeff, lhs_offset) = validation_single_var_affine(args[0].as_ref())?;
            if let Some(rhs_value) = args[1].as_i128() {
                return Some((lhs_name, lhs_coeff, lhs_offset.checked_sub(rhs_value)?));
            }
            let (rhs_name, rhs_coeff, rhs_offset) = validation_single_var_affine(args[1].as_ref())?;
            if lhs_name != rhs_name {
                return None;
            }
            let coeff = lhs_coeff.checked_sub(rhs_coeff)?;
            let offset = lhs_offset.checked_sub(rhs_offset)?;
            (coeff != 0 && matches!(coeff, -1 | 1)).then_some((lhs_name, coeff, offset))
        }
        ChcOp::Neg if args.len() == 1 => {
            let (name, coeff, offset) = validation_single_var_affine(args[0].as_ref())?;
            Some((name, coeff.checked_neg()?, offset.checked_neg()?))
        }
        _ => None,
    }
}

fn validation_affine_exact_interval(
    coeff: i128,
    offset: i128,
    value: i128,
) -> Option<ValidationInterval> {
    match coeff {
        1 => Some(ValidationInterval::exact(value.checked_sub(offset)?)),
        -1 => Some(ValidationInterval::exact(offset.checked_sub(value)?)),
        _ => None,
    }
}

fn validation_affine_upper_interval(
    coeff: i128,
    offset: i128,
    value: i128,
) -> Option<ValidationInterval> {
    match coeff {
        1 => Some(ValidationInterval::upper(value.checked_sub(offset)?)),
        -1 => Some(ValidationInterval::lower(offset.checked_sub(value)?)),
        _ => None,
    }
}

fn validation_affine_lower_interval(
    coeff: i128,
    offset: i128,
    value: i128,
) -> Option<ValidationInterval> {
    match coeff {
        1 => Some(ValidationInterval::lower(value.checked_sub(offset)?)),
        -1 => Some(ValidationInterval::upper(offset.checked_sub(value)?)),
        _ => None,
    }
}

fn refine_validation_intervals_with_residues(
    env: &mut FxHashMap<String, ValidationInterval>,
    residues: &FxHashMap<String, (i128, i128)>,
) -> bool {
    for (name, (modulus, residue)) in residues {
        let Some(current) = env.get(name).copied() else {
            continue;
        };
        let refined = refine_validation_interval_to_residue(current, *modulus, *residue);
        if refined.is_empty() {
            return false;
        }
        env.insert(name.clone(), refined);
    }
    true
}

fn refine_validation_interval_to_residue(
    interval: ValidationInterval,
    modulus: i128,
    residue: i128,
) -> ValidationInterval {
    if modulus <= 1 {
        return interval;
    }
    let residue = residue.rem_euclid(modulus);
    let lower = interval.lower.map(|lower| {
        let delta = (residue - lower).rem_euclid(modulus);
        lower.saturating_add(delta)
    });
    let upper = interval.upper.map(|upper| {
        let delta = (upper - residue).rem_euclid(modulus);
        upper.saturating_sub(delta)
    });
    ValidationInterval { lower, upper }
}

fn collect_validation_bool_assignments(conjuncts: &[ChcExpr]) -> Option<FxHashMap<String, bool>> {
    let mut env = FxHashMap::default();
    for conjunct in conjuncts {
        collect_validation_bool_assignment(conjunct, &mut env)?;
    }
    Some(env)
}

fn collect_validation_bool_assignment(
    conjunct: &ChcExpr,
    env: &mut FxHashMap<String, bool>,
) -> Option<()> {
    let simplified = conjunct.simplify_constants();
    match &simplified {
        ChcExpr::Var(var) if var.sort == ChcSort::Bool => {
            add_validation_bool_assignment(env, &var.name, true)
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            if let Some(name) = bool_var_name(args[0].as_ref()) {
                add_validation_bool_assignment(env, name, false)
            } else {
                Some(())
            }
        }
        ChcExpr::Op(op @ (ChcOp::Eq | ChcOp::Ne), args) if args.len() == 2 => {
            let negated = matches!(*op, ChcOp::Ne);
            if let (Some(name), ChcExpr::Bool(value)) =
                (bool_var_name(args[0].as_ref()), args[1].as_ref())
            {
                return add_validation_bool_assignment(env, name, *value ^ negated);
            }
            if let (ChcExpr::Bool(value), Some(name)) =
                (args[0].as_ref(), bool_var_name(args[1].as_ref()))
            {
                return add_validation_bool_assignment(env, name, *value ^ negated);
            }
            Some(())
        }
        _ => Some(()),
    }
}

fn add_validation_bool_assignment(
    env: &mut FxHashMap<String, bool>,
    name: &str,
    value: bool,
) -> Option<()> {
    if env
        .insert(name.to_string(), value)
        .is_some_and(|old| old != value)
    {
        return None;
    }
    Some(())
}

fn validation_bool_result(
    expr: &ChcExpr,
    int_env: &FxHashMap<String, ValidationInterval>,
    bool_env: &FxHashMap<String, bool>,
    residue_env: &FxHashMap<String, (i128, i128)>,
) -> Option<bool> {
    let simplified = expr.simplify_constants();
    match &simplified {
        ChcExpr::Bool(value) => Some(*value),
        ChcExpr::Var(var) if var.sort == ChcSort::Bool => bool_env.get(&var.name).copied(),
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => Some(!validation_bool_result(
            args[0].as_ref(),
            int_env,
            bool_env,
            residue_env,
        )?),
        ChcExpr::Op(ChcOp::And, args) => {
            let mut all_true = true;
            for arg in args {
                match validation_bool_result(arg.as_ref(), int_env, bool_env, residue_env) {
                    Some(false) => return Some(false),
                    Some(true) => {}
                    None => all_true = false,
                }
            }
            all_true.then_some(true)
        }
        ChcExpr::Op(ChcOp::Or, args) => {
            let mut all_false = true;
            for arg in args {
                match validation_bool_result(arg.as_ref(), int_env, bool_env, residue_env) {
                    Some(true) => return Some(true),
                    Some(false) => {}
                    None => all_false = false,
                }
            }
            all_false.then_some(false)
        }
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            if let Some(condition) =
                validation_bool_result(args[0].as_ref(), int_env, bool_env, residue_env)
            {
                return validation_bool_result(
                    args[if condition { 1 } else { 2 }].as_ref(),
                    int_env,
                    bool_env,
                    residue_env,
                );
            }
            let then_result =
                validation_bool_result(args[1].as_ref(), int_env, bool_env, residue_env);
            let else_result =
                validation_bool_result(args[2].as_ref(), int_env, bool_env, residue_env);
            if then_result.is_some() && then_result == else_result {
                return then_result;
            }
            validation_same_condition_nested_ite_result(
                args[0].as_ref(),
                args[1].as_ref(),
                args[2].as_ref(),
                int_env,
                bool_env,
                residue_env,
            )
        }
        ChcExpr::Op(op @ (ChcOp::Eq | ChcOp::Ne), args) if args.len() == 2 => {
            let negated = matches!(*op, ChcOp::Ne);
            if let (Some(lhs), Some(rhs)) = (
                validation_bool_result(args[0].as_ref(), int_env, bool_env, residue_env),
                validation_bool_result(args[1].as_ref(), int_env, bool_env, residue_env),
            ) {
                return Some((lhs == rhs) ^ negated);
            }
            if let Some(result) =
                bool_bitvec_sign_extract_eq_result(args[0].as_ref(), args[1].as_ref())
            {
                return Some(result ^ negated);
            }
            if let Some(result) =
                validation_mod_compare_result(args[0].as_ref(), args[1].as_ref(), residue_env)
            {
                return Some(result ^ negated);
            }
            if let Some(result) = validation_interval_compare_result(
                ChcOp::Eq,
                args[0].as_ref(),
                args[1].as_ref(),
                int_env,
            ) {
                return Some(result ^ negated);
            }
            None
        }
        ChcExpr::Op(op @ (ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge), args)
            if args.len() == 2 =>
        {
            if let Some(result) =
                validation_interval_compare_result(*op, args[0].as_ref(), args[1].as_ref(), int_env)
            {
                return Some(result);
            }
            if validation_bounded_increment_wrap_comparison_is_false(
                *op,
                args[0].as_ref(),
                args[1].as_ref(),
                int_env,
            ) {
                return Some(false);
            }
            None
        }
        _ => None,
    }
}

fn validation_static_bool_result(expr: &ChcExpr) -> Option<bool> {
    let simplified = expr.simplify_constants();
    match &simplified {
        ChcExpr::Bool(value) => Some(*value),
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            Some(!validation_static_bool_result(args[0].as_ref())?)
        }
        ChcExpr::Op(ChcOp::And, args) => {
            let mut all_true = true;
            for arg in args {
                match validation_static_bool_result(arg.as_ref()) {
                    Some(false) => return Some(false),
                    Some(true) => {}
                    None => all_true = false,
                }
            }
            all_true.then_some(true)
        }
        ChcExpr::Op(ChcOp::Or, args) => {
            let mut all_false = true;
            for arg in args {
                match validation_static_bool_result(arg.as_ref()) {
                    Some(true) => return Some(true),
                    Some(false) => {}
                    None => all_false = false,
                }
            }
            all_false.then_some(false)
        }
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            let condition = validation_static_bool_result(args[0].as_ref())?;
            validation_static_bool_result(args[if condition { 1 } else { 2 }].as_ref())
        }
        ChcExpr::Op(op @ (ChcOp::Eq | ChcOp::Ne), args) if args.len() == 2 => {
            let negated = matches!(*op, ChcOp::Ne);
            if let Some(result) =
                bool_bitvec_sign_extract_eq_result(args[0].as_ref(), args[1].as_ref())
            {
                return Some(result ^ negated);
            }
            None
        }
        _ => None,
    }
}

fn validation_same_condition_nested_ite_result(
    condition: &ChcExpr,
    then_expr: &ChcExpr,
    else_expr: &ChcExpr,
    int_env: &FxHashMap<String, ValidationInterval>,
    bool_env: &FxHashMap<String, bool>,
    residue_env: &FxHashMap<String, (i128, i128)>,
) -> Option<bool> {
    let condition_key = validation_expr_key(condition);
    let then_selected = validation_nested_ite_branch_for_condition(then_expr, &condition_key, true);
    let else_selected =
        validation_nested_ite_branch_for_condition(else_expr, &condition_key, false);
    let then_result = validation_bool_result(then_selected, int_env, bool_env, residue_env)?;
    let else_result = validation_bool_result(else_selected, int_env, bool_env, residue_env)?;
    (then_result == else_result).then_some(then_result)
}

fn validation_nested_ite_branch_for_condition<'a>(
    expr: &'a ChcExpr,
    condition_key: &str,
    condition_value: bool,
) -> &'a ChcExpr {
    let ChcExpr::Op(ChcOp::Ite, args) = expr else {
        return expr;
    };
    if args.len() != 3 || validation_expr_key(args[0].as_ref()) != condition_key {
        return expr;
    }
    args[if condition_value { 1 } else { 2 }].as_ref()
}

fn validation_bounded_increment_wrap_comparison_is_false(
    op: ChcOp,
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    env: &FxHashMap<String, ValidationInterval>,
) -> bool {
    let lhs = match op {
        ChcOp::Lt => lhs,
        ChcOp::Le => {
            let Some(stripped) = strip_plus_one(lhs) else {
                return false;
            };
            stripped
        }
        _ => return false,
    };
    let Some((name, modulus)) = increment_mod_less_than_base_pattern(lhs, rhs) else {
        return false;
    };
    let Some(interval) = env.get(name) else {
        return false;
    };
    let (Some(lower), Some(upper)) = (interval.lower, interval.upper) else {
        return false;
    };
    if lower < 0 {
        return false;
    }
    let Ok(upper) = u128::try_from(upper) else {
        return false;
    };
    let Some(last_residue) = modulus.checked_sub(1) else {
        return false;
    };
    upper < last_residue
}

fn validation_mod_compare_result(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    residues: &FxHashMap<String, (i128, i128)>,
) -> Option<bool> {
    if let (Some(lhs_residue), Some(rhs_value)) = (
        validation_mod_expr_known_residue(lhs, residues),
        rhs.as_i128(),
    ) {
        return Some(lhs_residue == rhs_value);
    }
    if let (Some(lhs_value), Some(rhs_residue)) = (
        lhs.as_i128(),
        validation_mod_expr_known_residue(rhs, residues),
    ) {
        return Some(lhs_value == rhs_residue);
    }
    None
}

fn validation_mod_expr_known_residue(
    expr: &ChcExpr,
    residues: &FxHashMap<String, (i128, i128)>,
) -> Option<i128> {
    let ChcExpr::Op(ChcOp::Mod, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let modulus = args[1].as_i128()?;
    if modulus <= 1 {
        return None;
    }
    let (name, offset) = validation_single_var_offset(args[0].as_ref())?;
    let (known_modulus, residue) = residues.get(name)?;
    if *known_modulus != modulus && *known_modulus % modulus != 0 {
        return None;
    }
    Some((*residue + offset).rem_euclid(modulus))
}

fn increment_mod_less_than_base_pattern<'a>(
    lhs: &'a ChcExpr,
    rhs: &'a ChcExpr,
) -> Option<(&'a str, u128)> {
    let (lhs_inner, lhs_modulus) = outer_mod(lhs)?;
    let (rhs_inner, rhs_modulus) = outer_mod(rhs)?;
    if lhs_modulus != rhs_modulus || lhs_modulus <= 1 {
        return None;
    }
    let lhs_name = add_one_int_var_name(lhs_inner)?;
    let rhs_name = int_var_name(rhs_inner)?;
    (lhs_name == rhs_name).then_some((lhs_name, lhs_modulus))
}

fn outer_mod(expr: &ChcExpr) -> Option<(&ChcExpr, u128)> {
    let ChcExpr::Op(ChcOp::Mod, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let modulus = eval_validation_nonnegative_const_u128(args[1].as_ref(), 0)?;
    if modulus == 0 {
        return None;
    }
    Some((strip_same_mod(args[0].as_ref(), modulus), modulus))
}

fn strip_same_mod(mut expr: &ChcExpr, modulus: u128) -> &ChcExpr {
    while let ChcExpr::Op(ChcOp::Mod, args) = expr {
        if args.len() != 2
            || eval_validation_nonnegative_const_u128(args[1].as_ref(), 0) != Some(modulus)
        {
            break;
        }
        expr = args[0].as_ref();
    }
    expr
}

fn add_one_int_var_name(expr: &ChcExpr) -> Option<&str> {
    let ChcExpr::Op(ChcOp::Add, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    if args[0].as_i64() == Some(1) {
        return int_var_name(args[1].as_ref());
    }
    if args[1].as_i64() == Some(1) {
        return int_var_name(args[0].as_ref());
    }
    None
}

fn strip_plus_one(expr: &ChcExpr) -> Option<&ChcExpr> {
    let ChcExpr::Op(ChcOp::Add, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    if args[0].as_i64() == Some(1) {
        return Some(args[1].as_ref());
    }
    if args[1].as_i64() == Some(1) {
        return Some(args[0].as_ref());
    }
    None
}

fn eval_validation_nonnegative_const_u128(expr: &ChcExpr, depth: usize) -> Option<u128> {
    if depth >= MAX_EXPR_RECURSION_DEPTH {
        return None;
    }
    maybe_grow_expr_stack(|| match expr {
        ChcExpr::Int(n) if *n >= 0 => Some(*n as u128),
        ChcExpr::Op(ChcOp::Add, args) => {
            let mut acc = 0u128;
            for arg in args {
                acc = acc.checked_add(eval_validation_nonnegative_const_u128(arg, depth + 1)?)?;
            }
            Some(acc)
        }
        ChcExpr::Op(ChcOp::Mul, args) => {
            let mut acc = 1u128;
            for arg in args {
                acc = acc.checked_mul(eval_validation_nonnegative_const_u128(arg, depth + 1)?)?;
            }
            Some(acc)
        }
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            let lhs = eval_validation_nonnegative_const_u128(args[0].as_ref(), depth + 1)?;
            let rhs = eval_validation_nonnegative_const_u128(args[1].as_ref(), depth + 1)?;
            lhs.checked_sub(rhs)
        }
        ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
            let lhs = eval_validation_nonnegative_const_u128(args[0].as_ref(), depth + 1)?;
            let rhs = eval_validation_nonnegative_const_u128(args[1].as_ref(), depth + 1)?;
            (rhs != 0).then_some(lhs % rhs)
        }
        _ => None,
    })
}

fn validation_interval_compare_result(
    op: ChcOp,
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    env: &FxHashMap<String, ValidationInterval>,
) -> Option<bool> {
    if let Some(result) = validation_interval_u128_compare_result(op, lhs, rhs, env) {
        return Some(result);
    }
    let lhs_interval = validation_expr_interval(lhs, env)?;
    let rhs_interval = validation_expr_interval(rhs, env)?;
    match op {
        ChcOp::Lt => {
            if lhs_interval.upper? < rhs_interval.lower? {
                Some(true)
            } else if lhs_interval.lower? >= rhs_interval.upper? {
                Some(false)
            } else {
                None
            }
        }
        ChcOp::Le => {
            if lhs_interval.upper? <= rhs_interval.lower? {
                Some(true)
            } else if lhs_interval.lower? > rhs_interval.upper? {
                Some(false)
            } else {
                None
            }
        }
        ChcOp::Gt => {
            if lhs_interval.lower? > rhs_interval.upper? {
                Some(true)
            } else if lhs_interval.upper? <= rhs_interval.lower? {
                Some(false)
            } else {
                None
            }
        }
        ChcOp::Ge => {
            if lhs_interval.lower? >= rhs_interval.upper? {
                Some(true)
            } else if lhs_interval.upper? < rhs_interval.lower? {
                Some(false)
            } else {
                None
            }
        }
        ChcOp::Eq => {
            // SOUNDNESS (#llreve-barthe wrong-sat): the "both singleton and
            // equal" test must require the bounds to EXIST. Both sides must be
            // the SAME KNOWN singleton [k,k]. For two unconstrained variables
            // every field is None and `None == None` made this arm return
            // Some(true) for `(= B C)` — which let
            // `validation_formula_proves_unsat` discharge satisfiable
            // query-clause violations (e.g. `inv(..) /\ c != d => false` with
            // `inv := true`) and certify unsafe systems as SAFE (false SAFE,
            // caught only by the CLI's final discharge gate).
            if lhs_interval.lower.is_some()
                && lhs_interval.lower == lhs_interval.upper
                && lhs_interval.lower == rhs_interval.lower
                && rhs_interval.lower == rhs_interval.upper
            {
                Some(true)
            } else if lhs_interval.upper? < rhs_interval.lower?
                || rhs_interval.upper? < lhs_interval.lower?
            {
                Some(false)
            } else {
                None
            }
        }
        ChcOp::Ne => {
            // SOUNDNESS: same `is_some()` guard as the Eq arm above. None ==
            // None must not be read as "same singleton value".
            if lhs_interval.lower.is_some()
                && lhs_interval.lower == lhs_interval.upper
                && lhs_interval.lower == rhs_interval.lower
                && rhs_interval.lower == rhs_interval.upper
            {
                Some(false)
            } else if lhs_interval.upper? < rhs_interval.lower?
                || rhs_interval.upper? < lhs_interval.lower?
            {
                Some(true)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn validation_interval_u128_compare_result(
    op: ChcOp,
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    env: &FxHashMap<String, ValidationInterval>,
) -> Option<bool> {
    if let (Some(lhs_interval), Some(rhs_const)) = (
        validation_expr_interval(lhs, env),
        eval_validation_nonnegative_const_u128(rhs, 0),
    ) {
        return compare_interval_to_u128(lhs_interval, op, rhs_const);
    }
    if let (Some(lhs_const), Some(rhs_interval)) = (
        eval_validation_nonnegative_const_u128(lhs, 0),
        validation_expr_interval(rhs, env),
    ) {
        return compare_u128_to_interval(lhs_const, op, rhs_interval);
    }
    None
}

fn compare_interval_to_u128(interval: ValidationInterval, op: ChcOp, value: u128) -> Option<bool> {
    match op {
        ChcOp::Lt => {
            if interval_i128_upper_lt_u128(interval.upper?, value) {
                Some(true)
            } else if interval_i128_lower_ge_u128(interval.lower?, value) {
                Some(false)
            } else {
                None
            }
        }
        ChcOp::Le => {
            if interval_i128_upper_le_u128(interval.upper?, value) {
                Some(true)
            } else if interval_i128_lower_gt_u128(interval.lower?, value) {
                Some(false)
            } else {
                None
            }
        }
        ChcOp::Gt => {
            if interval_i128_lower_gt_u128(interval.lower?, value) {
                Some(true)
            } else if interval_i128_upper_le_u128(interval.upper?, value) {
                Some(false)
            } else {
                None
            }
        }
        ChcOp::Ge => {
            if interval_i128_lower_ge_u128(interval.lower?, value) {
                Some(true)
            } else if interval_i128_upper_lt_u128(interval.upper?, value) {
                Some(false)
            } else {
                None
            }
        }
        ChcOp::Eq => {
            if interval.lower == interval.upper
                && interval
                    .lower
                    .is_some_and(|lower| i128_nonnegative_eq_u128(lower, value))
            {
                Some(true)
            } else if interval_i128_upper_lt_u128(interval.upper?, value)
                || interval_i128_lower_gt_u128(interval.lower?, value)
            {
                Some(false)
            } else {
                None
            }
        }
        ChcOp::Ne => compare_interval_to_u128(interval, ChcOp::Eq, value).map(|result| !result),
        _ => None,
    }
}

fn compare_u128_to_interval(value: u128, op: ChcOp, interval: ValidationInterval) -> Option<bool> {
    let flipped = match op {
        ChcOp::Lt => ChcOp::Gt,
        ChcOp::Le => ChcOp::Ge,
        ChcOp::Gt => ChcOp::Lt,
        ChcOp::Ge => ChcOp::Le,
        other => other,
    };
    compare_interval_to_u128(interval, flipped, value)
}

fn interval_i128_upper_lt_u128(upper: i128, value: u128) -> bool {
    upper < 0 || (upper as u128) < value
}

fn interval_i128_upper_le_u128(upper: i128, value: u128) -> bool {
    upper < 0 || (upper as u128) <= value
}

fn interval_i128_lower_gt_u128(lower: i128, value: u128) -> bool {
    lower >= 0 && (lower as u128) > value
}

fn interval_i128_lower_ge_u128(lower: i128, value: u128) -> bool {
    lower >= 0 && (lower as u128) >= value
}

fn i128_nonnegative_eq_u128(value: i128, expected: u128) -> bool {
    value >= 0 && (value as u128) == expected
}

fn validation_expr_interval(
    expr: &ChcExpr,
    env: &FxHashMap<String, ValidationInterval>,
) -> Option<ValidationInterval> {
    if matches!(expr.sort(), ChcSort::Int) && validation_expr_has_bool_domain(expr) {
        return Some(ValidationInterval {
            lower: Some(0),
            upper: Some(1),
        });
    }
    if let Some(interval) = signed_bv_to_int_interval(expr) {
        return Some(interval);
    }
    match expr {
        ChcExpr::Int(value) => Some(ValidationInterval::exact(*value)),
        ChcExpr::Var(var) if var.sort == ChcSort::Int => Some(
            env.get(&var.name)
                .copied()
                .unwrap_or_else(ValidationInterval::top),
        ),
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            Some(validation_expr_interval(args[0].as_ref(), env)?.checked_neg())
        }
        ChcExpr::Op(ChcOp::Add, args) if !args.is_empty() => {
            let mut interval = ValidationInterval::exact(0);
            for arg in args {
                interval = interval.checked_add(validation_expr_interval(arg.as_ref(), env)?);
            }
            Some(interval)
        }
        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            let mut iter = args.iter();
            let first = validation_expr_interval(iter.next()?.as_ref(), env)?;
            if args.len() == 1 {
                return Some(first.checked_neg());
            }
            let mut interval = first;
            for arg in iter {
                interval = interval.checked_sub(validation_expr_interval(arg.as_ref(), env)?);
            }
            Some(interval)
        }
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            if let Some(factor) = args[0].as_i128() {
                return Some(
                    validation_expr_interval(args[1].as_ref(), env)?.checked_scale(factor),
                );
            }
            if let Some(factor) = args[1].as_i128() {
                return Some(
                    validation_expr_interval(args[0].as_ref(), env)?.checked_scale(factor),
                );
            }
            Some(ValidationInterval::top())
        }
        _ if matches!(expr.sort(), ChcSort::Int) => Some(ValidationInterval::top()),
        _ => None,
    }
}

fn signed_bv_to_int_interval(expr: &ChcExpr) -> Option<ValidationInterval> {
    let (_, width) = signed_bv_to_int_payload_and_width(expr)?;
    if width == 0 || width > 64 {
        return None;
    }
    if width == 64 {
        return Some(ValidationInterval {
            lower: Some(i128::from(i64::MIN)),
            upper: Some(i128::from(i64::MAX)),
        });
    }
    let upper = (1_i128.checked_shl(width - 1)?).checked_sub(1)?;
    let lower = -(1_i128.checked_shl(width - 1)?);
    Some(ValidationInterval {
        lower: Some(lower),
        upper: Some(upper),
    })
}

fn signed_bv_to_int_payload_and_width(expr: &ChcExpr) -> Option<(&ChcExpr, u32)> {
    let ChcExpr::Op(ChcOp::Ite, args) = expr else {
        return None;
    };
    if args.len() != 3 {
        return None;
    }
    let (guard_key, width) = signed_bv_sign_guard_payload(args[0].as_ref())?;
    let (then_payload, then_width) = signed_bv_negative_branch_payload(args[1].as_ref())?;
    let (else_payload, else_width) = unsigned_bv_to_int_payload(args[2].as_ref())?;
    if width != then_width || width != else_width {
        return None;
    }
    let then_key = validation_expr_key(then_payload);
    let else_key = validation_expr_key(else_payload);
    (guard_key == then_key && guard_key == else_key).then_some((else_payload, width))
}

fn signed_bv_sign_guard_payload(expr: &ChcExpr) -> Option<(String, u32)> {
    let ChcExpr::Op(ChcOp::Eq, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    signed_bv_sign_guard_payload_sides(args[0].as_ref(), args[1].as_ref())
        .or_else(|| signed_bv_sign_guard_payload_sides(args[1].as_ref(), args[0].as_ref()))
}

fn signed_bv_sign_guard_payload_sides(lhs: &ChcExpr, rhs: &ChcExpr) -> Option<(String, u32)> {
    match rhs {
        ChcExpr::BitVec(1, 1) => {
            let ChcExpr::Op(ChcOp::BvExtract(hi, lo), extract_args) = lhs else {
                return None;
            };
            if extract_args.len() != 1 || hi != lo {
                return None;
            }
            if let ChcExpr::Op(ChcOp::Int2Bv(width), int2bv_args) = extract_args[0].as_ref() {
                if int2bv_args.len() != 1 || *hi + 1 != *width {
                    return None;
                }
                return Some((validation_expr_key(int2bv_args[0].as_ref()), *width));
            }
            let (payload, width) = bool_bitvec_ite_payload(extract_args[0].as_ref())?;
            if *hi + 1 != width {
                return None;
            }
            Some((validation_expr_key(payload), width))
        }
        ChcExpr::Int(1) => {
            let ChcExpr::Op(ChcOp::Div, div_args) = lhs else {
                return None;
            };
            if div_args.len() != 2 {
                return None;
            }
            let half_modulus = eval_validation_nonnegative_const_u128(div_args[1].as_ref(), 0)?;
            if half_modulus <= 1 {
                return None;
            }
            let (payload, width) = unsigned_bv_to_int_payload(div_args[0].as_ref())?;
            let expected_half = pow2_u128(width.checked_sub(1)?)?;
            (half_modulus == expected_half).then_some((validation_expr_key(payload), width))
        }
        _ => None,
    }
}

fn signed_bv_negative_branch_payload(expr: &ChcExpr) -> Option<(&ChcExpr, u32)> {
    let ChcExpr::Op(ChcOp::Sub, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (payload, width) = unsigned_bv_to_int_payload(args[0].as_ref())?;
    let modulus = eval_validation_nonnegative_const_u128(args[1].as_ref(), 0)?;
    (modulus == pow2_u128(width)?).then_some((payload, width))
}

fn unsigned_bv_to_int_payload(expr: &ChcExpr) -> Option<(&ChcExpr, u32)> {
    match expr {
        ChcExpr::Op(ChcOp::Bv2Nat, args) if args.len() == 1 => {
            if let ChcExpr::Op(ChcOp::Int2Bv(width), int2bv_args) = args[0].as_ref() {
                return (int2bv_args.len() == 1).then(|| (int2bv_args[0].as_ref(), *width));
            }
            bool_bitvec_ite_payload(args[0].as_ref())
        }
        ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
            let modulus = eval_validation_nonnegative_const_u128(args[1].as_ref(), 0)?;
            let width = modulus_to_pow2_width(modulus)?;
            Some((args[0].as_ref(), width))
        }
        _ => None,
    }
}

fn bool_bitvec_ite_payload(expr: &ChcExpr) -> Option<(&ChcExpr, u32)> {
    let ChcExpr::Op(ChcOp::Ite, args) = expr else {
        return None;
    };
    if args.len() != 3 || !matches!(args[0].sort(), ChcSort::Bool) {
        return None;
    }
    let (then_value, then_width) = bool_bitvec_ite_branch(args[1].as_ref())?;
    let (else_value, else_width) = bool_bitvec_ite_branch(args[2].as_ref())?;
    (then_width == else_width && matches!((then_value, else_value), (0, 1) | (1, 0)))
        .then_some((expr, then_width))
}

fn bool_bitvec_ite_branch(expr: &ChcExpr) -> Option<(u128, u32)> {
    let ChcExpr::BitVec(value, width) = expr else {
        return None;
    };
    (*width > 0 && matches!(*value, 0 | 1)).then_some((*value, *width))
}

fn bool_bitvec_ite_as_int_expr(expr: &ChcExpr) -> Option<ChcExpr> {
    let ChcExpr::Op(ChcOp::Ite, args) = expr else {
        return None;
    };
    if args.len() != 3 || !matches!(args[0].sort(), ChcSort::Bool) {
        return None;
    }
    let (then_value, then_width) = bool_bitvec_ite_branch(args[1].as_ref())?;
    let (else_value, else_width) = bool_bitvec_ite_branch(args[2].as_ref())?;
    if then_width != else_width || !matches!((then_value, else_value), (0, 1) | (1, 0)) {
        return None;
    }
    Some(ChcExpr::Op(
        ChcOp::Ite,
        vec![
            args[0].clone(),
            std::sync::Arc::new(ChcExpr::Int(i128::try_from(then_value).ok()?)),
            std::sync::Arc::new(ChcExpr::Int(i128::try_from(else_value).ok()?)),
        ],
    ))
}

fn bool_bitvec_sign_extract_eq_result(lhs: &ChcExpr, rhs: &ChcExpr) -> Option<bool> {
    bool_bitvec_sign_extract_eq_sides(lhs, rhs)
        .or_else(|| bool_bitvec_sign_extract_eq_sides(rhs, lhs))
}

fn bool_bitvec_sign_extract_eq_sides(lhs: &ChcExpr, rhs: &ChcExpr) -> Option<bool> {
    let ChcExpr::BitVec(expected, 1) = rhs else {
        return None;
    };
    let ChcExpr::Op(ChcOp::BvExtract(hi, lo), extract_args) = lhs else {
        return None;
    };
    if extract_args.len() != 1 || hi != lo {
        return None;
    }
    let (_, width) = bool_bitvec_ite_payload(extract_args[0].as_ref())?;
    if width <= 1 || *hi + 1 != width {
        return None;
    }
    Some(*expected == 0)
}

fn pow2_u128(width: u32) -> Option<u128> {
    1_u128.checked_shl(width)
}

fn modulus_to_pow2_width(modulus: u128) -> Option<u32> {
    (modulus > 1 && modulus.is_power_of_two()).then_some(modulus.trailing_zeros())
}

fn validation_interval_atom(expr: &ChcExpr) -> Option<(ChcOp, &ChcExpr, &ChcExpr)> {
    let ChcExpr::Op(op @ (ChcOp::Eq | ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge), args) = expr
    else {
        return None;
    };
    if args.len() == 2 {
        Some((*op, args[0].as_ref(), args[1].as_ref()))
    } else {
        None
    }
}

fn negated_validation_comparison(op: ChcOp) -> ChcOp {
    match op {
        ChcOp::Lt => ChcOp::Ge,
        ChcOp::Le => ChcOp::Gt,
        ChcOp::Gt => ChcOp::Le,
        ChcOp::Ge => ChcOp::Lt,
        ChcOp::Eq => ChcOp::Ne,
        other => other,
    }
}

fn int_var_name(expr: &ChcExpr) -> Option<&str> {
    match expr {
        ChcExpr::Var(var) if var.sort == ChcSort::Int => Some(var.name.as_str()),
        _ => None,
    }
}

fn bool_var_name(expr: &ChcExpr) -> Option<&str> {
    match expr {
        ChcExpr::Var(var) if var.sort == ChcSort::Bool => Some(var.name.as_str()),
        _ => None,
    }
}

/// Validate the model against all CHC clauses using SMT.
#[cfg(test)]
#[allow(dead_code)] // exposed for future test callers
pub(super) fn validate_model(problem: &ChcProblem, model: &InvariantModel) -> bool {
    matches!(
        validate_model_with_algebraic_fallback(problem, model, &FxHashSet::default(), false, None,),
        AlgebraicValidationResult::Valid,
    )
}

#[allow(dead_code)] // retained for validation-only callers that do not need counters.
pub(super) fn validate_model_with_algebraic_fallback(
    problem: &ChcProblem,
    model: &InvariantModel,
    _algebraic_self_loop_preds: &FxHashSet<PredicateId>,
    verbose: bool,
    deadline: Option<Instant>,
) -> AlgebraicValidationResult {
    validate_model_with_algebraic_fallback_and_stats(
        problem,
        model,
        _algebraic_self_loop_preds,
        verbose,
        deadline,
    )
    .0
}

pub(super) fn validate_model_with_algebraic_fallback_and_stats(
    problem: &ChcProblem,
    model: &InvariantModel,
    _algebraic_self_loop_preds: &FxHashSet<PredicateId>,
    verbose: bool,
    deadline: Option<Instant>,
) -> (AlgebraicValidationResult, AlgebraicValidationStats) {
    let mut smt = problem.make_smt_context();
    let mut stats = AlgebraicValidationStats::default();
    let result =
        validate_model_with_smt_and_stats(problem, model, verbose, deadline, &mut smt, &mut stats);
    (result, stats)
}

#[cfg(test)]
pub(super) fn validate_model_with_forced_results_for_tests(
    problem: &ChcProblem,
    model: &InvariantModel,
    forced_results: impl IntoIterator<Item = SmtResult>,
) -> (AlgebraicValidationResult, AlgebraicValidationStats) {
    let mut smt = problem.make_smt_context();
    for result in forced_results {
        smt.push_forced_check_sat_result_for_tests(result);
    }
    let mut stats = AlgebraicValidationStats::default();
    let result =
        validate_model_with_smt_and_stats(problem, model, false, None, &mut smt, &mut stats);
    (result, stats)
}

fn validate_model_with_smt_and_stats(
    problem: &ChcProblem,
    model: &InvariantModel,
    verbose: bool,
    deadline: Option<Instant>,
    smt: &mut SmtContext,
    stats: &mut AlgebraicValidationStats,
) -> AlgebraicValidationResult {
    stats.record_attempt();
    for clause in problem.clauses() {
        // #8753: bail out if the outer algebraic deadline has elapsed so the
        // adaptive portfolio can hand control to PDR/IMC/TPA/LAWI.
        if let Some(deadline) = deadline {
            if Instant::now() >= deadline {
                if verbose {
                    safe_eprintln!("Algebraic: validation deadline exceeded, bailing out (#8753)");
                }
                stats.record_unknown();
                return AlgebraicValidationResult::DeadlineExceeded;
            }
        }

        let mut body_conjuncts: Vec<ChcExpr> = Vec::new();

        for (pred_id, args) in &clause.body.predicates {
            if let Some(interp) = model.get(pred_id) {
                let substitution: Vec<(ChcVar, ChcExpr)> = interp
                    .vars
                    .iter()
                    .zip(args.iter())
                    .map(|(v, a)| (v.clone(), a.clone()))
                    .collect();
                body_conjuncts.push(interp.formula.substitute(&substitution));
            }
        }

        if let Some(constraint) = &clause.body.constraint {
            body_conjuncts.push(constraint.clone());
        }

        let body_formula = conjoin(body_conjuncts);

        let head_formula = match &clause.head {
            ClauseHead::Predicate(pred_id, args) => {
                if let Some(interp) = model.get(pred_id) {
                    let substitution: Vec<(ChcVar, ChcExpr)> = interp
                        .vars
                        .iter()
                        .zip(args.iter())
                        .map(|(v, a)| (v.clone(), a.clone()))
                        .collect();
                    interp.formula.substitute(&substitution)
                } else {
                    ChcExpr::Bool(true)
                }
            }
            ClauseHead::False => ChcExpr::Bool(false),
        };

        // #9073: The syntactic/canonical fast-paths below
        // (validation_body_syntactically_implies_head and
        // validation_formula_proves_unsat) both recurse through
        // canonical_validation_expr, which is un-memoized over the expression
        // DAG and so expands shared subterms as a tree — super-linear, and
        // effectively non-terminating on very large clauses (e.g. the single
        // sally/oral_messages transition over 145 vars). Because these calls
        // carry no deadline, one of them can burn the entire CHC wall clock,
        // making ALGEBRAIC_PRESTAGE_BUDGET unenforceable and STARVING the real
        // portfolio (IMC/PDR/LAWI/DAR never run). node_count is bounded (stops
        // at the cap, expanding the DAG-as-tree exactly like the blowup), so it
        // flags precisely the dangerous clauses in O(cap) time. For oversized
        // clauses, skip the optimization-only short-circuits and rely on the
        // time-bounded SMT check below. Sound: the fast-paths only add early
        // `continue`s; correctness rests on the SMT validation, which is
        // unchanged and capped by `per_query_timeout`.
        // #9075: 2000 was too aggressive — it skipped the fast-path on large
        // but well-behaved clauses (e.g. sally/approximate_agreement approx.6,
        // which the canonical syntactic-unsat fast-path proves quickly where the
        // budgeted 500ms SMT check returns Unknown), regressing real solves
        // (sat -> unknown). The cap exists only to bound the un-memoized
        // canonical_validation_expr DAG-as-tree blowup (om1: ~1M+ tree nodes);
        // a clause whose tree is under this cap canonicalizes in well under the
        // per-clause budget, so set the cap high enough to clear normal large
        // clauses while still catching the exponential cases. node_count is
        // bounded by the cap, so even the check itself stays O(cap).
        const ALGEBRAIC_FASTPATH_NODE_CAP: usize = 100_000;
        let fastpath_ok = body_formula.node_count(ALGEBRAIC_FASTPATH_NODE_CAP + 1)
            <= ALGEBRAIC_FASTPATH_NODE_CAP
            && head_formula.node_count(ALGEBRAIC_FASTPATH_NODE_CAP + 1)
                <= ALGEBRAIC_FASTPATH_NODE_CAP;

        if fastpath_ok
            && validation_body_syntactically_implies_head(&body_formula, &head_formula, verbose)
        {
            continue;
        }

        // Check: body AND NOT(head) is UNSAT
        let check = ChcExpr::and(body_formula.clone(), ChcExpr::not(head_formula.clone()))
            .simplify_constants();
        if fastpath_ok && validation_formula_proves_unsat(&check) {
            continue;
        }

        smt.reset();
        // #8753: cap each query at `ALGEBRAIC_QUERY_TIMEOUT` (shrunk further if
        // the outer deadline is closer). Unbounded `check_sat` was burning the
        // entire CHC wall clock on NIA/LRA dual simplex loops and starving
        // PDR/IMC/TPA/LAWI.
        let per_query_timeout = match deadline {
            Some(d) => d
                .saturating_duration_since(Instant::now())
                .min(ALGEBRAIC_QUERY_TIMEOUT),
            None => ALGEBRAIC_QUERY_TIMEOUT,
        };
        if per_query_timeout.is_zero() {
            if verbose {
                safe_eprintln!(
                    "Algebraic: validation deadline exceeded pre-query, bailing out (#8753)"
                );
            }
            stats.record_unknown();
            return AlgebraicValidationResult::DeadlineExceeded;
        }
        stats.record_query();
        match smt.check_sat_with_timeout(&check, per_query_timeout) {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
            SmtResult::Unknown => {
                if triangular_accumulator_query_is_syntactically_unsat(&check) {
                    if verbose {
                        safe_eprintln!(
                            "Algebraic: discharged triangular accumulator query after SMT Unknown"
                        );
                    }
                    continue;
                }
                if verbose {
                    safe_eprintln!(
                        "Algebraic: original-clause validation rejected SMT Unknown on clause {:?}",
                        clause
                    );
                }
                stats.record_unknown();
                return AlgebraicValidationResult::Invalid;
            }
            result => {
                if verbose {
                    safe_eprintln!(
                        "Algebraic: validation failed on clause {:?} with result {:?}",
                        clause,
                        result
                    );
                }
                stats.record_failure();
                return AlgebraicValidationResult::Invalid;
            }
        }
    }

    stats.record_success();
    AlgebraicValidationResult::Valid
}

fn validation_body_syntactically_implies_head(
    body: &ChcExpr,
    head: &ChcExpr,
    verbose: bool,
) -> bool {
    if matches!(head.simplify_constants(), ChcExpr::Bool(true)) {
        return true;
    }
    if validation_formula_proves_unsat(body) {
        return true;
    }

    let alias_substitution = validation_alias_substitution(body);
    let mut implied: FxHashSet<String> = body
        .conjuncts()
        .into_iter()
        .map(|expr| validation_alias_normalized_expr_key(expr, &alias_substitution))
        .collect();
    collect_guarded_active_diff_implications(body, &mut Vec::new(), &mut implied);
    let active_diff_shape = extract_active_diff_invariant_shape(head);

    for conjunct in head.conjuncts() {
        if !validation_body_syntactically_implies_conjunct(
            body,
            conjunct,
            &implied,
            &alias_substitution,
            active_diff_shape.as_ref(),
        ) {
            if verbose {
                safe_eprintln!(
                    "Algebraic: syntactic implication missing head conjunct {:?}",
                    conjunct.simplify_constants()
                );
            }
            return false;
        }
    }
    true
}

fn validation_body_syntactically_implies_conjunct(
    body: &ChcExpr,
    conjunct: &ChcExpr,
    implied: &FxHashSet<String>,
    alias_substitution: &[(ChcVar, ChcExpr)],
    active_diff_shape: Option<&ActiveDiffInvariantShape>,
) -> bool {
    let conjunct = conjunct.simplify_constants();
    if matches!(conjunct, ChcExpr::Bool(true)) {
        return true;
    }

    if let Some(shape) = active_diff_shape {
        if active_diff_transition_syntactically_preserves_conjunct(body, &conjunct, shape) {
            return true;
        }
    }
    if validation_body_implies_linear_equality(body, &conjunct, alias_substitution) {
        return true;
    }
    if validation_body_implies_linear_inequality(body, &conjunct, alias_substitution) {
        return true;
    }
    if validation_body_implies_positive_product_lower_bound(body, &conjunct, alias_substitution) {
        return true;
    }
    if validation_body_preserves_linear_mod_residue(body, &conjunct, alias_substitution) {
        return true;
    }
    if validation_formula_proves_unsat(&ChcExpr::not(conjunct.clone()).simplify_constants()) {
        return true;
    }
    if validation_formula_proves_unsat(&ChcExpr::and(body.clone(), ChcExpr::not(conjunct.clone())))
    {
        return true;
    }
    if implied.contains(&validation_alias_normalized_expr_key(
        &conjunct,
        alias_substitution,
    )) {
        return true;
    }

    match &conjunct {
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            if let Some(condition) = validation_static_bool_result(args[0].as_ref()) {
                return validation_body_syntactically_implies_conjunct(
                    body,
                    args[if condition { 1 } else { 2 }].as_ref(),
                    implied,
                    alias_substitution,
                    active_diff_shape,
                );
            }
            false
        }
        ChcExpr::Op(ChcOp::And, args) => args.iter().all(|arg| {
            validation_body_syntactically_implies_conjunct(
                body,
                arg.as_ref(),
                implied,
                alias_substitution,
                active_diff_shape,
            )
        }),
        ChcExpr::Op(ChcOp::Or, args) => args.iter().any(|arg| {
            validation_body_syntactically_implies_conjunct(
                body,
                arg.as_ref(),
                implied,
                alias_substitution,
                active_diff_shape,
            )
        }),
        _ => false,
    }
}

fn validation_body_implies_positive_product_lower_bound(
    body: &ChcExpr,
    conjunct: &ChcExpr,
    alias_substitution: &[(ChcVar, ChcExpr)],
) -> bool {
    let simplified = conjunct.substitute(alias_substitution).simplify_constants();
    let Some((product, lower_bound)) = validation_product_lower_bound_atom(&simplified) else {
        return false;
    };
    if lower_bound > 1 {
        return false;
    }

    let ChcExpr::Op(ChcOp::Mul, factors) = product else {
        return false;
    };
    factors.iter().all(|factor| match factor.as_ref() {
        ChcExpr::Int(value) => *value >= 1,
        factor => {
            let positive_factor = ChcExpr::ge(factor.clone(), ChcExpr::Int(1)).simplify_constants();
            validation_body_implies_linear_inequality(body, &positive_factor, alias_substitution)
        }
    })
}

fn validation_product_lower_bound_atom(expr: &ChcExpr) -> Option<(&ChcExpr, i128)> {
    let ChcExpr::Op(op, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }

    match op {
        ChcOp::Ge => match (&*args[0], &*args[1]) {
            (product @ ChcExpr::Op(ChcOp::Mul, _), ChcExpr::Int(bound)) => Some((product, *bound)),
            _ => None,
        },
        ChcOp::Le => match (&*args[0], &*args[1]) {
            (ChcExpr::Int(bound), product @ ChcExpr::Op(ChcOp::Mul, _)) => Some((product, *bound)),
            _ => None,
        },
        ChcOp::Gt => match (&*args[0], &*args[1]) {
            (product @ ChcExpr::Op(ChcOp::Mul, _), ChcExpr::Int(bound)) => {
                bound.checked_add(1).map(|lower| (product, lower))
            }
            _ => None,
        },
        ChcOp::Lt => match (&*args[0], &*args[1]) {
            (ChcExpr::Int(bound), product @ ChcExpr::Op(ChcOp::Mul, _)) => {
                bound.checked_add(1).map(|lower| (product, lower))
            }
            _ => None,
        },
        _ => None,
    }
}

fn validation_body_implies_linear_equality(
    body: &ChcExpr,
    conjunct: &ChcExpr,
    alias_substitution: &[(ChcVar, ChcExpr)],
) -> bool {
    let substitution = validation_body_linear_substitution(body, alias_substitution);
    // Every substitution entry `var -> expr` is an equality entailed by the
    // body, so substituting equals-for-equals preserves body-equivalence. If
    // the conjunct collapses to `true` under it (e.g. `F = G` with body
    // equalities `A = B`, `F = A + 1`, `G = B + 1` collapsing both sides to
    // `A + 1`), the body implies the conjunct outright. Without this check the
    // key comparison below misses identically-true equalities because
    // `simplify_constants` folds them away before a linear key can be built.
    if matches!(
        conjunct.substitute(&substitution).simplify_constants(),
        ChcExpr::Bool(true)
    ) {
        return true;
    }
    if let Some(head_key) = validation_linear_equality_key(conjunct, &substitution) {
        if body.conjuncts().into_iter().any(|body_conjunct| {
            validation_linear_equality_key(body_conjunct, &substitution).as_deref()
                == Some(head_key.as_str())
        }) {
            return true;
        }
    }
    // Polynomial fallback: discharge equalities whose sides contain small
    // products of variables (e.g. the conserved quantity `2*D = C + C*C`
    // following from body equalities `2*B = A + A*A`, `C = A + 1`,
    // `D = B + C`). Both sides are expanded into monomial-keyed polynomials
    // after the body substitution; the head equality is implied when its
    // normalized difference polynomial is identically zero or matches a body
    // equality's normalized difference exactly (equal up to rational scale).
    // Monomials are treated as opaque atoms, which is sound: any model
    // assigns each monomial a single value, so equal normalized atom-linear
    // combinations denote the same constraint.
    let Some(head_poly) = validation_poly_equality_normalized(conjunct, &substitution) else {
        return false;
    };
    if head_poly.is_empty() {
        // lhs - rhs expanded to the zero polynomial: identically true.
        return true;
    }
    body.conjuncts().into_iter().any(|body_conjunct| {
        validation_poly_equality_normalized(body_conjunct, &substitution)
            .is_some_and(|body_poly| body_poly == head_poly)
    })
}

/// Monomial-keyed polynomial: sorted variable-name multiset -> coefficient.
/// The empty multiset keys the constant term.
type ValidationPolyExpr = std::collections::BTreeMap<Vec<String>, i128>;

/// Degree/size caps keep expansion bounded; checked arithmetic bails on
/// overflow instead of wrapping (a wrapped coefficient could make two
/// different polynomials compare equal, which would be unsound).
const VALIDATION_POLY_MAX_DEGREE: usize = 4;
const VALIDATION_POLY_MAX_TERMS: usize = 16;

/// Expand `lhs - rhs` of an integer equality into a normalized
/// monomial-keyed polynomial (gcd-reduced, deterministic sign). Returns
/// `None` for non-equalities or expressions outside the supported
/// Int/Var/Add/Sub/Neg/Mul fragment.
fn validation_poly_equality_normalized(
    expr: &ChcExpr,
    substitution: &[(ChcVar, ChcExpr)],
) -> Option<ValidationPolyExpr> {
    let simplified = expr.substitute(substitution).simplify_constants();
    let ChcExpr::Op(ChcOp::Eq, args) = &simplified else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let lhs = validation_poly_expr(args[0].as_ref())?;
    let rhs = validation_poly_expr(args[1].as_ref())?;
    let mut diff = validation_poly_sub(&lhs, &rhs)?;
    validation_poly_normalize(&mut diff)?;
    Some(diff)
}

fn validation_poly_expr(expr: &ChcExpr) -> Option<ValidationPolyExpr> {
    match expr {
        ChcExpr::Int(value) => {
            let mut poly = ValidationPolyExpr::new();
            if *value != 0 {
                poly.insert(Vec::new(), *value);
            }
            Some(poly)
        }
        ChcExpr::Var(var) if var.sort == ChcSort::Int => {
            let mut poly = ValidationPolyExpr::new();
            poly.insert(vec![var.name.clone()], 1);
            Some(poly)
        }
        ChcExpr::Op(ChcOp::Add, args) => {
            let mut result = ValidationPolyExpr::new();
            for arg in args {
                result = validation_poly_add(&result, &validation_poly_expr(arg)?)?;
            }
            Some(result)
        }
        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            let mut iter = args.iter();
            let mut result = validation_poly_expr(iter.next()?.as_ref())?;
            for arg in iter {
                result = validation_poly_sub(&result, &validation_poly_expr(arg)?)?;
            }
            Some(result)
        }
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            validation_poly_scale(&validation_poly_expr(args[0].as_ref())?, -1)
        }
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => validation_poly_mul(
            &validation_poly_expr(args[0].as_ref())?,
            &validation_poly_expr(args[1].as_ref())?,
        ),
        _ => None,
    }
}

fn validation_poly_add(
    lhs: &ValidationPolyExpr,
    rhs: &ValidationPolyExpr,
) -> Option<ValidationPolyExpr> {
    let mut result = lhs.clone();
    for (monomial, coeff) in rhs {
        let next = result
            .get(monomial)
            .copied()
            .unwrap_or(0)
            .checked_add(*coeff)?;
        if next == 0 {
            result.remove(monomial);
        } else {
            result.insert(monomial.clone(), next);
        }
    }
    (result.len() <= VALIDATION_POLY_MAX_TERMS).then_some(result)
}

fn validation_poly_scale(poly: &ValidationPolyExpr, scale: i128) -> Option<ValidationPolyExpr> {
    let mut result = ValidationPolyExpr::new();
    for (monomial, coeff) in poly {
        let scaled = coeff.checked_mul(scale)?;
        if scaled != 0 {
            result.insert(monomial.clone(), scaled);
        }
    }
    Some(result)
}

fn validation_poly_sub(
    lhs: &ValidationPolyExpr,
    rhs: &ValidationPolyExpr,
) -> Option<ValidationPolyExpr> {
    validation_poly_add(lhs, &validation_poly_scale(rhs, -1)?)
}

fn validation_poly_mul(
    lhs: &ValidationPolyExpr,
    rhs: &ValidationPolyExpr,
) -> Option<ValidationPolyExpr> {
    let mut result = ValidationPolyExpr::new();
    for (lhs_monomial, lhs_coeff) in lhs {
        for (rhs_monomial, rhs_coeff) in rhs {
            let mut monomial: Vec<String> = lhs_monomial
                .iter()
                .chain(rhs_monomial.iter())
                .cloned()
                .collect();
            monomial.sort_unstable();
            if monomial.len() > VALIDATION_POLY_MAX_DEGREE {
                return None;
            }
            let term = lhs_coeff.checked_mul(*rhs_coeff)?;
            let next = result
                .get(&monomial)
                .copied()
                .unwrap_or(0)
                .checked_add(term)?;
            if next == 0 {
                result.remove(&monomial);
            } else {
                result.insert(monomial, next);
            }
        }
    }
    (result.len() <= VALIDATION_POLY_MAX_TERMS).then_some(result)
}

/// Divide by the gcd of all coefficients and fix a deterministic sign (the
/// first monomial in BTreeMap order gets a positive coefficient) so that
/// equalities equal up to rational scale produce identical maps.
fn validation_poly_normalize(poly: &mut ValidationPolyExpr) -> Option<()> {
    if poly.is_empty() {
        return Some(());
    }
    let mut gcd: i128 = 0;
    for coeff in poly.values() {
        let abs = coeff.checked_abs()?;
        gcd = if gcd == 0 { abs } else { gcd_i128(gcd, abs) };
    }
    let leading_negative = poly.values().next().copied()? < 0;
    let divisor = if leading_negative { -gcd } else { gcd };
    if divisor != 1 {
        for coeff in poly.values_mut() {
            *coeff /= divisor;
        }
    }
    Some(())
}

fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

fn validation_body_implies_linear_inequality(
    body: &ChcExpr,
    conjunct: &ChcExpr,
    alias_substitution: &[(ChcVar, ChcExpr)],
) -> bool {
    let substitution = validation_body_linear_substitution(body, alias_substitution);
    let Some(head_key) = validation_linear_inequality_key(conjunct, &substitution) else {
        return false;
    };
    if body.conjuncts().into_iter().any(|body_conjunct| {
        validation_linear_inequality_key(body_conjunct, &substitution).as_deref()
            == Some(head_key.as_str())
    }) {
        return true;
    }

    let Some(head_expr) = validation_linear_inequality_expr(conjunct, &substitution) else {
        return false;
    };
    let mut body_equalities = Vec::new();
    let mut body_inequalities = Vec::new();
    for body_conjunct in body.conjuncts() {
        if let Some(equality) = validation_linear_equality_expr(body_conjunct, &substitution) {
            body_equalities.push(equality);
        }
        if let Some(inequality) = validation_linear_inequality_expr(body_conjunct, &substitution) {
            body_inequalities.push(inequality);
        }
    }
    body_inequalities.iter().any(|inequality| {
        (1..=4).any(|scale| {
            let Some(scaled_inequality) = validation_linear_expr_checked_scale(inequality, scale)
            else {
                return false;
            };
            let Some(residual) = validation_linear_expr_checked_sub(&head_expr, &scaled_inequality)
            else {
                return false;
            };
            validation_linear_expr_in_equality_span_bounded(&residual, &body_equalities)
        })
    })
}

fn validation_linear_inequality_key(
    expr: &ChcExpr,
    substitution: &[(ChcVar, ChcExpr)],
) -> Option<String> {
    let linear = validation_linear_inequality_expr(expr, substitution)?;
    validation_normalized_linear_inequality_key(&linear)
}

fn validation_linear_inequality_expr(
    expr: &ChcExpr,
    substitution: &[(ChcVar, ChcExpr)],
) -> Option<ValidationLinearExpr> {
    let simplified = expr.substitute(substitution).simplify_constants();
    let ChcExpr::Op(op, args) = &simplified else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let linear = match op {
        ChcOp::Le => validation_linear_expr_sub(args[0].as_ref(), args[1].as_ref())?,
        ChcOp::Ge => validation_linear_expr_sub(args[1].as_ref(), args[0].as_ref())?,
        ChcOp::Lt => {
            let expr = validation_linear_expr_sub(args[0].as_ref(), args[1].as_ref())?;
            validation_linear_expr_add_constant(&expr, 1)
        }
        ChcOp::Gt => {
            let expr = validation_linear_expr_sub(args[1].as_ref(), args[0].as_ref())?;
            validation_linear_expr_add_constant(&expr, 1)
        }
        _ => return None,
    };
    Some(linear)
}

fn validation_linear_equality_key(
    expr: &ChcExpr,
    substitution: &[(ChcVar, ChcExpr)],
) -> Option<String> {
    let linear = validation_linear_equality_expr(expr, substitution)?;
    validation_normalized_linear_expr_key(&linear)
}

fn validation_linear_equality_expr(
    expr: &ChcExpr,
    substitution: &[(ChcVar, ChcExpr)],
) -> Option<ValidationLinearExpr> {
    let simplified = expr.substitute(substitution).simplify_constants();
    let ChcExpr::Op(ChcOp::Eq, args) = &simplified else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    validation_linear_expr_sub(args[0].as_ref(), args[1].as_ref())
}

fn validation_normalized_linear_expr_key(expr: &ValidationLinearExpr) -> Option<String> {
    let mut gcd = 0;
    for value in expr.coeffs.values().copied().chain([expr.constant]) {
        if value == 0 {
            continue;
        }
        let abs = value.checked_abs()?;
        gcd = if gcd == 0 {
            abs
        } else {
            validation_gcd_i128(gcd, abs)
        };
    }
    if gcd == 0 {
        return Some("0".to_string());
    }

    let mut terms: Vec<_> = expr
        .coeffs
        .iter()
        .map(|(name, coeff)| (name.as_str(), coeff / gcd))
        .collect();
    terms.sort_unstable_by_key(|(name, _)| *name);
    let mut constant = expr.constant / gcd;
    let sign = terms
        .iter()
        .find_map(|(_, coeff)| (*coeff != 0).then_some(coeff.signum()))
        .unwrap_or_else(|| constant.signum());
    if sign < 0 {
        for (_, coeff) in &mut terms {
            *coeff = coeff.checked_neg()?;
        }
        constant = constant.checked_neg()?;
    }

    let mut key = format!("const={constant}");
    for (name, coeff) in terms {
        if coeff != 0 {
            key.push_str(&format!(";{name}={coeff}"));
        }
    }
    Some(key)
}

fn validation_normalized_linear_inequality_key(expr: &ValidationLinearExpr) -> Option<String> {
    let gcd = validation_linear_expr_gcd(expr)?;
    let mut terms: Vec<_> = expr
        .coeffs
        .iter()
        .map(|(name, coeff)| (name.as_str(), coeff / gcd))
        .collect();
    terms.sort_unstable_by_key(|(name, _)| *name);
    let constant = expr.constant / gcd;

    let mut key = format!("const={constant}");
    for (name, coeff) in terms {
        if coeff != 0 {
            key.push_str(&format!(";{name}={coeff}"));
        }
    }
    Some(key)
}

fn validation_linear_expr_gcd(expr: &ValidationLinearExpr) -> Option<i128> {
    let mut gcd = 0;
    for value in expr.coeffs.values().copied().chain([expr.constant]) {
        if value == 0 {
            continue;
        }
        let abs = value.checked_abs()?;
        gcd = if gcd == 0 {
            abs
        } else {
            validation_gcd_i128(gcd, abs)
        };
    }
    (gcd != 0).then_some(gcd)
}

fn validation_linear_expr_in_equality_span_bounded(
    target: &ValidationLinearExpr,
    equalities: &[ValidationLinearExpr],
) -> bool {
    const MAX_EQUALITIES: usize = 6;
    if validation_linear_expr_is_zero(target) {
        return true;
    }
    if equalities.len() > MAX_EQUALITIES {
        return false;
    }
    validation_linear_expr_in_equality_span_rec(target, equalities, 0)
}

fn validation_linear_expr_in_equality_span_rec(
    residual: &ValidationLinearExpr,
    equalities: &[ValidationLinearExpr],
    idx: usize,
) -> bool {
    if validation_linear_expr_is_zero(residual) {
        return true;
    }
    if idx >= equalities.len() {
        return false;
    }
    if validation_linear_expr_in_equality_span_rec(residual, equalities, idx + 1) {
        return true;
    }
    for coeff in -4..=4 {
        if coeff == 0 {
            continue;
        }
        let Some(scaled) = validation_linear_expr_checked_scale(&equalities[idx], coeff) else {
            continue;
        };
        let Some(next) = validation_linear_expr_checked_sub(residual, &scaled) else {
            continue;
        };
        if validation_linear_expr_in_equality_span_rec(&next, equalities, idx + 1) {
            return true;
        }
    }
    false
}

fn validation_linear_expr_checked_sub(
    lhs: &ValidationLinearExpr,
    rhs: &ValidationLinearExpr,
) -> Option<ValidationLinearExpr> {
    let negated = validation_linear_expr_checked_scale(rhs, -1)?;
    validation_linear_expr_checked_add(lhs, &negated)
}

fn validation_linear_expr_checked_add(
    lhs: &ValidationLinearExpr,
    rhs: &ValidationLinearExpr,
) -> Option<ValidationLinearExpr> {
    let mut coeffs = lhs.coeffs.clone();
    for (name, coeff) in &rhs.coeffs {
        let next = coeffs.get(name).copied().unwrap_or(0).checked_add(*coeff)?;
        if next == 0 {
            coeffs.remove(name);
        } else {
            coeffs.insert(name.clone(), next);
        }
    }
    Some(ValidationLinearExpr {
        coeffs,
        constant: lhs.constant.checked_add(rhs.constant)?,
    })
}

fn validation_linear_expr_checked_scale(
    expr: &ValidationLinearExpr,
    scale: i128,
) -> Option<ValidationLinearExpr> {
    let mut coeffs = FxHashMap::default();
    for (name, coeff) in &expr.coeffs {
        let scaled = coeff.checked_mul(scale)?;
        if scaled != 0 {
            coeffs.insert(name.clone(), scaled);
        }
    }
    Some(ValidationLinearExpr {
        coeffs,
        constant: expr.constant.checked_mul(scale)?,
    })
}

fn validation_linear_expr_checked_add_constant(
    expr: &ValidationLinearExpr,
    constant: i128,
) -> Option<ValidationLinearExpr> {
    Some(ValidationLinearExpr {
        coeffs: expr.coeffs.clone(),
        constant: expr.constant.checked_add(constant)?,
    })
}

fn validation_linear_expr_is_zero(expr: &ValidationLinearExpr) -> bool {
    expr.constant == 0 && expr.coeffs.is_empty()
}

#[derive(Clone, Debug)]
struct ValidationLinearModResidue {
    expr: ValidationLinearExpr,
    modulus: i128,
    residue: i128,
}

fn validation_body_preserves_linear_mod_residue(
    body: &ChcExpr,
    conjunct: &ChcExpr,
    alias_substitution: &[(ChcVar, ChcExpr)],
) -> bool {
    let substitution = validation_body_linear_substitution(body, alias_substitution);
    let head_expr = conjunct.substitute(&substitution).simplify_constants();
    let Some(head_residue) = validation_linear_mod_residue_atom(&head_expr) else {
        return false;
    };

    body.conjuncts().into_iter().any(|body_conjunct| {
        let body_expr = body_conjunct.substitute(&substitution).simplify_constants();
        validation_linear_mod_residue_atom(&body_expr).is_some_and(|body_residue| {
            validation_linear_mod_residue_implies(&body_residue, &head_residue)
        })
    }) || validation_body_equalities_imply_linear_mod_residue(body, &substitution, &head_residue)
}

fn validation_body_equalities_imply_linear_mod_residue(
    body: &ChcExpr,
    substitution: &[(ChcVar, ChcExpr)],
    head_residue: &ValidationLinearModResidue,
) -> bool {
    let equalities: Vec<_> = body
        .conjuncts()
        .into_iter()
        .filter_map(|body_conjunct| validation_linear_equality_expr(body_conjunct, substitution))
        .collect();
    (-4..=4).any(|multiple| {
        let Some(offset) = head_residue
            .modulus
            .checked_mul(multiple)
            .and_then(|value| value.checked_add(head_residue.residue))
        else {
            return false;
        };
        let Some(residual) =
            validation_linear_expr_checked_add_constant(&head_residue.expr, -offset)
        else {
            return false;
        };
        validation_linear_expr_in_equality_span_bounded(&residual, &equalities)
    })
}

fn validation_body_linear_substitution(
    body: &ChcExpr,
    alias_substitution: &[(ChcVar, ChcExpr)],
) -> Vec<(ChcVar, ChcExpr)> {
    let mut substitution = alias_substitution.to_vec();
    let max_rounds = body.conjuncts().len().saturating_add(4).clamp(1, 32);
    for _ in 0..max_rounds {
        let before = substitution.len();
        for conjunct in body.conjuncts() {
            let simplified = conjunct.substitute(&substitution).simplify_constants();
            let Some((var, expr)) = validation_linear_expr_alias(&simplified) else {
                continue;
            };
            if substitution.iter().any(|(existing, _)| existing == &var)
                || expr.contains_var_name(&var.name)
                || expr.sort() != var.sort
            {
                continue;
            }
            substitution.push((var, expr));
        }
        if substitution.len() == before {
            break;
        }
    }
    substitution
}

fn validation_linear_expr_alias(expr: &ChcExpr) -> Option<(ChcVar, ChcExpr)> {
    let ChcExpr::Op(ChcOp::Eq, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    validation_linear_expr_alias_sides(args[0].as_ref(), args[1].as_ref())
        .or_else(|| validation_linear_expr_alias_sides(args[1].as_ref(), args[0].as_ref()))
}

fn validation_linear_expr_alias_sides(lhs: &ChcExpr, rhs: &ChcExpr) -> Option<(ChcVar, ChcExpr)> {
    let ChcExpr::Var(var) = lhs else {
        return None;
    };
    if var.sort != ChcSort::Int || matches!(rhs, ChcExpr::Var(_)) {
        return None;
    }
    validation_linear_expr(rhs)?;
    Some((var.clone(), rhs.clone()))
}

fn validation_linear_mod_residue_atom(expr: &ChcExpr) -> Option<ValidationLinearModResidue> {
    let simplified = expr.simplify_constants();
    let ChcExpr::Op(ChcOp::Eq, args) = &simplified else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    validation_linear_mod_residue_from_parts(args[0].as_ref(), args[1].as_ref())
        .or_else(|| validation_linear_mod_residue_from_parts(args[1].as_ref(), args[0].as_ref()))
}

fn validation_linear_mod_residue_from_parts(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
) -> Option<ValidationLinearModResidue> {
    let ChcExpr::Op(ChcOp::Mod, mod_args) = lhs else {
        return None;
    };
    if mod_args.len() != 2 {
        return None;
    }
    let modulus = mod_args[1].as_i128()?;
    if modulus <= 1 {
        return None;
    }
    let residue = rhs.as_i128()?.rem_euclid(modulus);
    Some(ValidationLinearModResidue {
        expr: validation_linear_expr(mod_args[0].as_ref())?,
        modulus,
        residue,
    })
}

fn validation_linear_mod_residue_implies(
    body: &ValidationLinearModResidue,
    head: &ValidationLinearModResidue,
) -> bool {
    if body.modulus % head.modulus != 0 {
        return false;
    }
    let modulus = i128::from(head.modulus);
    let mut names: FxHashSet<&str> = FxHashSet::default();
    names.extend(body.expr.coeffs.keys().map(String::as_str));
    names.extend(head.expr.coeffs.keys().map(String::as_str));
    for name in names {
        let body_coeff = i128::from(body.expr.coeffs.get(name).copied().unwrap_or(0));
        let head_coeff = i128::from(head.expr.coeffs.get(name).copied().unwrap_or(0));
        if (head_coeff - body_coeff).rem_euclid(modulus) != 0 {
            return false;
        }
    }
    let constant_delta = i128::from(head.expr.constant) - i128::from(body.expr.constant);
    let implied_residue = (i128::from(body.residue) + constant_delta).rem_euclid(modulus);
    implied_residue == i128::from(head.residue.rem_euclid(head.modulus))
}

fn validation_alias_normalized_expr_key(
    expr: &ChcExpr,
    substitution: &[(ChcVar, ChcExpr)],
) -> String {
    if substitution.is_empty() {
        return validation_expr_key(&expr.simplify_constants());
    }
    validation_expr_key(&expr.substitute(substitution).simplify_constants())
}

fn validation_alias_substitution(body: &ChcExpr) -> Vec<(ChcVar, ChcExpr)> {
    let mut parent: FxHashMap<ChcVar, ChcVar> = FxHashMap::default();
    for conjunct in body.conjuncts() {
        let ChcExpr::Op(ChcOp::Eq, args) = conjunct else {
            continue;
        };
        if args.len() != 2 {
            continue;
        }
        let (ChcExpr::Var(lhs), ChcExpr::Var(rhs)) = (args[0].as_ref(), args[1].as_ref()) else {
            continue;
        };
        if lhs.sort != rhs.sort {
            continue;
        }
        validation_alias_union(&mut parent, lhs.clone(), rhs.clone());
    }

    let keys: Vec<ChcVar> = parent.keys().cloned().collect();
    let mut substitution = Vec::new();
    for var in keys {
        let root = validation_alias_find(&mut parent, &var);
        if root != var {
            substitution.push((var, ChcExpr::var(root)));
        }
    }
    for conjunct in body.conjuncts() {
        let Some((var, expr)) = validation_bool_expr_alias(conjunct) else {
            continue;
        };
        if substitution.iter().any(|(existing, _)| existing == &var)
            || expr.contains_var_name(&var.name)
        {
            continue;
        }
        let expr = expr.substitute(&substitution).simplify_constants();
        if !expr.contains_var_name(&var.name) {
            substitution.push((var, expr));
        }
    }
    substitution
}

fn validation_bool_expr_alias(expr: &ChcExpr) -> Option<(ChcVar, ChcExpr)> {
    let ChcExpr::Op(ChcOp::Eq, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    validation_bool_expr_alias_sides(args[0].as_ref(), args[1].as_ref())
        .or_else(|| validation_bool_expr_alias_sides(args[1].as_ref(), args[0].as_ref()))
}

fn validation_bool_expr_alias_sides(lhs: &ChcExpr, rhs: &ChcExpr) -> Option<(ChcVar, ChcExpr)> {
    let ChcExpr::Var(var) = lhs else {
        return None;
    };
    if var.sort != ChcSort::Bool || rhs.sort() != ChcSort::Bool {
        return None;
    }
    Some((var.clone(), rhs.clone()))
}

fn validation_alias_union(parent: &mut FxHashMap<ChcVar, ChcVar>, lhs: ChcVar, rhs: ChcVar) {
    parent.entry(lhs.clone()).or_insert_with(|| lhs.clone());
    parent.entry(rhs.clone()).or_insert_with(|| rhs.clone());
    let lhs_root = validation_alias_find(parent, &lhs);
    let rhs_root = validation_alias_find(parent, &rhs);
    if lhs_root == rhs_root {
        return;
    }
    let (keep, replace) =
        if validation_alias_var_key(&lhs_root) <= validation_alias_var_key(&rhs_root) {
            (lhs_root, rhs_root)
        } else {
            (rhs_root, lhs_root)
        };
    parent.insert(replace, keep);
}

fn validation_alias_find(parent: &mut FxHashMap<ChcVar, ChcVar>, var: &ChcVar) -> ChcVar {
    let Some(current) = parent.get(var).cloned() else {
        return var.clone();
    };
    if current == *var {
        return current;
    }
    let root = validation_alias_find(parent, &current);
    parent.insert(var.clone(), root.clone());
    root
}

fn validation_alias_var_key(var: &ChcVar) -> String {
    format!("{:?}:{}", var.sort, var.name)
}

fn active_diff_transition_syntactically_preserves_conjunct(
    body: &ChcExpr,
    conjunct: &ChcExpr,
    shape: &ActiveDiffInvariantShape,
) -> bool {
    let Some((active_a, active_b, epsilon, value_a, value_b)) =
        parse_active_diff_invariant_clause(conjunct)
    else {
        return false;
    };
    if shape
        .epsilon
        .as_ref()
        .is_none_or(|shape_epsilon| shape_epsilon.name != epsilon.name)
        || !shape.has_active(&active_a)
        || !shape.has_active(&active_b)
        || !shape.has_value(&value_a)
        || !shape.has_value(&value_b)
    {
        return false;
    }
    (body_has_guarded_average_assignment(body, &active_a, &value_a)
        && body_has_guarded_average_assignment(body, &active_b, &value_b))
        || (body_has_guarded_average_assignment(body, &active_a, &value_b)
            && body_has_guarded_average_assignment(body, &active_b, &value_a))
}

struct ActiveDiffInvariantShape {
    epsilon: Option<ChcVar>,
    active_vars: Vec<ChcVar>,
    value_vars: Vec<ChcVar>,
}

impl ActiveDiffInvariantShape {
    fn has_active(&self, var: &ChcVar) -> bool {
        self.active_vars
            .iter()
            .any(|active| active.name == var.name)
    }

    fn has_value(&self, var: &ChcVar) -> bool {
        self.value_vars.iter().any(|value| value.name == var.name)
    }
}

fn extract_active_diff_invariant_shape(head: &ChcExpr) -> Option<ActiveDiffInvariantShape> {
    let mut active_vars: Vec<ChcVar> = Vec::new();
    let mut value_vars: Vec<ChcVar> = Vec::new();
    let mut eps: Option<ChcVar> = None;
    let mut diff_clause_count = 0usize;

    for conjunct in head.conjuncts() {
        let Some((active_a, active_b, clause_eps, value_a, value_b)) =
            parse_active_diff_invariant_clause(conjunct)
        else {
            continue;
        };
        if let Some(existing) = &eps {
            if existing.name != clause_eps.name {
                return None;
            }
        } else {
            eps = Some(clause_eps);
        }
        push_unique_var(&mut active_vars, active_a);
        push_unique_var(&mut active_vars, active_b);
        push_unique_var(&mut value_vars, value_a);
        push_unique_var(&mut value_vars, value_b);
        diff_clause_count += 1;
    }

    if active_vars.len() != value_vars.len() || active_vars.len() < 2 {
        return None;
    }
    let expected_diff_clauses = active_vars.len() * active_vars.len().saturating_sub(1);
    if diff_clause_count < expected_diff_clauses {
        return None;
    }

    Some(ActiveDiffInvariantShape {
        epsilon: eps,
        active_vars,
        value_vars,
    })
}

fn parse_active_diff_invariant_clause(
    expr: &ChcExpr,
) -> Option<(ChcVar, ChcVar, ChcVar, ChcVar, ChcVar)> {
    let ChcExpr::Op(ChcOp::Or, args) = expr else {
        return None;
    };
    let mut active = Vec::new();
    let mut diff = None;
    for arg in args {
        if let Some(var) = negative_bool_var(arg) {
            active.push(var);
            continue;
        }
        if let Some(parsed) = parse_negated_epsilon_distance_guard(arg) {
            diff = Some(parsed);
        }
    }
    if active.len() != 2 {
        return None;
    }
    let (eps, value_a, value_b) = diff?;
    Some((active[0].clone(), active[1].clone(), eps, value_a, value_b))
}

fn push_unique_var(vars: &mut Vec<ChcVar>, var: ChcVar) {
    if !vars.iter().any(|existing| existing.name == var.name) {
        vars.push(var);
    }
}

fn body_has_guarded_average_assignment(body: &ChcExpr, active: &ChcVar, value: &ChcVar) -> bool {
    match body {
        ChcExpr::Op(ChcOp::Or, args) => {
            let has_guard = args
                .iter()
                .any(|arg| negative_bool_var(arg).is_some_and(|var| var.name == active.name));
            has_guard && args.iter().any(|arg| is_assignment_to_average(arg, value))
        }
        ChcExpr::Op(_, args) => args
            .iter()
            .any(|arg| body_has_guarded_average_assignment(arg, active, value)),
        _ => false,
    }
}

fn is_assignment_to_average(expr: &ChcExpr, value: &ChcVar) -> bool {
    let ChcExpr::Op(ChcOp::Eq, args) = expr else {
        return false;
    };
    if args.len() != 2 {
        return false;
    }
    match (args[0].as_ref(), args[1].as_ref()) {
        (ChcExpr::Var(lhs), rhs) if lhs.name == value.name => is_average_expr(rhs),
        (lhs, ChcExpr::Var(rhs)) if rhs.name == value.name => is_average_expr(lhs),
        _ => false,
    }
}

fn is_average_expr(expr: &ChcExpr) -> bool {
    let ChcExpr::Op(ChcOp::Add, args) = expr else {
        return false;
    };
    args.len() == 2 && args.iter().all(|arg| is_half_scaled_expr(arg))
}

fn is_half_scaled_expr(expr: &ChcExpr) -> bool {
    let ChcExpr::Op(ChcOp::Mul, args) = expr else {
        return false;
    };
    args.len() == 2
        && args
            .iter()
            .any(|arg| matches!(arg.as_ref(), ChcExpr::Real(1, 2)))
}

fn collect_guarded_active_diff_implications(
    expr: &ChcExpr,
    active_context: &mut Vec<ChcVar>,
    implied: &mut FxHashSet<String>,
) {
    if let Some((epsilon, value_a, value_b)) = parse_negated_epsilon_distance_guard(expr) {
        let mut active = active_context.clone();
        active.sort_by(|a, b| a.name.cmp(&b.name));
        active.dedup_by(|a, b| a.name == b.name);
        if active.len() == 2 {
            let clause = ChcExpr::or_all([
                ChcExpr::not(ChcExpr::var(active[0].clone())),
                ChcExpr::not(ChcExpr::var(active[1].clone())),
                ChcExpr::not(ChcExpr::le(
                    ChcExpr::var(epsilon),
                    ChcExpr::sub(ChcExpr::var(value_a), ChcExpr::var(value_b)),
                )),
            ]);
            implied.insert(validation_expr_key(&clause));
        }
        return;
    }

    let ChcExpr::Op(op, args) = expr else {
        return;
    };

    match op {
        ChcOp::And => {
            for arg in args {
                collect_guarded_active_diff_implications(arg, active_context, implied);
            }
        }
        ChcOp::Or => {
            let mut guards = Vec::new();
            let mut guarded_payloads = Vec::new();
            for arg in args {
                if let Some(var) = negative_bool_var(arg) {
                    guards.push(var);
                } else {
                    guarded_payloads.push(arg);
                }
            }
            if !guards.is_empty() && guarded_payloads.len() == 1 {
                let original_len = active_context.len();
                for guard in guards {
                    if !active_context
                        .iter()
                        .any(|active| active.name == guard.name)
                    {
                        active_context.push(guard);
                    }
                }
                collect_guarded_active_diff_implications(
                    guarded_payloads[0],
                    active_context,
                    implied,
                );
                active_context.truncate(original_len);
            }
        }
        ChcOp::Not => {}
        _ => {
            for arg in args {
                collect_guarded_active_diff_implications(arg, active_context, implied);
            }
        }
    }
}

fn negative_bool_var(expr: &ChcExpr) -> Option<ChcVar> {
    let ChcExpr::Op(ChcOp::Not, args) = expr else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    match args[0].as_ref() {
        ChcExpr::Var(var) if matches!(var.sort, ChcSort::Bool) => Some(var.clone()),
        _ => None,
    }
}

fn parse_negated_epsilon_distance_guard(expr: &ChcExpr) -> Option<(ChcVar, ChcVar, ChcVar)> {
    let ChcExpr::Op(ChcOp::Not, args) = expr else {
        return None;
    };
    if args.len() != 1 {
        return None;
    }
    parse_epsilon_distance_guard(args[0].as_ref())
}

fn parse_epsilon_distance_guard(expr: &ChcExpr) -> Option<(ChcVar, ChcVar, ChcVar)> {
    let ChcExpr::Op(ChcOp::Le, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let ChcExpr::Var(epsilon) = args[0].as_ref() else {
        return None;
    };
    if !matches!(epsilon.sort, ChcSort::Real | ChcSort::Int) {
        return None;
    }
    let (value_a, value_b) = parse_var_difference(args[1].as_ref())?;
    Some((epsilon.clone(), value_a, value_b))
}

fn parse_var_difference(expr: &ChcExpr) -> Option<(ChcVar, ChcVar)> {
    match expr {
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            let ChcExpr::Var(lhs) = args[0].as_ref() else {
                return None;
            };
            let ChcExpr::Var(rhs) = args[1].as_ref() else {
                return None;
            };
            Some((lhs.clone(), rhs.clone()))
        }
        ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
            if let (ChcExpr::Var(lhs), Some(rhs)) =
                (args[0].as_ref(), parse_negated_var(args[1].as_ref()))
            {
                return Some((lhs.clone(), rhs));
            }
            if let (ChcExpr::Var(lhs), Some(rhs)) =
                (args[1].as_ref(), parse_negated_var(args[0].as_ref()))
            {
                return Some((lhs.clone(), rhs));
            }
            None
        }
        _ => None,
    }
}

fn parse_negated_var(expr: &ChcExpr) -> Option<ChcVar> {
    match expr {
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => match args[0].as_ref() {
            ChcExpr::Var(var) => Some(var.clone()),
            _ => None,
        },
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            if is_minus_one(args[0].as_ref()) {
                if let ChcExpr::Var(var) = args[1].as_ref() {
                    return Some(var.clone());
                }
            }
            if is_minus_one(args[1].as_ref()) {
                if let ChcExpr::Var(var) = args[0].as_ref() {
                    return Some(var.clone());
                }
            }
            None
        }
        _ => None,
    }
}

fn is_minus_one(expr: &ChcExpr) -> bool {
    matches!(expr, ChcExpr::Int(-1) | ChcExpr::Real(-1, 1))
        || matches!(expr, ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 && matches!(args[0].as_ref(), ChcExpr::Int(1) | ChcExpr::Real(1, 1)))
}

fn validation_expr_key(expr: &ChcExpr) -> String {
    format!("{:?}", canonical_validation_expr(expr))
}

fn canonical_bool_domain_int_expr(expr: &ChcExpr) -> Option<ChcExpr> {
    if let Some(as_int) = bool_bitvec_ite_as_int_expr(expr) {
        return Some(as_int);
    }
    if let ChcExpr::Op(ChcOp::Bv2Nat, args) = expr {
        if args.len() == 1 {
            return bool_bitvec_ite_as_int_expr(args[0].as_ref());
        }
    }
    if let Some((payload, width)) = signed_bv_to_int_payload_and_width(expr) {
        if width > 1 && validation_expr_has_bool_domain(payload) {
            return bool_domain_payload_to_int_expr(payload);
        }
    }
    if let Some((payload, _)) = unsigned_bv_to_int_payload(expr) {
        if validation_expr_has_bool_domain(payload) {
            return bool_domain_payload_to_int_expr(payload);
        }
    }
    None
}

fn bool_domain_payload_to_int_expr(payload: &ChcExpr) -> Option<ChcExpr> {
    if matches!(payload.sort(), ChcSort::Int) {
        return Some(payload.clone());
    }
    bool_bitvec_ite_as_int_expr(payload)
}

fn canonical_validation_expr(expr: &ChcExpr) -> ChcExpr {
    if let Some(as_int) = canonical_bool_domain_int_expr(expr) {
        return canonical_validation_expr(&as_int);
    }
    if let ChcExpr::Op(ChcOp::Ite, args) = expr {
        if args.len() == 3 {
            if let Some(condition) = validation_static_bool_result(args[0].as_ref()) {
                return canonical_validation_expr(args[if condition { 1 } else { 2 }].as_ref());
            }
        }
    }
    match expr {
        ChcExpr::Op(
            op @ (ChcOp::And | ChcOp::Or | ChcOp::Add | ChcOp::Mul | ChcOp::Eq | ChcOp::Ne),
            args,
        ) => {
            let mut canonical_args: Vec<ChcExpr> = args
                .iter()
                .map(|arg| canonical_validation_expr(arg))
                .collect();
            // Perf: sort_by_cached_key formats each arg's Debug string exactly
            // once (n times) instead of sort_by_key re-evaluating it on every
            // comparison (O(n log n) full-subtree Debug formats). Identical
            // canonical ordering; this is a hot path in algebraic-invariant
            // validation (profiled as the dominant Debug::fmt/alloc churn on
            // sally/oral_messages). #9072
            canonical_args.sort_by_cached_key(|arg| format!("{arg:?}"));
            ChcExpr::Op(
                *op,
                canonical_args
                    .into_iter()
                    .map(std::sync::Arc::new)
                    .collect(),
            )
        }
        ChcExpr::Op(op, args) => ChcExpr::Op(
            *op,
            args.iter()
                .map(|arg| std::sync::Arc::new(canonical_validation_expr(arg)))
                .collect(),
        ),
        ChcExpr::PredicateApp(name, pred, args) => ChcExpr::PredicateApp(
            name.clone(),
            *pred,
            args.iter()
                .map(|arg| std::sync::Arc::new(canonical_validation_expr(arg)))
                .collect(),
        ),
        ChcExpr::FuncApp(name, sort, args) => ChcExpr::FuncApp(
            name.clone(),
            sort.clone(),
            args.iter()
                .map(|arg| std::sync::Arc::new(canonical_validation_expr(arg)))
                .collect(),
        ),
        ChcExpr::ConstArray(sort, value) => ChcExpr::ConstArray(
            sort.clone(),
            std::sync::Arc::new(canonical_validation_expr(value)),
        ),
        other => other.clone(),
    }
}

fn triangular_accumulator_query_is_syntactically_unsat(check: &ChcExpr) -> bool {
    let conjuncts = check.conjuncts();
    let identities: Vec<(ChcVar, ChcVar)> = conjuncts
        .iter()
        .filter_map(|expr| triangular_accumulator_identity(expr))
        .collect();
    if identities.is_empty() {
        return false;
    }

    conjuncts
        .iter()
        .filter_map(|expr| sum_gt_square_query(expr))
        .any(|(sum_var, bound_var)| {
            identities.iter().any(|(identity_sum, counter_var)| {
                identity_sum == &sum_var
                    && has_nonnegative_bound(&conjuncts, counter_var)
                    && has_nonnegative_bound(&conjuncts, &bound_var)
                    && has_le_relation(&conjuncts, counter_var, &bound_var)
            })
        })
}

fn triangular_accumulator_identity(expr: &ChcExpr) -> Option<(ChcVar, ChcVar)> {
    let simplified = expr.simplify_constants();
    let ChcExpr::Op(ChcOp::Eq, args) = &simplified else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    triangular_accumulator_identity_sides(args[0].as_ref(), args[1].as_ref())
        .or_else(|| triangular_accumulator_identity_sides(args[1].as_ref(), args[0].as_ref()))
}

fn triangular_accumulator_identity_sides(lhs: &ChcExpr, rhs: &ChcExpr) -> Option<(ChcVar, ChcVar)> {
    let sum_var = twice_int_var(lhs)?;
    let counter_var = triangular_counter_product_var(rhs)?;
    (sum_var.sort == ChcSort::Int && counter_var.sort == ChcSort::Int)
        .then_some((sum_var, counter_var))
}

fn sum_gt_square_query(expr: &ChcExpr) -> Option<(ChcVar, ChcVar)> {
    let ChcExpr::Op(op @ (ChcOp::Gt | ChcOp::Lt), args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    match op {
        ChcOp::Gt => sum_gt_square_sides(args[0].as_ref(), args[1].as_ref()),
        ChcOp::Lt => sum_gt_square_sides(args[1].as_ref(), args[0].as_ref()),
        _ => None,
    }
}

fn sum_gt_square_sides(lhs: &ChcExpr, rhs: &ChcExpr) -> Option<(ChcVar, ChcVar)> {
    let sum_var = plain_int_var(lhs)?;
    let bound_var = square_int_var(rhs)?;
    Some((sum_var, bound_var))
}

fn has_nonnegative_bound(conjuncts: &[&ChcExpr], var: &ChcVar) -> bool {
    conjuncts
        .iter()
        .any(|expr| matches_lower_bound(expr, var).is_some_and(|lower| lower >= 0))
}

fn has_le_relation(conjuncts: &[&ChcExpr], lhs_var: &ChcVar, rhs_var: &ChcVar) -> bool {
    conjuncts.iter().any(|expr| match expr {
        ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
            same_var(args[0].as_ref(), lhs_var) && same_var(args[1].as_ref(), rhs_var)
        }
        ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
            same_var(args[0].as_ref(), rhs_var) && same_var(args[1].as_ref(), lhs_var)
        }
        _ => false,
    })
}

fn matches_lower_bound(expr: &ChcExpr, var: &ChcVar) -> Option<i128> {
    match expr {
        ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 && same_var(args[1].as_ref(), var) => {
            int_literal(args[0].as_ref())
        }
        ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 && same_var(args[0].as_ref(), var) => {
            int_literal(args[1].as_ref())
        }
        ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 && same_var(args[1].as_ref(), var) => {
            int_literal(args[0].as_ref()).and_then(|value| value.checked_add(1))
        }
        ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 && same_var(args[0].as_ref(), var) => {
            int_literal(args[1].as_ref()).and_then(|value| value.checked_add(1))
        }
        _ => None,
    }
}

fn twice_int_var(expr: &ChcExpr) -> Option<ChcVar> {
    let ChcExpr::Op(ChcOp::Mul, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    match (args[0].as_ref(), args[1].as_ref()) {
        (ChcExpr::Int(2), ChcExpr::Var(var)) | (ChcExpr::Var(var), ChcExpr::Int(2))
            if var.sort == ChcSort::Int =>
        {
            Some(var.clone())
        }
        _ => None,
    }
}

fn triangular_counter_product_var(expr: &ChcExpr) -> Option<ChcVar> {
    square_minus_same_var(expr).or_else(|| square_plus_same_var(expr))
}

fn square_minus_same_var(expr: &ChcExpr) -> Option<ChcVar> {
    match expr {
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            let square_var = square_int_var(args[0].as_ref())?;
            let minus_var = plain_int_var(args[1].as_ref())?;
            (square_var == minus_var).then_some(square_var)
        }
        ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
            square_plus_negated_same_var(args[0].as_ref(), args[1].as_ref())
                .or_else(|| square_plus_negated_same_var(args[1].as_ref(), args[0].as_ref()))
        }
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            product_counter_minus_one(args[0].as_ref(), args[1].as_ref())
                .or_else(|| product_counter_minus_one(args[1].as_ref(), args[0].as_ref()))
        }
        _ => None,
    }
}

fn square_plus_same_var(expr: &ChcExpr) -> Option<ChcVar> {
    match expr {
        ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
            square_plus_plain_same_var(args[0].as_ref(), args[1].as_ref())
                .or_else(|| square_plus_plain_same_var(args[1].as_ref(), args[0].as_ref()))
        }
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            product_counter_plus_one(args[0].as_ref(), args[1].as_ref())
                .or_else(|| product_counter_plus_one(args[1].as_ref(), args[0].as_ref()))
        }
        _ => None,
    }
}

fn product_counter_minus_one(counter: &ChcExpr, dec: &ChcExpr) -> Option<ChcVar> {
    let counter_var = plain_int_var(counter)?;
    let dec_var = decrement_int_var(dec)?;
    (counter_var == dec_var).then_some(counter_var)
}

fn product_counter_plus_one(counter: &ChcExpr, inc: &ChcExpr) -> Option<ChcVar> {
    let counter_var = plain_int_var(counter)?;
    let inc_var = increment_int_var(inc)?;
    (counter_var == inc_var).then_some(counter_var)
}

fn square_plus_negated_same_var(square: &ChcExpr, negated: &ChcExpr) -> Option<ChcVar> {
    let square_var = square_int_var(square)?;
    let negated_var = negated_int_var(negated)?;
    (square_var == negated_var).then_some(square_var)
}

fn square_plus_plain_same_var(square: &ChcExpr, plain: &ChcExpr) -> Option<ChcVar> {
    let square_var = square_int_var(square)?;
    let plain_var = plain_int_var(plain)?;
    (square_var == plain_var).then_some(square_var)
}

fn decrement_int_var(expr: &ChcExpr) -> Option<ChcVar> {
    match expr {
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            let var = plain_int_var(args[0].as_ref())?;
            (int_literal(args[1].as_ref()) == Some(1)).then_some(var)
        }
        ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
            int_var_plus_minus_one(args[0].as_ref(), args[1].as_ref())
                .or_else(|| int_var_plus_minus_one(args[1].as_ref(), args[0].as_ref()))
        }
        _ => None,
    }
}

fn int_var_plus_minus_one(var_expr: &ChcExpr, minus_one: &ChcExpr) -> Option<ChcVar> {
    let var = plain_int_var(var_expr)?;
    (int_literal(minus_one) == Some(-1)).then_some(var)
}

fn increment_int_var(expr: &ChcExpr) -> Option<ChcVar> {
    match expr {
        ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
            int_var_plus_one(args[0].as_ref(), args[1].as_ref())
                .or_else(|| int_var_plus_one(args[1].as_ref(), args[0].as_ref()))
        }
        _ => None,
    }
}

fn int_var_plus_one(var_expr: &ChcExpr, one: &ChcExpr) -> Option<ChcVar> {
    let var = plain_int_var(var_expr)?;
    (int_literal(one) == Some(1)).then_some(var)
}

fn square_int_var(expr: &ChcExpr) -> Option<ChcVar> {
    let ChcExpr::Op(ChcOp::Mul, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let lhs = plain_int_var(args[0].as_ref())?;
    let rhs = plain_int_var(args[1].as_ref())?;
    (lhs == rhs).then_some(lhs)
}

fn negated_int_var(expr: &ChcExpr) -> Option<ChcVar> {
    match expr {
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => plain_int_var(args[0].as_ref()),
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Int(-1), ChcExpr::Var(var)) | (ChcExpr::Var(var), ChcExpr::Int(-1))
                    if var.sort == ChcSort::Int =>
                {
                    Some(var.clone())
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn plain_int_var(expr: &ChcExpr) -> Option<ChcVar> {
    match expr {
        ChcExpr::Var(var) if var.sort == ChcSort::Int => Some(var.clone()),
        _ => None,
    }
}

fn same_var(expr: &ChcExpr, var: &ChcVar) -> bool {
    matches!(expr, ChcExpr::Var(found) if found == var)
}

fn int_literal(expr: &ChcExpr) -> Option<i128> {
    match expr {
        ChcExpr::Int(value) => Some(*value),
        _ => None,
    }
}

#[cfg(test)]
mod validation_syntax_tests {
    use super::*;
    use std::sync::Arc;

    fn arc(expr: ChcExpr) -> Arc<ChcExpr> {
        Arc::new(expr)
    }

    fn pow2_63_expr() -> ChcExpr {
        ChcExpr::Op(
            ChcOp::Add,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Mul,
                    vec![
                        arc(ChcExpr::Int(9_223_372_036)),
                        arc(ChcExpr::Int(1_000_000_000)),
                    ],
                )),
                arc(ChcExpr::Int(854_775_808)),
            ],
        )
    }

    fn pow2_64_expr() -> ChcExpr {
        ChcExpr::Op(
            ChcOp::Add,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Mul,
                    vec![
                        arc(ChcExpr::Int(18_446_744_073)),
                        arc(ChcExpr::Int(1_000_000_000)),
                    ],
                )),
                arc(ChcExpr::Int(709_551_616)),
            ],
        )
    }

    fn pow2_63_product_expr() -> ChcExpr {
        ChcExpr::Op(
            ChcOp::Mul,
            vec![
                arc(ChcExpr::Int(4_294_967_296)),
                arc(ChcExpr::Int(2_147_483_648)),
            ],
        )
    }

    fn pow2_64_product_expr() -> ChcExpr {
        ChcExpr::Op(
            ChcOp::Mul,
            vec![
                arc(ChcExpr::Int(4_294_967_296)),
                arc(ChcExpr::Int(4_294_967_296)),
            ],
        )
    }

    fn pow2_64_model_checker_consumer_split_expr() -> ChcExpr {
        ChcExpr::Op(
            ChcOp::Add,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Mul,
                    vec![
                        arc(ChcExpr::Op(
                            ChcOp::Add,
                            vec![
                                arc(ChcExpr::Op(
                                    ChcOp::Mul,
                                    vec![arc(ChcExpr::Int(18)), arc(ChcExpr::Int(1_000_000_000))],
                                )),
                                arc(ChcExpr::Int(446_744_073)),
                            ],
                        )),
                        arc(ChcExpr::Int(1_000_000_000)),
                    ],
                )),
                arc(ChcExpr::Int(709_551_616)),
            ],
        )
    }

    fn signed_int2bv64_norm(expr: ChcExpr) -> ChcExpr {
        let int2bv = ChcExpr::Op(ChcOp::Int2Bv(64), vec![arc(expr)]);
        signed_bv64_norm(int2bv)
    }

    fn signed_bv64_norm(bitvec: ChcExpr) -> ChcExpr {
        let unsigned = ChcExpr::Op(ChcOp::Bv2Nat, vec![arc(bitvec.clone())]);
        let sign_bit = ChcExpr::Op(ChcOp::BvExtract(63, 63), vec![arc(bitvec.clone())]);
        ChcExpr::Op(
            ChcOp::Ite,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Eq,
                    vec![arc(sign_bit), arc(ChcExpr::BitVec(1, 1))],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Sub,
                    vec![arc(unsigned.clone()), arc(pow2_64_expr())],
                )),
                arc(unsigned),
            ],
        )
    }

    fn bool_bv64_ite(var: ChcVar) -> ChcExpr {
        bool_bv64_ite_expr(ChcExpr::var(var))
    }

    fn bool_bv64_ite_expr(condition: ChcExpr) -> ChcExpr {
        ChcExpr::Op(
            ChcOp::Ite,
            vec![
                arc(condition),
                arc(ChcExpr::BitVec(1, 64)),
                arc(ChcExpr::BitVec(0, 64)),
            ],
        )
    }

    fn signed_mod64_norm(expr: ChcExpr) -> ChcExpr {
        signed_mod64_norm_with_constants(expr, pow2_64_expr(), pow2_63_expr(), pow2_64_expr())
    }

    fn signed_mod64_norm_product_modulus(expr: ChcExpr) -> ChcExpr {
        signed_mod64_norm_with_constants(
            expr,
            pow2_64_product_expr(),
            pow2_63_product_expr(),
            pow2_64_expr(),
        )
    }

    fn signed_mod64_norm_with_constants(
        expr: ChcExpr,
        modulus: ChcExpr,
        half_modulus: ChcExpr,
        subtract_modulus: ChcExpr,
    ) -> ChcExpr {
        let unsigned = ChcExpr::Op(ChcOp::Mod, vec![arc(expr), arc(modulus)]);
        ChcExpr::Op(
            ChcOp::Ite,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Eq,
                    vec![
                        arc(ChcExpr::Op(
                            ChcOp::Div,
                            vec![arc(unsigned.clone()), arc(half_modulus)],
                        )),
                        arc(ChcExpr::Int(1)),
                    ],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Sub,
                    vec![arc(unsigned.clone()), arc(subtract_modulus)],
                )),
                arc(unsigned),
            ],
        )
    }

    fn mod_eq(var: &ChcVar, modulus: i128, residue: i128) -> ChcExpr {
        mod_expr_eq(ChcExpr::var(var.clone()), modulus, residue)
    }

    fn mod_expr_eq(expr: ChcExpr, modulus: i128, residue: i128) -> ChcExpr {
        ChcExpr::Op(
            ChcOp::Eq,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Mod,
                    vec![arc(expr), arc(ChcExpr::Int(modulus))],
                )),
                arc(ChcExpr::Int(residue)),
            ],
        )
    }

    #[test]
    fn affine_residue_conflict_is_syntactically_unsat() {
        let x = ChcVar::new("x", ChcSort::Int);
        let y = ChcVar::new("y", ChcSort::Int);
        let impossible = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(mod_eq(&x, 2, 0)),
                arc(mod_eq(&y, 2, 0)),
                arc(ChcExpr::Op(
                    ChcOp::Eq,
                    vec![
                        arc(ChcExpr::var(x)),
                        arc(ChcExpr::Op(
                            ChcOp::Add,
                            vec![arc(ChcExpr::var(y)), arc(ChcExpr::Int(1))],
                        )),
                    ],
                )),
            ],
        );

        assert!(
            validation_formula_proves_unsat(&impossible),
            "x = y + 1 cannot preserve the same parity residue"
        );
    }

    #[test]
    fn linear_mod_residue_is_preserved_through_constant_delta_aliases_9691() {
        let a = ChcVar::new("A", ChcSort::Int);
        let b = ChcVar::new("B", ChcSort::Int);
        let c = ChcVar::new("C", ChcSort::Int);
        let d = ChcVar::new("D", ChcSort::Int);
        let e = ChcVar::new("E", ChcSort::Int);
        let f = ChcVar::new("F", ChcSort::Int);

        let parity = mod_expr_eq(
            ChcExpr::sub(ChcExpr::var(b.clone()), ChcExpr::var(a.clone())),
            2,
            0,
        );
        let mod4 = mod_expr_eq(
            ChcExpr::add(
                ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(b.clone())),
                ChcExpr::var(c.clone()),
            ),
            4,
            0,
        );
        let body = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(parity),
                arc(mod4),
                arc(ChcExpr::eq(
                    ChcExpr::var(d.clone()),
                    ChcExpr::sub(ChcExpr::var(a), ChcExpr::int(1)),
                )),
                arc(ChcExpr::eq(
                    ChcExpr::var(e.clone()),
                    ChcExpr::sub(ChcExpr::var(b), ChcExpr::int(3)),
                )),
                arc(ChcExpr::eq(
                    ChcExpr::var(f.clone()),
                    ChcExpr::add(ChcExpr::var(c), ChcExpr::int(2)),
                )),
            ],
        );
        let head = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(mod_expr_eq(
                    ChcExpr::sub(ChcExpr::var(e.clone()), ChcExpr::var(d.clone())),
                    2,
                    0,
                )),
                arc(mod_expr_eq(
                    ChcExpr::add(
                        ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(e)),
                        ChcExpr::var(f),
                    ),
                    4,
                    0,
                )),
            ],
        );

        assert!(
            validation_body_syntactically_implies_head(&body, &head, false),
            "constant-delta aliases should preserve compatible linear modular summaries"
        );
    }

    #[test]
    fn linear_equality_implies_matching_mod_residue_9691() {
        let a = ChcVar::new("A", ChcSort::Int);
        let b = ChcVar::new("B", ChcSort::Int);
        let body = ChcExpr::eq(
            ChcExpr::sub(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
            ChcExpr::int(0),
        );
        let head = mod_expr_eq(ChcExpr::sub(ChcExpr::var(a), ChcExpr::var(b)), 2, 0);

        assert!(
            validation_body_syntactically_implies_head(&body, &head, false),
            "an exact linear equality should imply the corresponding modular residue"
        );
    }

    #[test]
    fn positive_factor_bounds_imply_positive_product_bound_1753() {
        let i = ChcVar::new("i", ChcSort::Int);
        let result = ChcVar::new("result", ChcSort::Int);
        let body = ChcExpr::and(
            ChcExpr::ge(ChcExpr::var(i.clone()), ChcExpr::int(1)),
            ChcExpr::ge(ChcExpr::var(result.clone()), ChcExpr::int(1)),
        );
        let head = ChcExpr::ge(
            ChcExpr::mul(ChcExpr::var(result), ChcExpr::var(i)),
            ChcExpr::int(1),
        );

        assert!(
            validation_body_syntactically_implies_head(&body, &head, false),
            "factor lower bounds should discharge product positivity without NIA SMT"
        );
    }

    #[test]
    fn linear_equality_is_preserved_through_constant_delta_aliases_9691() {
        let a = ChcVar::new("A", ChcSort::Int);
        let c = ChcVar::new("C", ChcSort::Int);
        let d = ChcVar::new("D", ChcSort::Int);
        let f = ChcVar::new("F", ChcSort::Int);

        let body = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::eq(
                    ChcExpr::add(
                        ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(a.clone())),
                        ChcExpr::var(c.clone()),
                    ),
                    ChcExpr::int(0),
                )),
                arc(ChcExpr::eq(
                    ChcExpr::var(d.clone()),
                    ChcExpr::sub(ChcExpr::var(a), ChcExpr::int(1)),
                )),
                arc(ChcExpr::eq(
                    ChcExpr::var(f.clone()),
                    ChcExpr::add(ChcExpr::var(c), ChcExpr::int(2)),
                )),
            ],
        );
        let head = ChcExpr::eq(
            ChcExpr::add(
                ChcExpr::mul(ChcExpr::int(-2), ChcExpr::var(d)),
                ChcExpr::neg(ChcExpr::var(f)),
            ),
            ChcExpr::int(0),
        );

        assert!(
            validation_body_syntactically_implies_head(&body, &head, false),
            "linear equalities should validate through constant-delta aliases even when sign-flipped"
        );
    }

    #[test]
    fn linear_inequality_is_preserved_through_constant_delta_aliases_9691() {
        let a = ChcVar::new("A", ChcSort::Int);
        let b = ChcVar::new("B", ChcSort::Int);
        let d = ChcVar::new("D", ChcSort::Int);
        let e = ChcVar::new("E", ChcSort::Int);

        let body = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::le(
                    ChcExpr::sub(
                        ChcExpr::var(b.clone()),
                        ChcExpr::mul(ChcExpr::int(3), ChcExpr::var(a.clone())),
                    ),
                    ChcExpr::int(0),
                )),
                arc(ChcExpr::eq(
                    ChcExpr::var(d.clone()),
                    ChcExpr::sub(ChcExpr::var(a), ChcExpr::int(1)),
                )),
                arc(ChcExpr::eq(
                    ChcExpr::var(e.clone()),
                    ChcExpr::sub(ChcExpr::var(b), ChcExpr::int(3)),
                )),
            ],
        );
        let head = ChcExpr::le(
            ChcExpr::sub(
                ChcExpr::var(e),
                ChcExpr::mul(ChcExpr::int(3), ChcExpr::var(d)),
            ),
            ChcExpr::int(0),
        );

        assert!(
            validation_body_syntactically_implies_head(&body, &head, false),
            "linear inequalities should validate through same-direction constant-delta aliases"
        );
    }

    #[test]
    fn linear_inequality_uses_body_equalities_for_exact_combination_9691() {
        let a = ChcVar::new("A", ChcSort::Int);
        let b = ChcVar::new("B", ChcSort::Int);
        let c = ChcVar::new("C", ChcSort::Int);

        let body = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::eq(
                    ChcExpr::sub(ChcExpr::var(b.clone()), ChcExpr::var(a.clone())),
                    ChcExpr::int(0),
                )),
                arc(ChcExpr::eq(
                    ChcExpr::add(
                        ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(a)),
                        ChcExpr::var(c.clone()),
                    ),
                    ChcExpr::int(0),
                )),
                arc(ChcExpr::le(ChcExpr::var(c.clone()), ChcExpr::int(0))),
            ],
        );
        let head = ChcExpr::le(
            ChcExpr::add(
                ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(b)),
                ChcExpr::mul(ChcExpr::int(3), ChcExpr::var(c)),
            ),
            ChcExpr::int(0),
        );

        assert!(
            validation_body_syntactically_implies_head(&body, &head, false),
            "linear inequalities should combine body equalities with a same-direction inequality"
        );
    }

    #[test]
    fn compatible_nested_residues_are_not_a_contradiction() {
        let x = ChcVar::new("x", ChcSort::Int);
        let compatible = ChcExpr::Op(
            ChcOp::And,
            vec![arc(mod_eq(&x, 2, 0)), arc(mod_eq(&x, 4, 0))],
        );

        assert!(
            !validation_formula_proves_unsat(&compatible),
            "compatible residues with different moduli remain satisfiable"
        );
    }

    #[test]
    fn signed_int2bv64_norm_proves_upper_bound_above_i64_max() {
        let x = ChcVar::new("x", ChcSort::Int);
        let signed = signed_int2bv64_norm(ChcExpr::var(x));
        let impossible = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Ge,
                    vec![arc(signed.clone()), arc(ChcExpr::Int(i128::from(i64::MIN)))],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Not,
                    vec![arc(ChcExpr::Op(
                        ChcOp::Lt,
                        vec![arc(signed), arc(pow2_63_expr())],
                    ))],
                )),
            ],
        );
        assert!(
            validation_formula_proves_unsat(&impossible),
            "signed bv-to-int normalization should validate its i64 upper range"
        );
    }

    #[test]
    fn bool_encoded_signed_mod64_dual_exclusion_is_unsat() {
        let b = ChcVar::new("b", ChcSort::Bool);
        let bool_as_int = ChcExpr::Op(
            ChcOp::Ite,
            vec![
                arc(ChcExpr::var(b)),
                arc(ChcExpr::Int(1)),
                arc(ChcExpr::Int(0)),
            ],
        );
        let signed = signed_mod64_norm(bool_as_int);
        let impossible = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Not,
                    vec![arc(ChcExpr::Op(
                        ChcOp::Eq,
                        vec![arc(signed.clone()), arc(ChcExpr::Int(0))],
                    ))],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Not,
                    vec![arc(ChcExpr::Op(
                        ChcOp::Eq,
                        vec![arc(signed), arc(ChcExpr::Int(1))],
                    ))],
                )),
            ],
        );

        assert!(
            validation_formula_proves_unsat(&impossible),
            "bool-as-int terms cannot be distinct from both 0 and 1"
        );
    }

    #[test]
    fn bool_encoded_signed_bv_ite_dual_exclusion_is_unsat() {
        let b = ChcVar::new("b", ChcSort::Bool);
        let signed = signed_bv64_norm(bool_bv64_ite(b));
        let impossible = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Not,
                    vec![arc(ChcExpr::Op(
                        ChcOp::Eq,
                        vec![arc(signed.clone()), arc(ChcExpr::Int(0))],
                    ))],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Not,
                    vec![arc(ChcExpr::Op(
                        ChcOp::Eq,
                        vec![arc(signed), arc(ChcExpr::Int(1))],
                    ))],
                )),
            ],
        );

        assert!(
            validation_formula_proves_unsat(&impossible),
            "bool-as-bv signed terms cannot be distinct from both 0 and 1"
        );
    }

    #[test]
    fn bool_encoded_signed_bv_ite_conflicting_equalities_are_unsat() {
        let b = ChcVar::new("b", ChcSort::Bool);
        let signed = signed_bv64_norm(bool_bv64_ite(b));
        let impossible = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Eq,
                    vec![arc(signed.clone()), arc(ChcExpr::Int(0))],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Eq,
                    vec![arc(signed), arc(ChcExpr::Int(1))],
                )),
            ],
        );

        assert!(
            validation_formula_proves_unsat(&impossible),
            "bool-as-bv signed terms cannot be equal to both 0 and 1"
        );
    }

    #[test]
    fn unsat_body_syntactically_implies_false_head() {
        let b = ChcVar::new("b", ChcSort::Bool);
        let signed = signed_bv64_norm(bool_bv64_ite(b));
        let body = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Not,
                    vec![arc(ChcExpr::Op(
                        ChcOp::Eq,
                        vec![arc(signed.clone()), arc(ChcExpr::Int(0))],
                    ))],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Not,
                    vec![arc(ChcExpr::Op(
                        ChcOp::Eq,
                        vec![arc(signed), arc(ChcExpr::Int(1))],
                    ))],
                )),
            ],
        );

        assert!(
            validation_body_syntactically_implies_head(&body, &ChcExpr::Bool(false), false),
            "syntactically unreachable bodies should validate false-head CHC clauses"
        );
    }

    #[test]
    fn conflicting_bool_encoded_body_syntactically_implies_false_head() {
        let b = ChcVar::new("b", ChcSort::Bool);
        let signed = signed_bv64_norm(bool_bv64_ite(b));
        let body = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Eq,
                    vec![arc(signed.clone()), arc(ChcExpr::Int(0))],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Eq,
                    vec![arc(signed), arc(ChcExpr::Int(1))],
                )),
            ],
        );

        assert!(
            validation_body_syntactically_implies_head(&body, &ChcExpr::Bool(false), false),
            "conflicting bool-encoded equalities should validate false-head CHC clauses"
        );
    }

    #[test]
    fn bool_encoded_signed_mod64_product_constants_dual_exclusion_is_unsat() {
        let b = ChcVar::new("b", ChcSort::Bool);
        let bool_as_int = ChcExpr::Op(
            ChcOp::Ite,
            vec![
                arc(ChcExpr::var(b)),
                arc(ChcExpr::Int(1)),
                arc(ChcExpr::Int(0)),
            ],
        );
        let signed = signed_mod64_norm_product_modulus(bool_as_int);
        let impossible = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Not,
                    vec![arc(ChcExpr::Op(
                        ChcOp::Eq,
                        vec![arc(signed.clone()), arc(ChcExpr::Int(0))],
                    ))],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Not,
                    vec![arc(ChcExpr::Op(
                        ChcOp::Eq,
                        vec![arc(signed), arc(ChcExpr::Int(1))],
                    ))],
                )),
            ],
        );

        assert!(
            validation_formula_proves_unsat(&impossible),
            "product-spelled 2^64 bool-as-int terms cannot be distinct from both 0 and 1"
        );
    }

    #[test]
    fn bool_encoded_signed_mod64_model_checker_consumer_split_dual_exclusion_is_unsat() {
        let b = ChcVar::new("b", ChcSort::Bool);
        let bool_as_int = ChcExpr::Op(
            ChcOp::Ite,
            vec![
                arc(ChcExpr::var(b)),
                arc(ChcExpr::Int(1)),
                arc(ChcExpr::Int(0)),
            ],
        );
        let signed = signed_mod64_norm_with_constants(
            bool_as_int,
            pow2_64_product_expr(),
            pow2_63_product_expr(),
            pow2_64_model_checker_consumer_split_expr(),
        );
        let impossible = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Not,
                    vec![arc(ChcExpr::Op(
                        ChcOp::Eq,
                        vec![arc(signed.clone()), arc(ChcExpr::Int(0))],
                    ))],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Not,
                    vec![arc(ChcExpr::Op(
                        ChcOp::Eq,
                        vec![arc(signed), arc(ChcExpr::Int(1))],
                    ))],
                )),
            ],
        );

        assert!(
            validation_formula_proves_unsat(&impossible),
            "model-checker-consumer-spelled 2^64 bool-as-int terms cannot be distinct from both 0 and 1"
        );
    }

    #[test]
    fn repeated_condition_nested_ite_tautology_is_unsat_when_negated() {
        let c = ChcVar::new("c", ChcSort::Bool);
        let x = ChcVar::new("x", ChcSort::Bool);
        let y = ChcVar::new("y", ChcSort::Bool);
        let condition = ChcExpr::var(c);
        let tautology = ChcExpr::Op(
            ChcOp::Ite,
            vec![
                arc(condition.clone()),
                arc(ChcExpr::Op(
                    ChcOp::Ite,
                    vec![
                        arc(condition.clone()),
                        arc(ChcExpr::Bool(true)),
                        arc(ChcExpr::var(x)),
                    ],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Ite,
                    vec![
                        arc(condition),
                        arc(ChcExpr::var(y)),
                        arc(ChcExpr::Bool(true)),
                    ],
                )),
            ],
        );
        let impossible = ChcExpr::Op(ChcOp::Not, vec![arc(tautology)]);

        assert!(
            validation_formula_proves_unsat(&impossible),
            "ite(c, ite(c, true, _), ite(c, _, true)) is tautologically true"
        );
    }

    #[test]
    fn tautological_nested_ite_head_is_syntactically_implied() {
        let c = ChcVar::new("c", ChcSort::Bool);
        let x = ChcVar::new("x", ChcSort::Bool);
        let y = ChcVar::new("y", ChcSort::Bool);
        let condition = ChcExpr::var(c);
        let tautology = ChcExpr::Op(
            ChcOp::Ite,
            vec![
                arc(condition.clone()),
                arc(ChcExpr::Op(
                    ChcOp::Ite,
                    vec![
                        arc(condition.clone()),
                        arc(ChcExpr::Bool(true)),
                        arc(ChcExpr::var(x)),
                    ],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Ite,
                    vec![
                        arc(condition),
                        arc(ChcExpr::var(y)),
                        arc(ChcExpr::Bool(true)),
                    ],
                )),
            ],
        );

        assert!(
            validation_body_syntactically_implies_head(&ChcExpr::Bool(true), &tautology, false),
            "tautological nested ITE head conjuncts should not fall through to SMT validation"
        );
    }

    #[test]
    fn alias_equalities_make_head_bounds_syntactically_implied() {
        let x = ChcVar::new("x", ChcSort::Int);
        let out = ChcVar::new("x__out", ChcSort::Int);
        let out2 = ChcVar::new("x__out2", ChcSort::Int);
        let upper = pow2_64_model_checker_consumer_split_expr();
        let body = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Ge,
                    vec![arc(ChcExpr::var(x.clone())), arc(ChcExpr::Int(0))],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Lt,
                    vec![arc(ChcExpr::var(x.clone())), arc(upper.clone())],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Eq,
                    vec![arc(ChcExpr::var(out.clone())), arc(ChcExpr::var(x.clone()))],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Eq,
                    vec![arc(ChcExpr::var(out2.clone())), arc(ChcExpr::var(out))],
                )),
            ],
        );
        let head = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Ge,
                    vec![arc(ChcExpr::var(out2.clone())), arc(ChcExpr::Int(0))],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Lt,
                    vec![arc(ChcExpr::var(out2)), arc(upper)],
                )),
            ],
        );

        assert!(
            validation_body_syntactically_implies_head(&body, &head, false),
            "alias-only transfer equalities should carry interval head conjuncts"
        );
    }

    #[test]
    fn body_interval_contradicts_negated_head_bound() {
        let x = ChcVar::new("x", ChcSort::Int);
        let body = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Ge,
                    vec![arc(ChcExpr::var(x.clone())), arc(ChcExpr::Int(0))],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Lt,
                    vec![arc(ChcExpr::var(x.clone())), arc(ChcExpr::Int(10))],
                )),
            ],
        );
        let head = ChcExpr::Op(ChcOp::Le, vec![arc(ChcExpr::var(x)), arc(ChcExpr::Int(9))]);

        assert!(
            validation_body_syntactically_implies_head(&body, &head, false),
            "body interval facts should discharge implied head bounds without SMT"
        );
    }

    #[test]
    fn body_implied_disjunct_makes_or_head_implied() {
        let x = ChcVar::new("x", ChcSort::Int);
        let y = ChcVar::new("y", ChcSort::Int);
        let z = ChcVar::new("z", ChcSort::Int);
        let body_x = ChcExpr::Op(
            ChcOp::Eq,
            vec![arc(ChcExpr::var(x.clone())), arc(ChcExpr::Int(0))],
        );
        let body_y = ChcExpr::Op(
            ChcOp::Eq,
            vec![arc(ChcExpr::var(y.clone())), arc(ChcExpr::Int(1))],
        );
        let body = ChcExpr::Op(ChcOp::And, vec![arc(body_x.clone()), arc(body_y.clone())]);
        let implied_disjunct = ChcExpr::Op(ChcOp::And, vec![arc(body_x), arc(body_y)]);
        let unrelated_disjunct =
            ChcExpr::Op(ChcOp::Eq, vec![arc(ChcExpr::var(z)), arc(ChcExpr::Int(2))]);
        let head = ChcExpr::Op(
            ChcOp::Or,
            vec![arc(implied_disjunct), arc(unrelated_disjunct)],
        );

        assert!(
            validation_body_syntactically_implies_head(&body, &head, false),
            "a body-implied disjunct should discharge an or-shaped head invariant"
        );
    }

    #[test]
    fn bool_bv_sign_guard_false_selects_unsigned_branch() {
        let c = ChcVar::new("c", ChcSort::Bool);
        let x = ChcVar::new("x", ChcSort::Int);
        let bitvec = bool_bv64_ite(c);
        let unsigned = ChcExpr::Op(ChcOp::Bv2Nat, vec![arc(bitvec.clone())]);
        let sign_guard = ChcExpr::Op(
            ChcOp::Eq,
            vec![
                arc(ChcExpr::Op(ChcOp::BvExtract(63, 63), vec![arc(bitvec)])),
                arc(ChcExpr::BitVec(1, 1)),
            ],
        );
        let body = ChcExpr::Op(
            ChcOp::Eq,
            vec![arc(ChcExpr::var(x.clone())), arc(unsigned.clone())],
        );
        let head = ChcExpr::Op(
            ChcOp::Ite,
            vec![
                arc(sign_guard),
                arc(ChcExpr::Op(
                    ChcOp::Eq,
                    vec![
                        arc(ChcExpr::var(x.clone())),
                        arc(ChcExpr::Op(
                            ChcOp::Sub,
                            vec![arc(unsigned.clone()), arc(pow2_64_expr())],
                        )),
                    ],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Eq,
                    vec![arc(ChcExpr::var(x)), arc(unsigned)],
                )),
            ],
        );

        assert!(
            validation_body_syntactically_implies_head(&body, &head, false),
            "MSB guard for bool-as-bv64 is always false, so the unsigned branch is selected"
        );
    }

    #[test]
    fn bool_expr_alias_normalizes_signed_bv_head_argument() {
        let b = ChcVar::new("b", ChcSort::Bool);
        let i = ChcVar::new("i", ChcSort::Int);
        let limit = ChcVar::new("limit", ChcSort::Int);
        let x = ChcVar::new("x", ChcSort::Int);
        let condition = ChcExpr::Op(
            ChcOp::Lt,
            vec![arc(ChcExpr::var(i)), arc(ChcExpr::var(limit))],
        );
        let body = ChcExpr::Op(
            ChcOp::And,
            vec![
                arc(ChcExpr::Op(
                    ChcOp::Eq,
                    vec![arc(ChcExpr::var(b.clone())), arc(condition.clone())],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Eq,
                    vec![
                        arc(ChcExpr::var(x.clone())),
                        arc(signed_bv64_norm(bool_bv64_ite(b))),
                    ],
                )),
            ],
        );
        let head = ChcExpr::Op(
            ChcOp::Eq,
            vec![
                arc(ChcExpr::var(x)),
                arc(ChcExpr::Op(
                    ChcOp::Bv2Nat,
                    vec![arc(bool_bv64_ite_expr(condition))],
                )),
            ],
        );

        assert!(
            validation_body_syntactically_implies_head(&body, &head, false),
            "Bool variable aliases should normalize model-checker-consumer bool-as-bv64 signed arguments"
        );
    }

    #[test]
    fn commutative_constant_bounds_are_syntactically_implied() {
        let x = ChcVar::new("x", ChcSort::Int);
        let upper_body = ChcExpr::Op(
            ChcOp::Add,
            vec![
                arc(ChcExpr::Int(9_223_372_036_000_000_000)),
                arc(ChcExpr::Int(854_775_808)),
            ],
        );
        let upper_head = ChcExpr::Op(
            ChcOp::Add,
            vec![
                arc(ChcExpr::Int(854_775_808)),
                arc(ChcExpr::Int(9_223_372_036_000_000_000)),
            ],
        );
        let body = ChcExpr::Op(
            ChcOp::Lt,
            vec![arc(ChcExpr::var(x.clone())), arc(upper_body)],
        );
        let head = ChcExpr::Op(ChcOp::Lt, vec![arc(ChcExpr::var(x)), arc(upper_head)]);

        assert!(
            validation_body_syntactically_implies_head(&body, &head, false),
            "large split constants should canonicalize across commutative spellings"
        );
    }

    #[test]
    fn repeated_sign_bit_condition_nested_ite_tautology_is_unsat_when_negated() {
        let x = ChcVar::new("x", ChcSort::Int);
        let int2bv = ChcExpr::Op(ChcOp::Int2Bv(64), vec![arc(ChcExpr::var(x))]);
        let unsigned = ChcExpr::Op(ChcOp::Bv2Nat, vec![arc(int2bv.clone())]);
        let condition = ChcExpr::Op(
            ChcOp::Eq,
            vec![
                arc(ChcExpr::Op(ChcOp::BvExtract(63, 63), vec![arc(int2bv)])),
                arc(ChcExpr::BitVec(1, 1)),
            ],
        );
        let wrapped = ChcExpr::Op(ChcOp::Sub, vec![arc(unsigned.clone()), arc(pow2_64_expr())]);
        let tautology = ChcExpr::Op(
            ChcOp::Ite,
            vec![
                arc(condition.clone()),
                arc(ChcExpr::Op(
                    ChcOp::Ite,
                    vec![
                        arc(condition.clone()),
                        arc(ChcExpr::Bool(true)),
                        arc(ChcExpr::Op(
                            ChcOp::Eq,
                            vec![arc(unsigned.clone()), arc(wrapped.clone())],
                        )),
                    ],
                )),
                arc(ChcExpr::Op(
                    ChcOp::Ite,
                    vec![
                        arc(condition),
                        arc(ChcExpr::Op(ChcOp::Eq, vec![arc(wrapped), arc(unsigned)])),
                        arc(ChcExpr::Bool(true)),
                    ],
                )),
            ],
        );
        let impossible = ChcExpr::Op(ChcOp::Not, vec![arc(tautology)]);

        assert!(
            validation_formula_proves_unsat(&impossible),
            "repeated BV sign-bit condition should reduce to the selected true branches"
        );
    }
}
