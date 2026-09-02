// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV strategy methods for the adaptive portfolio solver.
//!
//! Contains portfolio config builders and the simple loop orchestrator.
//! Companion: `adaptive_bv_dual_lane.rs` has the multi-lane BV solving
//! method (`solve_bv_dual_lane`).

use crate::adaptive_decision_log::DecisionEntry;
use crate::bmc::BmcConfig;
use crate::cegar::CegarConfig;
use crate::classifier::ProblemFeatures;
use crate::engine_config::ChcEngineConfig;
use crate::engine_result::ValidationEvidence;
use crate::imc::ImcConfig;
use crate::kind::{KindConfig, KindResult, KindSolver};
use crate::pdkind::PdkindConfig;
use crate::pdr::{
    Counterexample, CounterexampleStep, InvariantModel, PdrConfig, PdrResult, PdrSolver,
    PredicateInterpretation,
};
use crate::portfolio::{EngineConfig, PortfolioConfig, PortfolioResult};
use crate::tpa::TpaConfig;
use crate::transform::{DtFlattener, TransformationPipeline};
use crate::transition_system::TransitionSystem;
use crate::trl::TrlConfig;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, ClauseHead, SmtResult};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;
use ay_sat::TlaTraceable;
use std::sync::Arc;
use std::time::Duration;

use crate::adaptive::{AdaptivePortfolio, StagedProbeBudgetProfile};

fn try_budgeted_pdr(
    portfolio: &AdaptivePortfolio,
    mut pdr_config: PdrConfig,
    budget: Duration,
) -> Option<(PortfolioResult, ValidationEvidence)> {
    if budget.is_zero() {
        return None;
    }

    pdr_config.solve_timeout = Some(budget);
    portfolio.apply_user_hints(&mut pdr_config);
    let mut solver = PdrSolver::new(portfolio.problem.clone(), pdr_config);
    solver.enable_tla_trace_from_config();
    let result_with_stats = solver.solve_with_stats();
    portfolio.accumulate_stats(&result_with_stats.stats);
    let validated = portfolio.validate_adaptive_result(result_with_stats.result);

    match validated {
        PdrResult::Safe(model) => Some((
            PortfolioResult::Safe(model),
            ValidationEvidence::FullVerification,
        )),
        PdrResult::Unsafe(cex) => Some((
            PortfolioResult::Unsafe(cex),
            ValidationEvidence::FullVerification,
        )),
        PdrResult::Unknown | PdrResult::NotApplicable => None,
    }
}

/// Run PDR on a specific problem (not the portfolio's problem).
/// Used for DT-flattened problems (#8288) where the problem has been
/// transformed before the PDR probe.
///
/// SOUNDNESS CONTRACT (wishlist rank 1c, 2026-07-08): this helper does NOT
/// validate its result — it CANNOT, because validation must run against the
/// ORIGINAL problem in the original vocabulary, after back-translation, which
/// only the caller can do. Every caller MUST, before returning the result:
///   - Safe: re-validate the back-translated model on the original problem
///     (`validate_translated_safe_model_on_original`), else demote to Unknown;
///   - Unsafe: replay the back-translated counterexample on the original
///     problem (`validate_original_counterexample_with_budget`), else demote —
///     and reject outright when `unsafe_backtranslation_complete()` is false.
/// The DT-flatten caller in `solve_bv_dual_lane` is the reference
/// implementation. Returning this result unvalidated would stamp
/// `FullVerification` evidence on an unreplayed verdict — a fail-open.
fn try_budgeted_pdr_on_problem(
    portfolio: &AdaptivePortfolio,
    problem: &crate::ChcProblem,
    mut pdr_config: PdrConfig,
    budget: Duration,
) -> Option<(PortfolioResult, ValidationEvidence)> {
    if budget.is_zero() {
        return None;
    }

    pdr_config.solve_timeout = Some(budget);
    let mut solver = PdrSolver::new(problem.clone(), pdr_config);
    solver.enable_tla_trace_from_config();
    let result_with_stats = solver.solve_with_stats();
    portfolio.accumulate_stats(&result_with_stats.stats);

    match result_with_stats.result {
        PdrResult::Safe(model) => Some((
            PortfolioResult::Safe(model),
            ValidationEvidence::FullVerification,
        )),
        PdrResult::Unsafe(cex) => Some((
            PortfolioResult::Unsafe(cex),
            ValidationEvidence::FullVerification,
        )),
        PdrResult::Unknown | PdrResult::NotApplicable => None,
    }
}

fn unknown_accepted_result() -> (PortfolioResult, ValidationEvidence) {
    (
        PortfolioResult::Unknown,
        ValidationEvidence::FullVerification,
    )
}

#[derive(Clone, Debug)]
struct ListIntAdtView {
    sort: ChcSort,
    nil_ctor: String,
    cons_ctor: String,
    tail_selector: String,
}

fn recursive_list_int_view(sort: &ChcSort) -> Option<ListIntAdtView> {
    let ChcSort::Datatype { name, constructors } = sort else {
        return None;
    };

    let nil_ctor = constructors
        .iter()
        .find(|ctor| ctor.selectors.is_empty())?
        .name
        .clone();
    let cons_ctor = constructors.iter().find(|ctor| ctor.selectors.len() == 2)?;

    let mut head_selector = None;
    let mut tail_selector = None;
    for selector in &cons_ctor.selectors {
        match &selector.sort {
            ChcSort::Int => head_selector = Some(selector.name.clone()),
            ChcSort::Datatype {
                name: child_name, ..
            } if child_name == name => {
                tail_selector = Some(selector.name.clone());
            }
            ChcSort::Uninterpreted(child_name) if child_name == name => {
                tail_selector = Some(selector.name.clone());
            }
            _ => {}
        }
    }

    // Require an Int head selector so this is the standard recursive
    // list-of-Int shape, even though the invariant below avoids selecting the
    // head for easier validation.
    head_selector?;

    Some(ListIntAdtView {
        sort: sort.clone(),
        nil_ctor,
        cons_ctor: cons_ctor.name.clone(),
        tail_selector: tail_selector?,
    })
}

#[derive(Debug, Clone, Copy)]
struct DilligMulProfile {
    has_nontrivial_scalar_coeff_mul: bool,
    all_mul_are_scalar_coeff: bool,
}

impl Default for DilligMulProfile {
    fn default() -> Self {
        Self {
            has_nontrivial_scalar_coeff_mul: false,
            all_mul_are_scalar_coeff: true,
        }
    }
}

impl DilligMulProfile {
    fn scan(expr: &ChcExpr) -> Self {
        let mut profile = Self::default();
        Self::scan_into(expr, &mut profile);
        profile
    }

    fn scan_all<'a>(exprs: impl IntoIterator<Item = &'a ChcExpr>) -> Self {
        let mut profile = Self::default();
        for expr in exprs {
            Self::scan_into(expr, &mut profile);
        }
        profile
    }

    fn scan_into(expr: &ChcExpr, profile: &mut Self) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(op, args) => {
                if *op == ChcOp::Mul {
                    if Self::is_nontrivial_scalar_coeff_mul(args) {
                        profile.has_nontrivial_scalar_coeff_mul = true;
                    } else {
                        profile.all_mul_are_scalar_coeff = false;
                    }
                }
                for arg in args {
                    Self::scan_into(arg, profile);
                }
            }
            ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                for arg in args {
                    Self::scan_into(arg, profile);
                }
            }
            ChcExpr::ConstArray(_, value) => Self::scan_into(value, profile),
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Real(_, _)
            | ChcExpr::Var(_)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {}
        });
    }

    fn is_nontrivial_scalar_coeff_mul(args: &[std::sync::Arc<ChcExpr>]) -> bool {
        if args.len() != 2 {
            return false;
        }
        match (args[0].as_ref(), args[1].as_ref()) {
            (ChcExpr::Int(k), rhs) | (rhs, ChcExpr::Int(k)) => {
                k.unsigned_abs() > 1 && !rhs.vars().is_empty()
            }
            _ => false,
        }
    }
}

fn expr_contains_ite(expr: &ChcExpr) -> bool {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Op(ChcOp::Ite, _) => true,
        ChcExpr::Op(_, args) => args.iter().any(|arg| expr_contains_ite(arg)),
        ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args.iter().any(|arg| expr_contains_ite(arg))
        }
        ChcExpr::ConstArray(_, value) => expr_contains_ite(value),
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Real(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_) => false,
    })
}

#[derive(Debug, Clone)]
struct BvArrayCounterCellInvariantCandidate {
    array_arg_index: usize,
    counter_arg_index: usize,
    key: ChcExpr,
    init_value: u128,
    value_width: u32,
    counter_width: u32,
    counter_bound: ChcExpr,
}

fn bv_binary(op: ChcOp, left: ChcExpr, right: ChcExpr) -> ChcExpr {
    ChcExpr::Op(op, vec![Arc::new(left), Arc::new(right)])
}

fn bv_const(expr: &ChcExpr) -> Option<(u128, u32)> {
    match expr {
        ChcExpr::BitVec(value, width) => Some((*value, *width)),
        _ => None,
    }
}

fn eq_sides(expr: &ChcExpr) -> Option<(&ChcExpr, &ChcExpr)> {
    let ChcExpr::Op(ChcOp::Eq, args) = expr else {
        return None;
    };
    if args.len() == 2 {
        Some((args[0].as_ref(), args[1].as_ref()))
    } else {
        None
    }
}

fn conjunct_refs(expr: &ChcExpr) -> Vec<&ChcExpr> {
    match expr {
        ChcExpr::Bool(true) => Vec::new(),
        ChcExpr::Op(ChcOp::And, args) => args.iter().map(AsRef::as_ref).collect(),
        other => vec![other],
    }
}

fn select_args(expr: &ChcExpr) -> Option<(&ChcExpr, &ChcExpr)> {
    let ChcExpr::Op(ChcOp::Select, args) = expr else {
        return None;
    };
    if args.len() == 2 {
        Some((args[0].as_ref(), args[1].as_ref()))
    } else {
        None
    }
}

fn store_args(expr: &ChcExpr) -> Option<(&ChcExpr, &ChcExpr, &ChcExpr)> {
    let ChcExpr::Op(ChcOp::Store, args) = expr else {
        return None;
    };
    if args.len() == 3 {
        Some((args[0].as_ref(), args[1].as_ref(), args[2].as_ref()))
    } else {
        None
    }
}

fn bv_add_const(expr: &ChcExpr, left: &ChcExpr) -> Option<(u128, u32)> {
    let ChcExpr::Op(ChcOp::BvAdd, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    if args[0].as_ref() == left {
        bv_const(args[1].as_ref())
    } else if args[1].as_ref() == left {
        bv_const(args[0].as_ref())
    } else {
        None
    }
}

fn expr_is_var(expr: &ChcExpr, var: &ChcVar) -> bool {
    matches!(expr, ChcExpr::Var(candidate) if candidate == var)
}

fn is_eq_var_expr(expr: &ChcExpr, var: &ChcVar, rhs: &ChcExpr) -> bool {
    let Some((left, right)) = eq_sides(expr) else {
        return false;
    };
    (expr_is_var(left, var) && right == rhs) || (expr_is_var(right, var) && left == rhs)
}

fn is_eq_var_bv_const(expr: &ChcExpr, var: &ChcVar, value: u128, width: u32) -> bool {
    let Some((left, right)) = eq_sides(expr) else {
        return false;
    };
    let matches_const = |candidate: &ChcExpr| bv_const(candidate) == Some((value, width));
    (expr_is_var(left, var) && matches_const(right))
        || (expr_is_var(right, var) && matches_const(left))
}

fn select_const_eq(expr: &ChcExpr, array_var: &ChcVar) -> Option<(ChcExpr, u128, u32)> {
    let (left, right) = eq_sides(expr)?;
    if let Some((array, key)) = select_args(left) {
        if expr_is_var(array, array_var) {
            let (value, width) = bv_const(right)?;
            return Some((key.clone(), value, width));
        }
    }
    if let Some((array, key)) = select_args(right) {
        if expr_is_var(array, array_var) {
            let (value, width) = bv_const(left)?;
            return Some((key.clone(), value, width));
        }
    }
    None
}

fn is_bvult(expr: &ChcExpr, left: &ChcExpr, right: &ChcExpr) -> bool {
    let ChcExpr::Op(ChcOp::BvULt, args) = expr else {
        return false;
    };
    args.len() == 2 && args[0].as_ref() == left && args[1].as_ref() == right
}

fn bv_array_counter_cell_candidate(
    problem: &crate::ChcProblem,
) -> Option<BvArrayCounterCellInvariantCandidate> {
    if problem.predicates().len() != 1
        || problem.facts().count() != 1
        || problem.transitions().count() != 1
        || problem.queries().count() != 1
    {
        return None;
    }

    let pred = problem.predicates().first()?;
    if pred.arg_sorts.len() != 2 {
        return None;
    }
    let (array_arg_index, counter_arg_index, counter_width) =
        match (&pred.arg_sorts[0], &pred.arg_sorts[1]) {
            (ChcSort::Array(key, value), ChcSort::BitVec(counter_width))
                if matches!((&**key, &**value), (ChcSort::BitVec(_), ChcSort::BitVec(_))) =>
            {
                (0, 1, *counter_width)
            }
            _ => return None,
        };

    let ts = TransitionSystem::from_chc_problem(problem).ok()?;
    let array_var = ts.vars.get(array_arg_index)?;
    let counter_var = ts.vars.get(counter_arg_index)?;
    let next_array_var = ChcVar::new(format!("{}_next", array_var.name), array_var.sort.clone());
    let next_counter_var = ChcVar::new(
        format!("{}_next", counter_var.name),
        counter_var.sort.clone(),
    );
    let array_expr = ChcExpr::var(array_var.clone());
    let counter_expr = ChcExpr::var(counter_var.clone());
    let one = ChcExpr::BitVec(1, counter_width);
    let counter_next_expr = bv_binary(ChcOp::BvAdd, counter_expr.clone(), one);

    let init_conjuncts = conjunct_refs(&ts.init);
    if !init_conjuncts
        .iter()
        .any(|expr| is_eq_var_bv_const(expr, counter_var, 0, counter_width))
    {
        return None;
    }
    let (key, init_value, value_width) = init_conjuncts
        .iter()
        .find_map(|expr| select_const_eq(expr, array_var))?;

    let query_select = ChcExpr::select(array_expr.clone(), key.clone());
    let query_bound = ChcExpr::BitVec(init_value, value_width);
    if !conjunct_refs(&ts.query)
        .iter()
        .any(|expr| is_bvult(expr, &query_select, &query_bound))
    {
        return None;
    }

    let transition_conjuncts = conjunct_refs(&ts.transition);
    let guard_bound = transition_conjuncts.iter().find_map(|expr| {
        let ChcExpr::Op(ChcOp::BvULt, args) = expr else {
            return None;
        };
        if args.len() == 2 && args[0].as_ref() == &counter_expr {
            Some(args[1].as_ref().clone())
        } else {
            None
        }
    })?;

    if !transition_conjuncts
        .iter()
        .any(|expr| is_eq_var_expr(expr, &next_counter_var, &counter_next_expr))
    {
        return None;
    }

    let has_single_counter_store = transition_conjuncts.iter().any(|expr| {
        let Some((left, right)) = eq_sides(expr) else {
            return false;
        };
        let store = if expr_is_var(left, &next_array_var) {
            right
        } else if expr_is_var(right, &next_array_var) {
            left
        } else {
            return false;
        };
        let Some((store_array, store_index, store_value)) = store_args(store) else {
            return false;
        };
        if store_array != &array_expr || store_index != &counter_expr {
            return false;
        }
        let selected = ChcExpr::select(array_expr.clone(), counter_expr.clone());
        bv_add_const(store_value, &selected) == Some((1, value_width))
    });
    if !has_single_counter_store {
        return None;
    }

    Some(BvArrayCounterCellInvariantCandidate {
        array_arg_index,
        counter_arg_index,
        key,
        init_value,
        value_width,
        counter_width,
        counter_bound: guard_bound,
    })
}

fn is_literal_const(expr: &ChcExpr) -> bool {
    matches!(
        expr,
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::BitVec(_, _) | ChcExpr::Real(_, _)
    )
}

/// Collect constant-cell pins `select(canonical, key) = val` implied by an init
/// head argument for a preserved array parameter.
///
/// Two init encodings are handled:
///   - store-in-head: `store(base, key, val)` (possibly nested) with a constant
///     `key` and constant `val` — `select` of that head arg at `key` is `val`;
///   - plain array var pinned by the init body constraint via
///     `select(var, key) = c` (BV) or `select(var, key)` / `not(select var
///     key)` (Bool).
///
/// Soundness never rests on this extraction: the caller validates the resulting
/// invariant against the original clauses before accepting it. A missed or
/// spurious pin just yields a candidate that fails validation (→ fall through).
fn collect_preserved_cell_pins(
    init_arg: &ChcExpr,
    init_constraint: &ChcExpr,
    canonical: &ChcVar,
    out: &mut Vec<ChcExpr>,
) {
    // store-in-head form (innermost store wins for a repeated key).
    let mut cursor = init_arg;
    let mut pinned_keys: Vec<ChcExpr> = Vec::new();
    while let Some((base, key, val)) = store_args(cursor) {
        if is_literal_const(key) && is_literal_const(val) && !pinned_keys.iter().any(|k| k == key) {
            out.push(ChcExpr::eq(
                ChcExpr::select(ChcExpr::var(canonical.clone()), key.clone()),
                val.clone(),
            ));
            pinned_keys.push(key.clone());
        }
        cursor = base;
    }

    // plain-var form: scan the init body constraint for select pins on this var.
    if let ChcExpr::Var(array_var) = init_arg {
        for conjunct in conjunct_refs(init_constraint) {
            if let Some((key, value, width)) = select_const_eq(conjunct, array_var) {
                out.push(ChcExpr::eq(
                    ChcExpr::select(ChcExpr::var(canonical.clone()), key),
                    ChcExpr::BitVec(value, width),
                ));
                continue;
            }
            // Bool cell pinned true: `(select array_var key)`.
            if let Some((array, key)) = select_args(conjunct) {
                if expr_is_var(array, array_var) {
                    out.push(ChcExpr::select(
                        ChcExpr::var(canonical.clone()),
                        key.clone(),
                    ));
                    continue;
                }
            }
            // Bool cell pinned false: `(not (select array_var key))`.
            if let ChcExpr::Op(ChcOp::Not, inner) = conjunct {
                if inner.len() == 1 {
                    if let Some((array, key)) = select_args(inner[0].as_ref()) {
                        if expr_is_var(array, array_var) {
                            out.push(ChcExpr::not(ChcExpr::select(
                                ChcExpr::var(canonical.clone()),
                                key.clone(),
                            )));
                        }
                    }
                }
            }
        }
    }
}

/// Recognize the STORE-PRESERVING array-cell shape — the model-checker-consumer Mem-track
/// pattern — and synthesize its safety invariant.
///
/// The predicate's array parameters are carried UNCHANGED across the single
/// transition (`next_arr` is syntactically the body's `arr`), so every cell they
/// pin at init is a loop invariant. This differs from
/// `bv_array_counter_cell_candidate`, which requires the cell to *increment*
/// with the counter (`counter != 0 => cell = init+1`) and only handles a
/// 2-arg predicate. The store-preserving shape has any arity (a live BV/Int
/// counter alongside one or more preserved arrays), possibly no counter bound,
/// and a Bool- or BV-valued query cell.
///
/// The synthesized invariant is the conjunction of the init cell pins. It is
/// returned as a candidate only; `try_bv_array_preserved_cell_safe_route`
/// validates it against the ORIGINAL clauses (`verify_model_per_rule`) before it
/// is ever accepted, so a syntactic mis-recognition cannot produce an unsound
/// SAFE result.
fn bv_array_preserved_cell_candidate(problem: &crate::ChcProblem) -> Option<InvariantModel> {
    if problem.predicates().len() != 1
        || problem.facts().count() != 1
        || problem.transitions().count() != 1
        || problem.queries().count() == 0
    {
        return None;
    }

    let pred = problem.predicates().first()?;
    let vars: Vec<ChcVar> = pred
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("__p{}_a{}", pred.id.index(), i), sort.clone()))
        .collect();

    let array_positions: Vec<usize> = pred
        .arg_sorts
        .iter()
        .enumerate()
        .filter(|(_, sort)| {
            matches!(sort, ChcSort::Array(key, _)
                if matches!(**key, ChcSort::BitVec(_) | ChcSort::Int))
        })
        .map(|(i, _)| i)
        .collect();
    if array_positions.is_empty() {
        return None;
    }

    // Transition: every array parameter is carried through unchanged.
    let transition = problem.transitions().next()?;
    let ClauseHead::Predicate(head_pred, head_args) = &transition.head else {
        return None;
    };
    let [(body_pred, body_args)] = transition.body.predicates.as_slice() else {
        return None;
    };
    if *head_pred != pred.id
        || *body_pred != pred.id
        || head_args.len() != vars.len()
        || body_args.len() != vars.len()
    {
        return None;
    }
    for &j in &array_positions {
        // Preserved iff the head array arg is exactly the body's array var.
        if !matches!(body_args[j], ChcExpr::Var(_)) || head_args[j] != body_args[j] {
            return None;
        }
    }

    // Init: collect the constant-cell pins for each preserved array.
    let fact = problem.facts().next()?;
    let ClauseHead::Predicate(fact_pred, init_args) = &fact.head else {
        return None;
    };
    if *fact_pred != pred.id || init_args.len() != vars.len() {
        return None;
    }
    let init_constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));

    let mut pins: Vec<ChcExpr> = Vec::new();
    for &j in &array_positions {
        collect_preserved_cell_pins(&init_args[j], &init_constraint, &vars[j], &mut pins);
    }
    if pins.is_empty() {
        return None;
    }

    let mut model = InvariantModel::new();
    model.set(
        pred.id,
        PredicateInterpretation::new(vars, ChcExpr::and_all(pins)),
    );
    Some(model)
}

fn adaptive_resolved_head_arg_definitions(
    clause: &crate::HornClause,
    body_args: &[ChcExpr],
    head_args: &[ChcExpr],
) -> Option<Vec<ChcExpr>> {
    let mut definitions = Vec::with_capacity(head_args.len());
    for head_arg in head_args {
        if body_args.iter().any(|body_arg| body_arg == head_arg) {
            definitions.push(head_arg.clone());
        } else if let ChcExpr::Var(var) = head_arg {
            let constraint = clause.body.constraint.as_ref()?;
            definitions.push(adaptive_find_var_definition(constraint, var)?);
        } else {
            definitions.push(head_arg.clone());
        }
    }
    Some(definitions)
}

fn adaptive_find_var_definition(expr: &ChcExpr, var: &ChcVar) -> Option<ChcExpr> {
    match expr {
        ChcExpr::Op(ChcOp::And, args) => args
            .iter()
            .find_map(|arg| adaptive_find_var_definition(arg.as_ref(), var)),
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            if matches_var(args[0].as_ref(), var) {
                Some(args[1].as_ref().clone())
            } else if matches_var(args[1].as_ref(), var) {
                Some(args[0].as_ref().clone())
            } else {
                None
            }
        }
        _ => None,
    }
}

fn matches_var(expr: &ChcExpr, var: &ChcVar) -> bool {
    matches!(expr, ChcExpr::Var(candidate) if candidate.name == var.name && candidate.sort == var.sort)
}

fn is_add_const_update(expr: &ChcExpr, base: &ChcExpr, value: i64) -> bool {
    let ChcExpr::Op(ChcOp::Add, _) = expr else {
        return false;
    };
    let mut terms = Vec::new();
    flatten_add_terms(expr, &mut terms);
    if terms.len() != 2 {
        return false;
    }
    (terms[0] == *base && terms[1].as_i64() == Some(value))
        || (terms[1] == *base && terms[0].as_i64() == Some(value))
}

fn is_sum_of_terms(expr: &ChcExpr, expected_terms: &[ChcExpr]) -> bool {
    let mut actual_terms = Vec::new();
    flatten_add_terms(expr, &mut actual_terms);
    if actual_terms.len() != expected_terms.len() {
        return false;
    }

    let mut remaining = expected_terms.to_vec();
    for term in actual_terms {
        let Some(pos) = remaining.iter().position(|expected| *expected == term) else {
            return false;
        };
        remaining.remove(pos);
    }
    remaining.is_empty()
}

fn flatten_add_terms(expr: &ChcExpr, out: &mut Vec<ChcExpr>) {
    match expr {
        ChcExpr::Op(ChcOp::Add, args) => {
            for arg in args {
                flatten_add_terms(arg.as_ref(), out);
            }
        }
        other => out.push(other.clone()),
    }
}

fn expr_any(expr: &ChcExpr, predicate: &mut impl FnMut(&ChcExpr) -> bool) -> bool {
    if predicate(expr) {
        return true;
    }
    match expr {
        ChcExpr::Op(_, args) => args.iter().any(|arg| expr_any(arg.as_ref(), predicate)),
        ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args.iter().any(|arg| expr_any(arg, predicate))
        }
        ChcExpr::ConstArray(_, value) => expr_any(value, predicate),
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Real(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_) => false,
    }
}

fn expr_contains_int_lower_bound_on(expr: &ChcExpr, term: &ChcExpr) -> bool {
    int_lower_bound_threshold(expr, term).is_some()
}

fn int_lower_bound_threshold(expr: &ChcExpr, term: &ChcExpr) -> Option<(i64, bool)> {
    let mut found = None;
    expr_any(expr, &mut |candidate| {
        found = match candidate {
            ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => (args[0].as_ref() == term)
                .then(|| args[1].as_i64().map(|threshold| (threshold, true)))
                .flatten()
                .or(found),
            ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => (args[0].as_ref() == term)
                .then(|| args[1].as_i64().map(|threshold| (threshold, false)))
                .flatten()
                .or(found),
            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => (args[1].as_ref() == term)
                .then(|| args[0].as_i64().map(|threshold| (threshold, true)))
                .flatten()
                .or(found),
            ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => (args[1].as_ref() == term)
                .then(|| args[0].as_i64().map(|threshold| (threshold, false)))
                .flatten()
                .or(found),
            _ => found,
        };
        found.is_some()
    });
    found
}

fn fact_arg_exact_int_values(
    clause: &crate::HornClause,
    fact_args: &[ChcExpr],
) -> Option<Vec<i64>> {
    let constraint = clause.body.constraint.as_ref()?;
    let mut values = Vec::with_capacity(fact_args.len());
    for arg in fact_args {
        values.push(eval_int_expr_under_constraint(arg, constraint, 0)?);
    }
    Some(values)
}

fn eval_int_expr_under_constraint(
    expr: &ChcExpr,
    constraint: &ChcExpr,
    depth: usize,
) -> Option<i64> {
    if depth > 8 {
        return None;
    }
    if let Some(value) = expr.as_i64() {
        return Some(value);
    }
    match expr {
        ChcExpr::Var(var) => {
            let definition = adaptive_find_var_definition(constraint, var)?;
            eval_int_expr_under_constraint(&definition, constraint, depth + 1)
        }
        ChcExpr::Op(ChcOp::Add, args) => {
            let mut sum = 0i64;
            for arg in args {
                sum = sum.checked_add(eval_int_expr_under_constraint(
                    arg.as_ref(),
                    constraint,
                    depth + 1,
                )?)?;
            }
            Some(sum)
        }
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            eval_int_expr_under_constraint(args[0].as_ref(), constraint, depth + 1)?.checked_sub(
                eval_int_expr_under_constraint(args[1].as_ref(), constraint, depth + 1)?,
            )
        }
        ChcExpr::Op(ChcOp::Mul, args) => {
            let mut product = 1i64;
            for arg in args {
                product = product.checked_mul(eval_int_expr_under_constraint(
                    arg.as_ref(),
                    constraint,
                    depth + 1,
                )?)?;
            }
            Some(product)
        }
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            eval_int_expr_under_constraint(args[0].as_ref(), constraint, depth + 1)?.checked_neg()
        }
        _ => None,
    }
}

fn int_lower_bound_holds(value: i64, threshold: i64, strict: bool) -> bool {
    if strict {
        value > threshold
    } else {
        value >= threshold
    }
}

impl AdaptivePortfolio {
    fn apply_adt_lia_model_interp(
        interp: &PredicateInterpretation,
        args: &[ChcExpr],
    ) -> Option<ChcExpr> {
        if interp.vars.len() != args.len() {
            return None;
        }

        let subst: Vec<(ChcVar, ChcExpr)> = interp
            .vars
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();
        Some(interp.formula.substitute(&subst))
    }

    fn adt_lia_expr_under_model(expr: &ChcExpr, model: &InvariantModel) -> Option<ChcExpr> {
        match expr {
            ChcExpr::PredicateApp(_, pred, args) => {
                let interp = model.get(pred)?;
                let plain_args = args
                    .iter()
                    .map(|arg| Self::adt_lia_expr_under_model(arg.as_ref(), model))
                    .collect::<Option<Vec<_>>>()?;
                Self::apply_adt_lia_model_interp(interp, &plain_args)
            }
            ChcExpr::Op(op, args) => Some(ChcExpr::Op(
                *op,
                args.iter()
                    .map(|arg| Self::adt_lia_expr_under_model(arg.as_ref(), model).map(Arc::new))
                    .collect::<Option<Vec<_>>>()?,
            )),
            ChcExpr::FuncApp(name, sort, args) => Some(ChcExpr::FuncApp(
                name.clone(),
                sort.clone(),
                args.iter()
                    .map(|arg| Self::adt_lia_expr_under_model(arg.as_ref(), model).map(Arc::new))
                    .collect::<Option<Vec<_>>>()?,
            )),
            ChcExpr::ConstArray(sort, value) => Some(ChcExpr::ConstArray(
                sort.clone(),
                Arc::new(Self::adt_lia_expr_under_model(value.as_ref(), model)?),
            )),
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Var(_)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => Some(expr.clone()),
        }
    }

    fn adt_lia_body_under_model(
        body: &crate::ClauseBody,
        model: &InvariantModel,
    ) -> Option<ChcExpr> {
        let mut parts = Vec::new();
        if let Some(constraint) = &body.constraint {
            parts.push(Self::adt_lia_expr_under_model(constraint, model)?);
        }

        for (pred, args) in &body.predicates {
            let interp = model.get(pred)?;
            parts.push(Self::apply_adt_lia_model_interp(interp, args)?);
        }

        Some(ChcExpr::and_all(parts))
    }

    fn adt_lia_head_under_model(head: &ClauseHead, model: &InvariantModel) -> Option<ChcExpr> {
        match head {
            ClauseHead::False => Some(ChcExpr::Bool(false)),
            ClauseHead::Predicate(pred, args) => {
                let interp = model.get(pred)?;
                Self::apply_adt_lia_model_interp(interp, args)
            }
        }
    }

    fn validate_adt_lia_model_on_original_clauses(
        &self,
        model: &InvariantModel,
        per_clause_budget: Duration,
    ) -> Result<(), String> {
        for (clause_idx, clause) in self.problem.clauses().iter().enumerate() {
            let Some(body) = Self::adt_lia_body_under_model(&clause.body, model) else {
                return Err(format!("clause_{clause_idx}_body"));
            };
            // Keep the original replay formula intact for the DT executor. Local
            // simplification can drop singleton-list disjuncts before constructor
            // injectivity is available, turning valid safety obligations SAT.
            let query = match &clause.head {
                ClauseHead::False => body,
                ClauseHead::Predicate(_, _) => {
                    let Some(head) = Self::adt_lia_head_under_model(&clause.head, model) else {
                        return Err(format!("clause_{clause_idx}_head"));
                    };
                    ChcExpr::and(body, ChcExpr::not(head))
                }
            };

            if matches!(query, ChcExpr::Bool(false)) {
                continue;
            }

            let smt = self.problem.make_smt_context();
            let propagated_model = ay_core::kani_compat::DetHashMap::default();
            match smt.check_sat_via_executor(&query, &propagated_model, per_clause_budget) {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
                SmtResult::Sat(_) => return Err(format!("clause_{clause_idx}_sat")),
                SmtResult::Unknown => return Err(format!("clause_{clause_idx}_unknown")),
            }
        }

        Ok(())
    }

    fn validate_translated_safe_model_on_original(
        &self,
        model: &InvariantModel,
        per_clause_budget: Duration,
    ) -> bool {
        if per_clause_budget.is_zero() {
            return false;
        }

        let mut verifier = PdrSolver::new(
            self.problem.clone(),
            PdrConfig {
                verbose: self.config.verbose,
                strict_proofs: true,
                solve_timeout: Some(per_clause_budget),
                disable_array_scalarization: true,
                preserve_original_clauses: true,
                ..PdrConfig::default()
            },
        );
        if verifier.verify_model_per_rule(model, per_clause_budget) {
            return true;
        }

        if self.problem.has_datatype_sorts() {
            match self.validate_adt_lia_model_on_original_clauses(model, per_clause_budget) {
                Ok(()) => return true,
                Err(reason) if self.config.verbose => {
                    safe_eprintln!(
                        "Adaptive: DT original-clause validator rejected model: {reason}"
                    );
                }
                Err(_) => {}
            }
        }

        false
    }

    fn try_bv_array_counter_cell_safe_route(
        &self,
        budget: Duration,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        let route_start = Instant::now();
        if budget < Duration::from_millis(100) {
            return None;
        }

        let candidate = bv_array_counter_cell_candidate(&self.problem)?;
        let pred = self.problem.predicates().first()?;
        let vars: Vec<_> = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| ChcVar::new(format!("__p{}_a{}", pred.id.index(), i), sort.clone()))
            .collect();
        let array = ChcExpr::var(vars[candidate.array_arg_index].clone());
        let counter = ChcExpr::var(vars[candidate.counter_arg_index].clone());
        let selected = ChcExpr::select(array, candidate.key.clone());
        let zero = ChcExpr::BitVec(0, candidate.counter_width);
        let init_value = ChcExpr::BitVec(candidate.init_value, candidate.value_width);
        let post_value = ChcExpr::BitVec(
            candidate.init_value.wrapping_add(1) & crate::bv_util::bv_mask(candidate.value_width),
            candidate.value_width,
        );
        let formula = ChcExpr::and_all([
            ChcExpr::bv_ule(counter.clone(), candidate.counter_bound),
            ChcExpr::implies(
                ChcExpr::eq(counter.clone(), zero.clone()),
                ChcExpr::eq(selected.clone(), init_value),
            ),
            ChcExpr::implies(
                ChcExpr::ne(counter, zero),
                ChcExpr::eq(selected, post_value),
            ),
        ]);

        let mut model = InvariantModel::new();
        model.set(pred.id, PredicateInterpretation::new(vars, formula));

        let validation_budget = budget
            .saturating_sub(route_start.elapsed())
            .min(Duration::from_secs(3));
        if self.validate_translated_safe_model_on_original(&model, validation_budget) {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: BV+array counter-cell invariant validated in {:.3}s",
                    route_start.elapsed().as_secs_f64()
                );
            }
            Some((
                PortfolioResult::Safe(model),
                ValidationEvidence::FullVerification,
            ))
        } else {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: BV+array counter-cell invariant rejected by original-clause validation"
                );
            }
            None
        }
    }

    /// Store-preserving array-cell safe route (model-checker-consumer Mem-track shape).
    ///
    /// Synthesizes the preserved-cell invariant (see
    /// `bv_array_preserved_cell_candidate`) and accepts it only after
    /// original-clause validation. This closes the store-preserving shape that
    /// the #8739 BV+array dual-lane otherwise leaves as `unknown`: its BV-native
    /// lane's PDR generalization couples the preserved cell with the wrapping BV
    /// counter (`cell OR counter>=1`, unsound under BV wraparound) and diverges,
    /// while the array-safe lane bit-blasts the counter and its IMC invariant
    /// fails query-only validation.
    fn try_bv_array_preserved_cell_safe_route(
        &self,
        budget: Duration,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        let route_start = Instant::now();
        if budget < Duration::from_millis(100) {
            return None;
        }

        let model = bv_array_preserved_cell_candidate(&self.problem)?;
        let validation_budget = budget
            .saturating_sub(route_start.elapsed())
            .min(Duration::from_secs(3));
        if self.validate_translated_safe_model_on_original(&model, validation_budget) {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: BV+array preserved-cell invariant validated in {:.3}s",
                    route_start.elapsed().as_secs_f64()
                );
            }
            Some((
                PortfolioResult::Safe(model),
                ValidationEvidence::FullVerification,
            ))
        } else {
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: BV+array preserved-cell invariant rejected by original-clause validation"
                );
            }
            None
        }
    }

    fn log_bv_bool_control_reachability_route(
        &self,
        gate_result: bool,
        gate_reason: String,
        budget: Duration,
        elapsed: Duration,
        result: &'static str,
    ) {
        self.decision_log.log_decision(DecisionEntry {
            stage: "bv_bool_control_reachability",
            gate_result,
            gate_reason,
            budget_secs: budget.as_secs_f64(),
            elapsed_secs: elapsed.as_secs_f64(),
            result,
            lemmas_learned: 0,
            max_frame: 0,
        });
    }

    fn bool_control_cube_expr(vars: &[ChcVar], bool_indices: &[usize], cube: usize) -> ChcExpr {
        let mut parts = Vec::with_capacity(bool_indices.len());
        for (bit, index) in bool_indices.iter().enumerate() {
            let atom = ChcExpr::var(vars[*index].clone());
            parts.push(if ((cube >> bit) & 1) == 1 {
                atom
            } else {
                ChcExpr::not(atom)
            });
        }
        ChcExpr::and_all(parts)
    }

    fn smt_sat_before_deadline(
        &self,
        formula: &ChcExpr,
        deadline: Instant,
        per_query_budget: Duration,
    ) -> Option<bool> {
        let remaining = deadline.checked_duration_since(Instant::now())?;
        let timeout = remaining.min(per_query_budget);
        if timeout < Duration::from_millis(1) {
            return None;
        }

        let mut ctx = self.problem.make_smt_context();
        match ctx.check_sat_with_timeout(formula, timeout) {
            SmtResult::Sat(_) => Some(true),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                Some(false)
            }
            SmtResult::Unknown => None,
        }
    }

    fn bool_control_reachability_model(
        &self,
        bool_indices: &[usize],
        reachable: &[bool],
    ) -> Option<InvariantModel> {
        let pred = self.problem.predicates().first()?;
        let vars: Vec<_> = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| ChcVar::new(format!("__p{}_a{}", pred.id.index(), i), sort.clone()))
            .collect();

        let mut cubes = Vec::new();
        for (cube, is_reachable) in reachable.iter().enumerate() {
            if *is_reachable {
                cubes.push(Self::bool_control_cube_expr(&vars, bool_indices, cube));
            }
        }

        let mut model = InvariantModel::new();
        model.set(
            pred.id,
            PredicateInterpretation::new(vars, ChcExpr::or_all(cubes)),
        );
        Some(model)
    }

    fn try_bv_bool_control_reachability_safe_route(
        &self,
        ts: &TransitionSystem,
        budget: Duration,
    ) -> Option<InvariantModel> {
        let route_start = Instant::now();
        if budget < Duration::from_millis(50) {
            return None;
        }

        let bool_indices: Vec<_> = ts
            .vars
            .iter()
            .enumerate()
            .filter_map(|(idx, var)| (var.sort == ChcSort::Bool).then_some(idx))
            .collect();
        if bool_indices.is_empty() || bool_indices.len() > 4 {
            self.log_bv_bool_control_reachability_route(
                false,
                format!("bool_controls={}", bool_indices.len()),
                budget,
                route_start.elapsed(),
                "not_applicable",
            );
            return None;
        }

        let Some(total_cubes) = 1usize.checked_shl(bool_indices.len() as u32) else {
            return None;
        };
        let synth_budget = budget.min(Duration::from_secs(3));
        let deadline = Instant::now() + synth_budget;
        let per_query_budget = if total_cubes <= 8 {
            Duration::from_millis(100)
        } else {
            Duration::from_millis(50)
        };
        let gate_reason = format!(
            "predicate={} bool_controls={} cubes={} init_nodes={} transition_nodes={} query_nodes={}",
            ts.predicate.index(),
            bool_indices.len(),
            total_cubes,
            ts.init.node_count(10_000),
            ts.transition.node_count(10_000),
            ts.query.node_count(10_000),
        );

        let mut reachable = vec![false; total_cubes];
        let mut worklist = Vec::new();
        for (cube, reachable_cube) in reachable.iter_mut().enumerate().take(total_cubes) {
            let query = ChcExpr::and(
                ts.init.clone(),
                Self::bool_control_cube_expr(&ts.vars, &bool_indices, cube),
            );
            match self.smt_sat_before_deadline(&query, deadline, per_query_budget) {
                Some(true) => {
                    *reachable_cube = true;
                    worklist.push(cube);
                }
                Some(false) => {}
                None => {
                    self.log_bv_bool_control_reachability_route(
                        true,
                        gate_reason,
                        budget,
                        route_start.elapsed(),
                        "init_unknown",
                    );
                    return None;
                }
            }
        }

        if worklist.is_empty() {
            self.log_bv_bool_control_reachability_route(
                true,
                gate_reason,
                budget,
                route_start.elapsed(),
                "empty_init",
            );
            return None;
        }

        let next_vars: Vec<ChcVar> = ts
            .vars
            .iter()
            .map(|v| ChcVar::new(format!("{}_next", v.name), v.sort.clone()))
            .collect();
        let mut cursor = 0;
        while cursor < worklist.len() {
            let pre_cube = worklist[cursor];
            cursor += 1;
            let pre = Self::bool_control_cube_expr(&ts.vars, &bool_indices, pre_cube);

            for (post_cube, reachable_post_cube) in
                reachable.iter_mut().enumerate().take(total_cubes)
            {
                if *reachable_post_cube {
                    continue;
                }

                let post = Self::bool_control_cube_expr(&next_vars, &bool_indices, post_cube);
                let query = ChcExpr::and(ChcExpr::and(pre.clone(), ts.transition.clone()), post);
                match self.smt_sat_before_deadline(&query, deadline, per_query_budget) {
                    Some(true) => {
                        *reachable_post_cube = true;
                        worklist.push(post_cube);
                    }
                    Some(false) => {}
                    None => {
                        self.log_bv_bool_control_reachability_route(
                            true,
                            gate_reason,
                            budget,
                            route_start.elapsed(),
                            "transition_unknown",
                        );
                        return None;
                    }
                }
            }
        }

        let reachable_count = reachable
            .iter()
            .filter(|&&is_reachable| is_reachable)
            .count();
        if reachable_count == total_cubes {
            self.log_bv_bool_control_reachability_route(
                true,
                format!("{gate_reason} reachable={reachable_count}/{total_cubes}"),
                budget,
                route_start.elapsed(),
                "all_control_cubes_reachable",
            );
            return None;
        }

        for (cube, is_reachable) in reachable.iter().enumerate() {
            if !*is_reachable {
                continue;
            }
            let query = ChcExpr::and(
                ts.query.clone(),
                Self::bool_control_cube_expr(&ts.vars, &bool_indices, cube),
            );
            match self.smt_sat_before_deadline(&query, deadline, per_query_budget) {
                Some(false) => {}
                Some(true) => {
                    self.log_bv_bool_control_reachability_route(
                        true,
                        format!("{gate_reason} reachable={reachable_count}/{total_cubes}"),
                        budget,
                        route_start.elapsed(),
                        "reachable_bad_control_cube",
                    );
                    return None;
                }
                None => {
                    self.log_bv_bool_control_reachability_route(
                        true,
                        format!("{gate_reason} reachable={reachable_count}/{total_cubes}"),
                        budget,
                        route_start.elapsed(),
                        "query_unknown",
                    );
                    return None;
                }
            }
        }

        let Some(model) = self.bool_control_reachability_model(&bool_indices, &reachable) else {
            return None;
        };
        let validation_budget = budget
            .saturating_sub(route_start.elapsed())
            .min(Duration::from_secs(2));
        if self.validate_translated_safe_model_on_original(&model, validation_budget) {
            self.log_bv_bool_control_reachability_route(
                true,
                format!("{gate_reason} reachable={reachable_count}/{total_cubes}"),
                budget,
                route_start.elapsed(),
                "safe_validated",
            );
            Some(model)
        } else {
            self.log_bv_bool_control_reachability_route(
                true,
                format!("{gate_reason} reachable={reachable_count}/{total_cubes}"),
                budget,
                route_start.elapsed(),
                "safe_validation_rejected",
            );
            None
        }
    }

    pub(crate) fn simple_loop_needs_dillig_style_kind_headroom(
        &self,
        features: &ProblemFeatures,
    ) -> bool {
        if features.num_predicates != 1
            || features.num_facts != 1
            || features.num_transitions != 1
            || features.num_queries != 1
            || features.self_loop_ratio < 1.0
            || features.uses_arrays
            || features.uses_real
            || features.uses_datatypes
            || features.has_mod_div
            || self.problem.has_bv_sorts()
        {
            return false;
        }

        let Some(transition_clause) = self.problem.transitions().next() else {
            return false;
        };
        let Some(query_clause) = self.problem.queries().next() else {
            return false;
        };
        let Some(query_constraint) = query_clause.body.constraint.as_ref() else {
            return false;
        };

        let transition_head_args = match &transition_clause.head {
            ClauseHead::Predicate(_, args) => args.as_slice(),
            ClauseHead::False => &[],
        };
        let transition_has_ite = transition_clause
            .body
            .constraint
            .as_ref()
            .is_some_and(expr_contains_ite)
            || transition_head_args.iter().any(expr_contains_ite);
        let transition_mul = DilligMulProfile::scan_all(
            transition_clause
                .body
                .constraint
                .iter()
                .chain(transition_head_args.iter()),
        );
        let query_mul = DilligMulProfile::scan(query_constraint);
        transition_has_ite
            && transition_mul.has_nontrivial_scalar_coeff_mul
            && query_mul.has_nontrivial_scalar_coeff_mul
            && transition_mul.all_mul_are_scalar_coeff
            && query_mul.all_mul_are_scalar_coeff
    }

    fn simple_loop_kind_budget_nominal(&self, features: &ProblemFeatures) -> Duration {
        if self.problem.has_bv_sorts() {
            Duration::from_secs(1)
        } else if self.simple_loop_needs_dillig_style_kind_headroom(features) {
            Duration::from_secs(3)
        } else if self.simple_loop_needs_deep_lia_unsafe_kind_budget(features) {
            Duration::from_secs(8)
        } else {
            Duration::from_millis(1500)
        }
    }

    fn simple_loop_needs_deep_lia_unsafe_kind_budget(&self, features: &ProblemFeatures) -> bool {
        if features.num_predicates != 1
            || features.num_facts != 1
            || features.num_transitions != 1
            || features.num_queries != 1
            || features.self_loop_ratio < 1.0
            || features.uses_arrays
            || features.uses_real
            || features.uses_datatypes
            || features.has_mod_div
            || features.has_ite
            || self.problem.has_bv_sorts()
        {
            return false;
        }

        let Some(pred) = self.problem.predicates().first() else {
            return false;
        };
        if pred.arg_sorts.len() != 2
            || !pred
                .arg_sorts
                .iter()
                .all(|sort| matches!(sort, ChcSort::Int))
        {
            return false;
        }

        let Some(transition) = self.problem.transitions().next() else {
            return false;
        };
        let [(body_pred, body_args)] = transition.body.predicates.as_slice() else {
            return false;
        };
        let ClauseHead::Predicate(head_pred, head_args) = &transition.head else {
            return false;
        };
        if *body_pred != pred.id
            || *head_pred != pred.id
            || body_args.len() != 2
            || head_args.len() != 2
        {
            return false;
        }
        let Some(head_defs) =
            adaptive_resolved_head_arg_definitions(transition, body_args, head_args)
        else {
            return false;
        };
        if !is_add_const_update(&head_defs[0], &body_args[0], 1)
            || !is_sum_of_terms(&head_defs[1], &[body_args[1].clone(), body_args[0].clone()])
        {
            return false;
        }

        let Some(query) = self.problem.queries().next() else {
            return false;
        };
        let [(query_pred, query_args)] = query.body.predicates.as_slice() else {
            return false;
        };
        if *query_pred != pred.id || query_args.len() != 2 {
            return false;
        }
        query
            .body
            .constraint
            .as_ref()
            .is_some_and(|constraint| expr_contains_int_lower_bound_on(constraint, &query_args[1]))
    }

    pub(super) fn try_accumulator_lia_unsafe_counterexample(
        &self,
        features: &ProblemFeatures,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        if !self.simple_loop_needs_deep_lia_unsafe_kind_budget(features) {
            return None;
        }

        let pred = self.problem.predicates().first()?;
        let fact = self.problem.facts().next()?;
        let ClauseHead::Predicate(fact_pred, fact_args) = &fact.head else {
            return None;
        };
        if *fact_pred != pred.id || fact_args.len() != 2 {
            return None;
        }
        let init_values = fact_arg_exact_int_values(fact, fact_args)?;

        let query = self.problem.queries().next()?;
        let [(query_pred, query_args)] = query.body.predicates.as_slice() else {
            return None;
        };
        if *query_pred != pred.id || query_args.len() != 2 {
            return None;
        }
        let (threshold, strict) =
            int_lower_bound_threshold(query.body.constraint.as_ref()?, &query_args[1])?;

        let mut x = init_values[0];
        let mut y = init_values[1];
        let mut steps = Vec::new();
        for depth in 0..=256usize {
            let mut assignments = FxHashMap::default();
            assignments.insert(crate::lemma_hints::canonical_var_name(pred.id, 0), x);
            assignments.insert(crate::lemma_hints::canonical_var_name(pred.id, 1), y);
            steps.push(CounterexampleStep::new(pred.id, assignments));

            if int_lower_bound_holds(y, threshold, strict) {
                let cex = Counterexample::new(steps);
                let validation_budget = Duration::from_secs(3);
                if self.validate_original_counterexample_with_budget(&cex, validation_budget) {
                    return Some((
                        PortfolioResult::Unsafe(cex),
                        ValidationEvidence::CounterexampleVerification,
                    ));
                }
                return None;
            }

            let next_y = y.checked_add(x)?;
            let next_x = x.checked_add(1)?;
            x = next_x;
            y = next_y;

            if depth == 256 {
                return None;
            }
        }
        None
    }

    /// Guess-and-check the IsaPlanner `last`-style constructor-case invariant
    /// `list = nil \/ list = cons(x, nil) \/ tail(list) != nil` for
    /// single-predicate ADT+LIA problems over one Int and one recursive
    /// Int-list argument.
    ///
    /// Called from `solve_internal`'s pre-strategy sequence (after the
    /// datatype bounded-BMC unsafe refutation, before the CATA abstraction
    /// lane): the CATA lane's refinement rounds burn multi-second budgets on
    /// exactly this shape, while this guess either validates in milliseconds
    /// or fails closed. Sound: the candidate only leaves through strict
    /// per-rule verification / SMT replay against the ORIGINAL clauses.
    pub(super) fn try_adt_lia_constructor_case_synthesis(
        &self,
        features: &ProblemFeatures,
    ) -> Option<PortfolioResult> {
        if !features.is_single_predicate
            || !features.uses_datatypes
            || features.uses_arrays
            || features.uses_real
            || self.problem.has_bv_sorts()
            || self.problem.predicates().len() != 1
        {
            return None;
        }

        let pred = self.problem.predicates().first()?;
        if pred.arg_sorts.len() != 2 || self.problem.queries().next().is_none() {
            return None;
        }

        let candidates = pred
            .arg_sorts
            .iter()
            .enumerate()
            .filter(|(_, sort)| matches!(sort, ChcSort::Int))
            .flat_map(|(int_idx, _)| {
                pred.arg_sorts
                    .iter()
                    .enumerate()
                    .filter_map(move |(list_idx, sort)| {
                        recursive_list_int_view(sort).map(|view| (int_idx, list_idx, view))
                    })
            })
            .collect::<Vec<_>>();

        for (int_idx, list_idx, list_view) in candidates {
            let start = Instant::now();
            let vars: Vec<_> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(arg_idx, sort)| {
                    ChcVar::new(format!("__p{}_a{}", pred.id.index(), arg_idx), sort.clone())
                })
                .collect();

            let list = ChcExpr::var(vars[list_idx].clone());
            let tail = ChcExpr::FuncApp(
                list_view.tail_selector.clone(),
                list_view.sort.clone(),
                vec![Arc::new(list.clone())],
            );
            let nil = ChcExpr::FuncApp(
                list_view.nil_ctor.clone(),
                list_view.sort.clone(),
                Vec::new(),
            );
            let singleton_with_value = ChcExpr::FuncApp(
                list_view.cons_ctor.clone(),
                list_view.sort.clone(),
                vec![
                    Arc::new(ChcExpr::var(vars[int_idx].clone())),
                    Arc::new(nil.clone()),
                ],
            );
            let formula = ChcExpr::or_all([
                ChcExpr::eq(list.clone(), nil.clone()),
                ChcExpr::eq(list, singleton_with_value),
                ChcExpr::not(ChcExpr::eq(tail, nil)),
            ]);

            let mut model = InvariantModel::new();
            model.set(pred.id, PredicateInterpretation::new(vars, formula));

            let mut verifier = PdrSolver::new(
                self.problem.clone(),
                PdrConfig {
                    verbose: self.config.verbose,
                    strict_proofs: true,
                    solve_timeout: Some(Duration::from_secs(30)),
                    disable_array_scalarization: true,
                    preserve_original_clauses: true,
                    ..PdrConfig::default()
                },
            );
            let pdr_accepted = verifier.verify_model_per_rule(&model, Duration::from_millis(1500));
            let replay_result = if pdr_accepted {
                Ok(())
            } else {
                self.validate_adt_lia_model_on_original_clauses(&model, Duration::from_millis(1500))
            };
            let replay_accepted = replay_result.is_ok();
            let validator = if pdr_accepted {
                "pdr_accepted".to_string()
            } else if replay_accepted {
                "smt_replay_accepted".to_string()
            } else {
                format!(
                    "rejected:{}",
                    replay_result
                        .as_ref()
                        .err()
                        .map(String::as_str)
                        .unwrap_or("unknown")
                )
            };
            self.decision_log.log_decision(DecisionEntry {
                stage: "adt_lia_constructor_case_synthesis",
                gate_result: replay_accepted,
                gate_reason: format!(
                    "predicate={} int_arg={} list_arg={} validator={}",
                    pred.name, int_idx, list_idx, validator
                ),
                budget_secs: 1.5,
                elapsed_secs: start.elapsed().as_secs_f64(),
                result: if replay_accepted { "safe" } else { "skipped" },
                lemmas_learned: 0,
                max_frame: 0,
            });

            if replay_accepted {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: ADT-LIA constructor-case invariant validated on original problem"
                    );
                }
                return Some(PortfolioResult::Safe(model));
            }
        }

        None
    }

    fn validate_original_counterexample_with_budget(
        &self,
        cex: &Counterexample,
        budget: Duration,
    ) -> bool {
        if budget.is_zero() {
            return false;
        }

        let mut verifier = PdrSolver::new(
            self.problem.clone(),
            PdrConfig {
                verbose: self.config.verbose,
                solve_timeout: Some(budget),
                disable_array_scalarization: true,
                preserve_original_clauses: true,
                ..PdrConfig::default()
            },
        );
        verifier.set_validation_deadline(budget);
        matches!(
            verifier
                .try_verify_counterexample(cex)
                .unwrap_or(crate::CexVerificationResult::Unknown),
            crate::CexVerificationResult::Valid
        )
    }

    fn log_deterministic_bv_bool_transition_route(
        &self,
        gate_result: bool,
        gate_reason: String,
        budget: Duration,
        elapsed: Duration,
        result: &'static str,
    ) {
        self.log_deterministic_bv_bool_transition_route_with_details(
            gate_result,
            gate_reason,
            budget,
            elapsed,
            result,
            serde_json::Value::Null,
        );
    }

    fn log_deterministic_bv_bool_transition_route_with_details(
        &self,
        gate_result: bool,
        gate_reason: String,
        budget: Duration,
        elapsed: Duration,
        result: &'static str,
        details: serde_json::Value,
    ) {
        self.decision_log.log_decision_with_details(
            DecisionEntry {
                stage: "deterministic_bv_bool_transition",
                gate_result,
                gate_reason,
                budget_secs: budget.as_secs_f64(),
                elapsed_secs: elapsed.as_secs_f64(),
                result,
                lemmas_learned: 0,
                max_frame: 0,
            },
            details,
        );
    }

    /// Deterministic BV/Bool transition route.
    ///
    /// This is intentionally bug-finding first: BMC searches deeper than the
    /// common BV Kind pre-pass and accepts only source-validated witnesses.
    /// Safe candidates come from Kind and must validate as full invariants on
    /// the original CHC before leaving this route. Failed validation is a hard
    /// UNKNOWN, not a silent pass to the next route.
    pub(crate) fn try_deterministic_bv_bool_transition_route(
        &self,
        budget: Duration,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        let route_start = Instant::now();
        let route_budget = budget.min(Duration::from_secs(5));
        if route_budget < Duration::from_millis(10) {
            return None;
        }
        self.record_deterministic_bv_bool_transition_attempt();

        let ts = match TransitionSystem::from_chc_problem(&self.problem) {
            Ok(ts) => ts,
            Err(reason) => {
                self.log_deterministic_bv_bool_transition_route(
                    false,
                    format!("transition-system extraction failed: {reason}"),
                    route_budget,
                    route_start.elapsed(),
                    "not_applicable",
                );
                return None;
            }
        };

        let Some(recognized) = ts.recognize_deterministic_bv_bool() else {
            self.log_deterministic_bv_bool_transition_route(
                false,
                "not deterministic Bool/BV transition syntax".to_string(),
                route_budget,
                route_start.elapsed(),
                "not_applicable",
            );
            return None;
        };
        self.record_deterministic_bv_bool_transition_recognized();

        let route_reason = format!(
            "predicate={} vars={} bool_vars={} bv_vars={} state_bits={} total_bv_width={} max_bv_width={} assignments={} guard={} guards={} conjuncts={} init_nodes={} trans_nodes={} query_nodes={}",
            recognized.predicate.index(),
            recognized.vars.len(),
            recognized.metadata.bool_state_vars,
            recognized.metadata.bv_state_vars,
            recognized.metadata.total_state_bits,
            recognized.metadata.total_bv_width,
            recognized.metadata.max_bv_width,
            recognized.next_assignments.len(),
            recognized.has_transition_guard,
            recognized.metadata.guard_conjuncts,
            recognized.metadata.transition_conjuncts,
            recognized.init.node_count(10_000),
            recognized.transition.node_count(10_000),
            recognized.query.node_count(10_000),
        );
        if self.config.verbose {
            safe_eprintln!(
                "Adaptive: Deterministic BV/Bool transition route recognized ({route_reason})"
            );
        }
        if let Some(model) = self.try_bv_bool_control_reachability_safe_route(&ts, route_budget) {
            self.record_deterministic_bv_bool_transition_bool_control_safe_validated();
            self.log_deterministic_bv_bool_transition_route(
                true,
                route_reason,
                route_budget,
                route_start.elapsed(),
                "bool_control_safe_validated",
            );
            return Some((
                PortfolioResult::Safe(model),
                ValidationEvidence::FullVerification,
            ));
        }

        let bmc_budget = route_budget.min(Duration::from_secs(2));
        if bmc_budget >= Duration::from_millis(10) {
            // Child of the portfolio handle (item 5).
            let cancel = self.cancellation_token.child();
            let _timeout_guard = cancel.cancel_after(bmc_budget);
            let bmc_config = BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    cancellation_token: Some(cancel),
                },
                max_depth: 128,
                per_depth_timeout: Some(bmc_budget.min(Duration::from_millis(500))),
                time_budget: Some(bmc_budget),
                enable_adaptive_stepping: true,
                enable_k_induction: false,
                acyclic_safe: false,
                prefer_exact_acyclic_first: false,
                proof_cross_check: false,
                ts_probe_clamp: None,
                sweep_past_spurious_sat: true,
            };
            let bmc_solver = crate::bmc::BmcSolver::new(self.problem.clone(), bmc_config);
            let bmc_result = bmc_solver.solve();
            let bmc_stats = bmc_solver.stats();
            let bmc_details = || {
                serde_json::json!({
                    "bmc_max_depth": bmc_stats.max_depth_reached,
                    "bmc_checks": bmc_stats.num_checks,
                    "bmc_budget_exhausted": bmc_stats.budget_exhausted,
                    "bmc_exhausted_search": bmc_stats.exhausted_search,
                    "bmc_used_executor_path": bmc_stats.used_executor_path,
                    "bmc_used_legacy_fallback": bmc_stats.used_legacy_fallback,
                })
            };
            match bmc_result {
                crate::engine_result::ChcEngineResult::Unsafe(cex) => {
                    if cex.witness.is_none() {
                        // The bad state is reachable but this route cannot
                        // rebuild a replayable witness (e.g. wide BV models the
                        // i64-oriented reconstructor cannot represent). A
                        // witness-less Unsafe is "known reachable but
                        // unprovable HERE", not a confident terminal verdict.
                        // Fall through (return None) so KIND/TPA/PDR/Lane-E —
                        // which have working witness extraction and validate
                        // their own counterexamples — get a chance. Never emit
                        // Unsafe/Unknown as a confident terminal here without a
                        // verified witness.
                        self.record_deterministic_bv_bool_transition_validation_rejection();
                        self.log_deterministic_bv_bool_transition_route_with_details(
                            true,
                            route_reason.clone(),
                            route_budget,
                            route_start.elapsed(),
                            "bmc_unsafe_missing_witness",
                            bmc_details(),
                        );
                        return None;
                    }
                    let validation_budget = route_budget
                        .saturating_sub(route_start.elapsed())
                        .min(Duration::from_secs(3));
                    let valid =
                        self.validate_original_counterexample_with_budget(&cex, validation_budget);
                    if valid {
                        self.record_deterministic_bv_bool_transition_bmc_unsafe_validated();
                    } else {
                        self.record_deterministic_bv_bool_transition_validation_rejection();
                    }
                    self.log_deterministic_bv_bool_transition_route_with_details(
                        true,
                        route_reason.clone(),
                        route_budget,
                        route_start.elapsed(),
                        if valid {
                            "bmc_unsafe_validated"
                        } else {
                            "bmc_unsafe_validation_rejected"
                        },
                        bmc_details(),
                    );
                    return Some(if valid {
                        (
                            PortfolioResult::Unsafe(cex),
                            ValidationEvidence::CounterexampleVerification,
                        )
                    } else {
                        (
                            PortfolioResult::Unknown,
                            ValidationEvidence::FullVerification,
                        )
                    });
                }
                crate::engine_result::ChcEngineResult::Safe(_) => {
                    self.log_deterministic_bv_bool_transition_route_with_details(
                        true,
                        route_reason,
                        route_budget,
                        route_start.elapsed(),
                        "bmc_safe_rejected",
                        bmc_details(),
                    );
                    return Some((
                        PortfolioResult::Unknown,
                        ValidationEvidence::FullVerification,
                    ));
                }
                crate::engine_result::ChcEngineResult::Unknown
                | crate::engine_result::ChcEngineResult::NotApplicable => {}
            }
        }

        let kind_budget = route_budget
            .saturating_sub(route_start.elapsed())
            .min(Duration::from_secs(3));
        if kind_budget < Duration::from_millis(10) {
            self.log_deterministic_bv_bool_transition_route(
                true,
                route_reason,
                route_budget,
                route_start.elapsed(),
                "unknown",
            );
            return None;
        }

        // Child of the portfolio handle (item 5).
        let cancel = self.cancellation_token.child();
        let cancellation_observer = cancel.clone();
        let _timeout_guard = cancel.cancel_after(kind_budget);
        let max_k = if recognized.vars.len() <= 16 { 6 } else { 3 };
        let kind_config = KindConfig::with_engine_config(
            max_k,
            kind_budget.min(Duration::from_millis(750)),
            kind_budget,
            self.config.verbose,
            Some(cancel),
        );
        let mut kind_solver = KindSolver::new(self.problem.clone(), kind_config);
        kind_solver.maybe_enable_tla_trace_from_env();
        let kind_result = kind_solver.solve();
        if cancellation_observer.is_cancelled() {
            self.log_deterministic_bv_bool_transition_route(
                true,
                route_reason,
                route_budget,
                route_start.elapsed(),
                "unknown",
            );
            return None;
        }

        match kind_result {
            KindResult::Safe(model) => {
                let validation_budget = route_budget
                    .saturating_sub(route_start.elapsed())
                    .min(Duration::from_secs(3));
                let valid =
                    self.validate_translated_safe_model_on_original(&model, validation_budget);
                if valid {
                    self.record_deterministic_bv_bool_transition_kind_safe_validated();
                } else {
                    self.record_deterministic_bv_bool_transition_validation_rejection();
                }
                self.log_deterministic_bv_bool_transition_route(
                    true,
                    route_reason,
                    route_budget,
                    route_start.elapsed(),
                    if valid {
                        "kind_safe_validated"
                    } else {
                        "kind_safe_validation_rejected"
                    },
                );
                Some(if valid {
                    (
                        PortfolioResult::Safe(model),
                        ValidationEvidence::FullVerification,
                    )
                } else {
                    (
                        PortfolioResult::Unknown,
                        ValidationEvidence::FullVerification,
                    )
                })
            }
            KindResult::Unsafe(cex) => {
                if cex.witness.is_none() {
                    // Witness-less k-induction base-case hit: the bad state is
                    // reachable but this route cannot rebuild a replayable
                    // witness. Fall through (return None) rather than claiming a
                    // confident terminal Unknown, so KIND/TPA/PDR/Lane-E — which
                    // validate their own counterexamples — can solve it. Never
                    // emit Unsafe/Unknown as terminal here without a witness.
                    self.record_deterministic_bv_bool_transition_validation_rejection();
                    self.log_deterministic_bv_bool_transition_route(
                        true,
                        route_reason,
                        route_budget,
                        route_start.elapsed(),
                        "kind_unsafe_missing_witness",
                    );
                    return None;
                }
                let validation_budget = route_budget
                    .saturating_sub(route_start.elapsed())
                    .min(Duration::from_secs(3));
                let valid =
                    self.validate_original_counterexample_with_budget(&cex, validation_budget);
                if valid {
                    self.record_deterministic_bv_bool_transition_kind_unsafe_validated();
                } else {
                    self.record_deterministic_bv_bool_transition_validation_rejection();
                }
                self.log_deterministic_bv_bool_transition_route(
                    true,
                    route_reason,
                    route_budget,
                    route_start.elapsed(),
                    if valid {
                        "kind_unsafe_validated"
                    } else {
                        "kind_unsafe_validation_rejected"
                    },
                );
                Some(if valid {
                    (
                        PortfolioResult::Unsafe(cex),
                        ValidationEvidence::CounterexampleVerification,
                    )
                } else {
                    (
                        PortfolioResult::Unknown,
                        ValidationEvidence::FullVerification,
                    )
                })
            }
            KindResult::Unknown | KindResult::NotApplicable => {
                self.log_deterministic_bv_bool_transition_route(
                    true,
                    route_reason,
                    route_budget,
                    route_start.elapsed(),
                    "unknown",
                );
                None
            }
        }
    }

    /// Solve simple loop problems with validation evidence tracking.
    ///
    /// Safe results get `FullVerification` evidence: direct Kind candidates are
    /// checked against the original init/transition/query clauses before they
    /// can leave the adaptive path.
    /// Part of #5746.
    pub(super) fn solve_simple_loop_with_evidence(
        &self,
        features: &ProblemFeatures,
        deadline: Option<ay_core::time::Instant>,
    ) -> (PortfolioResult, ValidationEvidence) {
        let _strategy_start = Instant::now();

        if features.uses_arrays && self.problem.has_bv_sorts() {
            let route_budget = self
                .remaining_budget(deadline)
                .unwrap_or(Duration::from_secs(5))
                .min(Duration::from_secs(5));
            if let Some(result) = self.try_bv_array_counter_cell_safe_route(route_budget) {
                return result;
            }
            if let Some(result) = self.try_bv_array_preserved_cell_safe_route(route_budget) {
                return result;
            }
        }

        // Stage 0: Try structural synthesis (< 1ms overhead)
        if let Some(result) = self.try_synthesis() {
            if self.config.verbose {
                safe_eprintln!("Adaptive: Simple loop solved by structural synthesis");
            }
            return (result, ValidationEvidence::FullVerification);
        }

        // The ADT-LIA constructor-case guess (`try_adt_lia_constructor_case_synthesis`)
        // moved to solve_internal's pre-strategy sequence: on the IsaPlanner
        // `last`/singleton shape the CATA lane otherwise burns the whole
        // budget before this cheap validated guess ever ran (#9700 margin).

        if let Some(result) = self.try_accumulator_lia_unsafe_counterexample(features) {
            return result;
        }

        if self.problem.has_bv_sorts() && !features.uses_arrays && !features.uses_datatypes {
            let deterministic_budget = self
                .remaining_budget(deadline)
                .unwrap_or(Duration::from_secs(5))
                .min(Duration::from_secs(5));
            if let Some(result) =
                self.try_deterministic_bv_bool_transition_route(deterministic_budget)
            {
                return result;
            }
        }

        // Stage 1: Try K-Induction (forward AND backward per Golem's Kind.cc)
        // This gives quick wins for problems with k-inductive invariants.
        // Reference: Golem Kind.cc:44-133 tries both forward and backward k-induction.
        // Cap Kind budget to the remaining time budget (if any).
        //
        // #6047: Skip KIND for problems with arrays. Bit-blasting array operations
        // (especially with BV32 indices) causes catastrophic blowup: a BV32-indexed
        // array at k=1 produces 689K SAT variables and 4.9M clauses, consuming the
        // entire solve budget. PDR/Spacer handles arrays far better via SMT-level
        // reasoning with array MBP (Model-Based Projection).
        //
        // #5877: KIND now uses non-incremental mode for BV problems (each query
        // gets a fresh SmtContext). This avoids the incremental solver state
        // corruption that caused false-UNSAT on BV bitblast formulas, while still
        // allowing KIND's k-induction to find proofs. The non-incremental path
        // is slower (no learned clause reuse) but correct.
        //
        // #7930: Skip Kind for DT problems too. Kind with SingleLoop encoding
        // produces huge flattened formulas for DT+BV problems (Option<u8>,
        // struct wrappers), adding CPU contention without useful k-induction
        // results. Matches the ComplexLoop DT guard in adaptive_multi_pred_complex.rs.
        let skip_kind = features.uses_arrays || features.uses_datatypes;
        if !skip_kind {
            // #5877: BV problems get a tight KIND budget. Non-incremental
            // BV-to-Int queries at k>=2 produce formulas with 3+ copies of
            // the transition relation (each with BV range constraints). Even
            // with a 1s per-query timeout, preprocessing consumes the entire
            // budget before DPLL starts. Cap BV to 1s (enough for k=0/k=1
            // which take ~40ms total). Pure LIA gets 3s — enough for k=0..3
            // attempts while leaving budget for the PDR probe and parallel
            // portfolio that follow. Previous 8s starved PDR for problems
            // like yz_plus_minus_1 and s_mutants_02 that need relational
            // invariants (not k-inductive).
            // #8856: Keep the common pure-LIA pre-pass at 1.5s so fruitless
            // induction attempts do not starve the downstream PDR probe. For
            // Dillig-style multiplicative counters, Kind needs the older 3s
            // window to reach the k-inductive proof before PDR enters a long
            // frame-relative invariant search.
            let kind_budget_nominal = self.simple_loop_kind_budget_nominal(features);
            // Scaled with the global budget (#phase0c): long competition
            // runs let Kind reach deeper k on slow-check instances.
            let kind_budget =
                self.scaled_probe_budget(deadline, kind_budget_nominal, 8, Duration::from_mins(1));
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Simple loop direct Kind attempt (budget {:.1}s)",
                    kind_budget.as_secs_f64()
                );
            }
            if let Some(result) = self.try_kind(kind_budget) {
                // Kind Safe results passed original-clause validation inside
                // `try_kind`. Kind Unsafe results carry counterexample traces
                // that finalize_verified_result validates independently.
                let evidence = if matches!(result, PortfolioResult::Unsafe(_)) {
                    ValidationEvidence::CounterexampleVerification
                } else {
                    ValidationEvidence::FullVerification
                };
                if self.config.verbose {
                    safe_eprintln!("Adaptive: Simple loop direct Kind solved the problem");
                }
                return (result, evidence);
            }
            if self.config.verbose {
                safe_eprintln!("Adaptive: Simple loop direct Kind returned Unknown");
            }
        } else if self.config.verbose {
            tracing::info!(
                "Adaptive: Skipping K-Induction for array problem (bit-blasting blowup)"
            );
        }

        // #11 QUAL-MINE: conjunctive-Houdini prepass for single-predicate BV
        // problems (vmt shape), fed by the mined qualifier vocabulary. Placed
        // AFTER the cheap unsafe routes above (front BMC probe upstream,
        // deterministic BV transition, Kind) so already-solved BV unsafes
        // keep their fast path; the sat-side vmt instances this targets are
        // not solved by those stages and reach here within a few seconds.
        // Sound: the prepass validates every survivor against the original
        // clauses and fails closed to None.
        if self.problem.has_bv_sorts() && !features.uses_arrays && !features.uses_datatypes {
            if let Some(result) = self.try_houdini_conjunctive_prepass(features, deadline) {
                return result;
            }
        }

        if self.config.verbose {
            safe_eprintln!("Adaptive: Using simple loop strategy (TPA probe, PDR fallback)");
        }

        // Use deadline-based remaining budget (#7932). Previous code used
        // `self.config.time_budget.saturating_sub(strategy_start.elapsed())`
        // which didn't account for time spent before this function (classification,
        // algebraic prepass, etc.), causing budget overruns that starve downstream
        // fallback solvers (e.g., Z3 Spacer in model-checker-consumer's auto mode).
        let unbounded_budget = deadline.is_none();
        let remaining_budget = self
            .remaining_budget(deadline)
            .unwrap_or(Duration::from_secs(25));
        if !unbounded_budget && remaining_budget.is_zero() {
            return (
                PortfolioResult::Unknown,
                ValidationEvidence::FullVerification,
            );
        }

        // Stage 1.25 (removed): the focused BMC probe now runs FIRST in the
        // SimpleLoop strategy arm (try_simple_loop_bmc_probe in
        // adaptive_engines.rs), before the LIA/Farkas route and Kind, so
        // shallow counterexamples no longer wait behind invariant routes.

        // Stage 1.5: Focused production-PDR probe for non-BV simple loops.
        //
        // Some single-predicate loops regress after KIND soundness hardening:
        // KIND spends its budget on rejected induction candidates, while a
        // direct production PDR run can still prove safety quickly
        // (dillig32-style pattern). Give PDR a short solo window before the
        // wider parallel portfolio so it can return a verified result without
        // competing with less-matched engines.
        // #chc25-lever-5: BV single-predicate transition systems (vmt-chc
        // shape) now get the same solo window — Lane C's BV-native PDR
        // (bv_generalization + bounds_bv discovery) never left startup while
        // racing four CPU-contended lanes, yet it is the engine best matched
        // to this shape. Gated to compact systems (≤60 clauses) so huge
        // bit-blasts (ssh) don't eat the window; the same validation gates
        // guard the verdict.
        let direct_pdr_candidate = features.is_single_predicate
            && !features.uses_arrays
            && !features.uses_real
            && (!self.problem.has_bv_sorts() || self.problem.clauses().len() <= 60);
        if direct_pdr_candidate {
            // #8856: Increased from 6s to 8s. Budget freed by reducing
            // Kind (3s→1.5s) and BMC (2s→1.5s) probes goes to PDR which
            // handles the majority of SAT invariant discovery.
            // Scaled with the global budget (#phase0c): competition runs
            // (1800s) give the solo PDR window up to 120s.
            let pdr_probe_budget = self.scaled_probe_budget(
                deadline,
                Duration::from_secs(8),
                15,
                Duration::from_mins(2),
            );
            if !pdr_probe_budget.is_zero() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: Simple loop production PDR probe (budget {:.1}s)",
                        pdr_probe_budget.as_secs_f64()
                    );
                }
                // #8288: For DT problems, run PDR on the DT-flattened problem
                // so PDR sees scalar fields instead of constructor/selector ops.
                // The DT-aware PDR (with MBP) can handle DTs but struggles to
                // discover field-relationship invariants like fst(p) = snd(p).
                // After flattening, this becomes p_fst = p_snd — a trivial equality.
                if self.problem.has_datatype_sorts() {
                    let dt_pipeline = TransformationPipeline::new()
                        .with(DtFlattener::new().with_verbose(self.config.verbose));
                    let dt_result = dt_pipeline.transform(self.problem.clone());
                    let pdr_config =
                        PdrConfig::production(self.config.verbose).with_tla_trace_from_env();
                    if let Some((pdr_result, evidence)) = try_budgeted_pdr_on_problem(
                        self,
                        &dt_result.problem,
                        pdr_config,
                        pdr_probe_budget,
                    ) {
                        let transform_memory = dt_result.transform_memory();
                        // Back-translate the result to the original problem's DT vocabulary.
                        match pdr_result {
                            PortfolioResult::Safe(model) => {
                                let orig_model =
                                    dt_result.back_translator.translate_validity(model);
                                let validation_budget =
                                    pdr_probe_budget.min(Duration::from_millis(1500));
                                if self.validate_translated_safe_model_on_original(
                                    &orig_model,
                                    validation_budget,
                                ) {
                                    return (PortfolioResult::Safe(orig_model), evidence);
                                }
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "Adaptive: DT-flattened PDR Safe failed original CHC validation"
                                    );
                                }
                                return (
                                    PortfolioResult::Unknown,
                                    ValidationEvidence::FullVerification,
                                );
                            }
                            PortfolioResult::Unsafe(cex) => {
                                if !transform_memory.unsafe_backtranslation_complete() {
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "Adaptive: DT-flattened PDR Unsafe rejected before promotion; {}",
                                            transform_memory.diagnostic_summary()
                                        );
                                    }
                                    return (
                                        PortfolioResult::Unknown,
                                        ValidationEvidence::FullVerification,
                                    );
                                }
                                let orig_cex = dt_result.back_translator.translate_invalidity(cex);
                                let validation_budget =
                                    pdr_probe_budget.min(Duration::from_secs(3));
                                if self.validate_original_counterexample_with_budget(
                                    &orig_cex,
                                    validation_budget,
                                ) {
                                    return (
                                        PortfolioResult::Unsafe(orig_cex),
                                        ValidationEvidence::CounterexampleVerification,
                                    );
                                }
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "Adaptive: DT-flattened PDR Unsafe failed original CHC validation"
                                    );
                                }
                                return (
                                    PortfolioResult::Unknown,
                                    ValidationEvidence::FullVerification,
                                );
                            }
                            PortfolioResult::Unknown | PortfolioResult::NotApplicable => {}
                        }
                    }
                } else {
                    let pdr_config =
                        PdrConfig::production(self.config.verbose).with_tla_trace_from_env();
                    if let Some(result) = try_budgeted_pdr(self, pdr_config, pdr_probe_budget) {
                        return result;
                    }
                }
            }
        }

        let remaining_budget = self
            .remaining_budget(deadline)
            .unwrap_or(Duration::from_secs(25));
        if !unbounded_budget && remaining_budget.is_zero() {
            return unknown_accepted_result();
        }

        // Stage 2: Run all engines in parallel.
        let full_budget = if unbounded_budget {
            Duration::from_secs(25)
        } else {
            remaining_budget
        };

        if features.uses_arrays {
            // #8739: For BV-indexed array problems, the array-safe lane alone is
            // insufficient. Its preprocessing (BvToBoolBitBlaster + BvToIntAbstractor)
            // destroys the select-index correspondence: the BV index becomes a bit
            // pattern over 32 Bool args and Array(BV,BV) gets abstracted to
            // Array(Int,Int). Post-preprocessing, `try_scalarize_const_array_selects`
            // sees only constant selects, strips the array from the predicate
            // signature, and PDR runs with `uses_arrays=false` — ROW expansion has
            // nothing to operate on.
            //
            // Race the BV-native Lane C (which preserves Array(BV,BV) via
            // PreprocessSummary::build_bv_native) in parallel with the array-safe
            // lane. First definitive result wins. For LIA-indexed arrays,
            // has_bv_sorts() is false and we fall through to the original path.
            if self.problem.has_bv_sorts() {
                if let Some(result) = self.try_bv_array_counter_cell_safe_route(full_budget) {
                    return result;
                }
                if let Some(result) = self.try_bv_array_preserved_cell_safe_route(full_budget) {
                    return result;
                }
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: BV+array simple loop — racing BV-native Lane C + array-safe PDR (#8739)"
                    );
                }
                return (
                    self.solve_bv_array_portfolio(full_budget),
                    ValidationEvidence::FullVerification,
                );
            }
            if self.config.verbose {
                safe_eprintln!(
                    "Adaptive: Using array-safe simple loop portfolio (PDR + negated-eq PDR + BMC; array BMC restored after #8745/#8822)"
                );
            }
            let mut config = self.simple_loop_array_portfolio_config(full_budget);
            self.apply_original_problem_engine_selection(&mut config);
            return (
                self.run_portfolio(config),
                ValidationEvidence::FullVerification,
            );
        }

        // #5877: For BV simple loops, run dual-lane portfolio — BvToBool (Boolean
        // lane) and BvToInt (LIA lane) race in parallel. BvToBool expands BV args
        // to individual Bool bits, creating a large state space (100-1000+ args) that
        // PDR/PDKIND can struggle with. BvToInt converts BV to integer arithmetic,
        // preserving the original variable count but introducing ITE-heavy modular
        // encoding. Neither encoding dominates: BvToBool solves problems needing
        // bit-level reasoning, BvToInt solves problems with arithmetic invariants.
        // Running both in parallel maximizes coverage.
        //
        // #5877/#7930/#8419: BV dual-lane for BV problems.
        //
        // For DT+BV problems: DT-flatten first to eliminate DT sorts, then route
        // the flattened problem (now pure BV) through the BV dual-lane. The old
        // approach (#7930) skipped the dual-lane entirely because BvToBool/BvToInt
        // cannot handle DT constructor/selector/tester operations. But after DT
        // flattening, there are no DT operations left — BV fields become top-level
        // BV arguments. This enables BV-native PDR to operate on compact BV
        // variables instead of 8×-expanded boolean variables from bit-blasting.
        //
        // This removes the need for large amounts of consumer-side DT+BV
        // workaround code because the solver can now directly handle DT-wrapped
        // BV fields in CHC invariants.
        if self.problem.has_bv_sorts() {
            if self.problem.has_datatype_sorts() {
                if self.config.verbose {
                    safe_eprintln!(
                        "Adaptive: DT+BV simple loop — DT-flatten then BV dual-lane (#8419)"
                    );
                }
                // DT-flatten: removes DT sorts, BV fields become top-level args.
                let dt_pipeline = TransformationPipeline::new()
                    .with(DtFlattener::new().with_verbose(self.config.verbose));
                let dt_result = dt_pipeline.transform(self.problem.clone());

                // Create a new adaptive portfolio with the flattened problem.
                // After DT flattening, the problem is pure BV and can use all
                // BV solving lanes (BvToBool, BvToInt, BV-native, relaxed).
                let flattened_adaptive = Self::new(dt_result.problem.clone(), self.config.clone());
                let bv_result = flattened_adaptive.solve_bv_dual_lane(full_budget);
                let transform_memory = dt_result.transform_memory();

                // Back-translate results to the original DT vocabulary.
                let translated = match bv_result {
                    PortfolioResult::Safe(model) => {
                        let flattened_model = model.clone();
                        let orig_model = dt_result.back_translator.translate_validity(model);
                        let validation_budget = full_budget.min(Duration::from_millis(1500));
                        if self.validate_translated_safe_model_on_original(
                            &orig_model,
                            validation_budget,
                        ) || {
                            let mut verifier = PdrSolver::new(
                                dt_result.problem.clone(),
                                PdrConfig {
                                    verbose: self.config.verbose,
                                    strict_proofs: true,
                                    solve_timeout: Some(validation_budget),
                                    disable_array_scalarization: true,
                                    preserve_original_clauses: true,
                                    ..PdrConfig::default()
                                },
                            );
                            verifier.verify_model_with_budget(&flattened_model, validation_budget)
                        } {
                            PortfolioResult::Safe(orig_model)
                        } else {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "Adaptive: DT+BV translated Safe failed original CHC validation"
                                );
                            }
                            PortfolioResult::Unknown
                        }
                    }
                    PortfolioResult::Unsafe(cex) => {
                        if !transform_memory.unsafe_backtranslation_complete() {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "Adaptive: DT+BV translated Unsafe rejected before promotion; {}",
                                    transform_memory.diagnostic_summary()
                                );
                            }
                            return (
                                PortfolioResult::Unknown,
                                ValidationEvidence::FullVerification,
                            );
                        }
                        let orig_cex = dt_result.back_translator.translate_invalidity(cex);
                        let validation_budget = full_budget.min(Duration::from_secs(3));
                        if validation_budget.is_zero() {
                            PortfolioResult::Unknown
                        } else {
                            let mut verifier = PdrSolver::new(
                                self.problem.clone(),
                                PdrConfig {
                                    verbose: self.config.verbose,
                                    solve_timeout: Some(validation_budget),
                                    disable_array_scalarization: true,
                                    ..PdrConfig::default()
                                },
                            );
                            verifier.set_validation_deadline(validation_budget);
                            match verifier
                                .try_verify_counterexample(&orig_cex)
                                .unwrap_or(crate::CexVerificationResult::Unknown)
                            {
                                crate::CexVerificationResult::Valid => {
                                    PortfolioResult::Unsafe(orig_cex)
                                }
                                crate::CexVerificationResult::Spurious
                                | crate::CexVerificationResult::Unknown => {
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "Adaptive: DT+BV translated Unsafe failed original CHC validation"
                                        );
                                    }
                                    PortfolioResult::Unknown
                                }
                            }
                        }
                    }
                    other => other,
                };
                return (translated, ValidationEvidence::FullVerification);
            }
            let result = self.solve_bv_dual_lane(full_budget);
            return (result, ValidationEvidence::FullVerification);
        }

        let mut config = self.simple_loop_portfolio_config(full_budget);
        self.apply_original_problem_engine_selection(&mut config);
        (
            self.run_portfolio(config),
            ValidationEvidence::FullVerification,
        )
    }

    pub(crate) fn use_bv_native_direct_route(&self, features: &ProblemFeatures) -> bool {
        self.problem.has_bv_sorts()
            && features.class == crate::classifier::ProblemClass::SimpleLoop
            && features.is_single_predicate
            && features.num_transitions == 1
            && !features.uses_arrays
            && !features.uses_real
    }

    /// Build the portfolio config for simple loop problems.
    pub(super) fn simple_loop_portfolio_config(&self, budget: Duration) -> PortfolioConfig {
        let pdr_config_val = PdrConfig {
            verbose: self.config.verbose,
            use_lemma_hints: true,
            ..PdrConfig::default()
        }
        .with_tla_trace_from_env();

        let mut config = PortfolioConfig {
            external_cancellation: Some(self.cancellation_token.clone()),
            engines: vec![
                EngineConfig::Tpa(TpaConfig {
                    base: ChcEngineConfig {
                        verbose: self.config.verbose,
                        ..ChcEngineConfig::default()
                    },
                    max_power: 20,
                    timeout_per_power: Duration::from_secs(2),
                    verbose_level: u8::from(self.config.verbose),
                }),
                EngineConfig::Pdkind(PdkindConfig {
                    base: ChcEngineConfig {
                        verbose: self.config.verbose,
                        ..ChcEngineConfig::default()
                    },
                    ..PdkindConfig::default()
                }),
                // IMC: interpolation-based model checking — golem's workhorse
                // for the lustre-sat family (closes 1-inductive monitor
                // properties in a few interpolation rounds). Previously absent
                // from this roster, so it was never scheduled on exactly the
                // family it wins (gap-attribution wf_308f0314). Its 30s/50-k
                // self-caps are lifted to the injected lane budget; acceptance
                // is unchanged (every Safe answer still replays against the
                // ORIGINAL clauses in portfolio validation).
                EngineConfig::Imc(ImcConfig {
                    base: ChcEngineConfig {
                        verbose: self.config.verbose,
                        ..ChcEngineConfig::default()
                    },
                    total_timeout: budget,
                    ..ImcConfig::default()
                }),
                // TRL adds loop summarization via transitive relation learning
                // with n-retention (Golem TRL.cc:296-351). Safety proving only.
                EngineConfig::Trl(TrlConfig {
                    base: ChcEngineConfig {
                        verbose: self.config.verbose,
                        ..ChcEngineConfig::default()
                    },
                    ..TrlConfig::default()
                }),
                EngineConfig::Pdr(pdr_config_val),
                // inc-12: spacer-mode PDR lane for the SimpleLoop arm (the
                // lustre-class family). No startup discovery, interpolant-as-
                // lemma blocking, executor-first per-pob checks; runs on the
                // same collapsed portfolio problem. The default PDR engine
                // above is unchanged.
                EngineConfig::Pdr(
                    PdrConfig {
                        verbose: self.config.verbose,
                        use_lemma_hints: true,
                        ..PdrConfig::portfolio_spacer_variant()
                    }
                    .with_tla_trace_from_env(),
                ),
                EngineConfig::Cegar(CegarConfig {
                    base: ChcEngineConfig {
                        verbose: self.config.verbose,
                        ..ChcEngineConfig::default()
                    },
                    ..CegarConfig::default()
                }),
                // BMC for bounded counterexample discovery (#5383).
                // TRL subsumes BMC's safety proving but NOT its UNSAT capability.
                EngineConfig::Bmc(BmcConfig::default()),
            ],
            parallel: true,
            timeout: None,
            parallel_timeout: Some(budget),
            verbose: self.config.verbose,

            enable_preprocessing: true,
            engine_budgets: ay_core::kani_compat::DetHashMap::default(),
            memory_budget: self.config.memory_budget,
            strict_proofs: self.config.strict_proofs,
        };
        self.apply_staged_probe_budget_defaults(&mut config, StagedProbeBudgetProfile::BmcOnly);
        config
    }

    /// Build the portfolio config for array-containing simple loops.
    ///
    /// Arrays stay on the original problem and avoid the simple-loop engines
    /// whose transition-system encodings assume scalar Int/Bool state.
    ///
    /// BMC is included again. It was excluded during #8734 while the
    /// underlying SMT array-model soundness bug (#8745) was still open, but
    /// current HEAD includes that SMT fix and #8822 removed the temporary
    /// BMC-side downgrade. Re-enable BMC here so array simple loops regain
    /// bounded counterexample search in the adaptive portfolio.
    pub(super) fn simple_loop_array_portfolio_config(&self, budget: Duration) -> PortfolioConfig {
        let pdr_config = PdrConfig {
            verbose: self.config.verbose,
            use_lemma_hints: true,
            ..PdrConfig::default()
        }
        .with_tla_trace_from_env();

        let mut config = PortfolioConfig {
            external_cancellation: Some(self.cancellation_token.clone()),
            engines: vec![
                EngineConfig::Pdr(pdr_config.clone()),
                EngineConfig::Pdr(PdrConfig {
                    use_negated_equality_splits: true,
                    ..pdr_config
                }),
                EngineConfig::Bmc(BmcConfig::default()),
                // Array routing (#C-LAWI): this single-loop ARRAY roster had no
                // interpolation engine at all. LAWI (lazy abstraction with
                // interpolants, McMillan IMPACT) is AY's purpose-built array
                // engine, and IMC is interpolation-based MC — both previously
                // dead code for Int-array problems (only the SimpleLoop&&uses_real
                // selector path constructed LAWI). Additive + self-validating
                // (Safe replayed per-rule on the original; Unsafe by
                // counterexample), preserving 0-wrong.
                EngineConfig::Lawi(crate::lawi::LawiConfig::default()),
                EngineConfig::Imc(ImcConfig::default()),
            ],
            parallel: true,
            timeout: None,
            parallel_timeout: Some(budget),
            verbose: self.config.verbose,

            enable_preprocessing: true,
            engine_budgets: ay_core::kani_compat::DetHashMap::default(),
            memory_budget: self.config.memory_budget,
            strict_proofs: self.config.strict_proofs,
        };
        self.apply_staged_probe_budget_defaults(&mut config, StagedProbeBudgetProfile::BmcOnly);
        config
    }

    /// Build the portfolio config for pure-Boolean simple loop problems (#5877).
    ///
    /// After BvToBool preprocessing, the predicate state space is all Bool+Int.
    /// Interpolation-heavy engines (CEGAR, DAR, IMC, TRL, TPA) are mismatched
    /// for 100+ shared Boolean variables. Use PDKIND for safety proving and
    /// BMC for counterexample discovery. PDR is also included as it uses
    /// SMT-level reasoning that works with Bool constraints.
    pub(super) fn boolean_simple_loop_portfolio_config(
        &self,
        budget: Duration,
        bv_bit_groups: &[(usize, u32)],
    ) -> PortfolioConfig {
        let pdr_config_val = PdrConfig {
            verbose: self.config.verbose,
            use_lemma_hints: true,
            bv_bit_groups: bv_bit_groups.to_vec(),
            ..PdrConfig::default()
        }
        .with_tla_trace_from_env();

        let mut config = PortfolioConfig {
            external_cancellation: Some(self.cancellation_token.clone()),
            engines: vec![
                EngineConfig::Pdkind(PdkindConfig {
                    base: ChcEngineConfig {
                        verbose: self.config.verbose,
                        ..ChcEngineConfig::default()
                    },
                    bv_to_bool_applied: true,
                    // BvToBool expands BV(32) to 160+ Boolean state vars. The
                    // k-transition formula is huge, so the default 5s timeout
                    // causes immediate Unknown from k-induction. Use 30s and
                    // FreshOnly to avoid BV state corruption (#5877, #8161).
                    per_obligation_timeout_secs: 30,
                    incremental_mode: crate::pdkind::IncrementalMode::FreshOnly(
                        "BitVector state unsupported".to_string(),
                    ),
                    ..PdkindConfig::default()
                }),
                EngineConfig::Pdr(pdr_config_val),
                EngineConfig::Bmc(BmcConfig::default()),
            ],
            parallel: true,
            timeout: None,
            parallel_timeout: Some(budget),
            verbose: self.config.verbose,

            // Preprocessing already done via PreprocessSummary — do not re-run.
            enable_preprocessing: false,
            engine_budgets: ay_core::kani_compat::DetHashMap::default(),
            memory_budget: self.config.memory_budget,
            strict_proofs: self.config.strict_proofs,
        };
        self.apply_staged_probe_budget_defaults(&mut config, StagedProbeBudgetProfile::CallerOnly);
        config
    }

    /// Build the portfolio config for BV-native PDR solving (#5877 Wave 3).
    ///
    /// Runs PDR + BMC on the original BV-sorted problem with no BV transforms.
    /// PDR operates on BV-sorted predicates directly, delegating BV constraints
    /// to the SMT solver's BV theory. This matches Z3 Spacer's default behavior
    /// where `xform.bit_blast = false`.
    ///
    /// PDR is the primary engine for both SAT-finding (backward reachability with
    /// BV-native cubes) and UNSAT-proving (BV-level inductive invariants). BMC
    /// provides bounded counterexample discovery. Other engines (PDKIND, TPA,
    /// CEGAR, TRL) are excluded: PDKIND has a soundness guard for arrays
    /// (#8675) that short-circuits to Unknown; interpolation-heavy engines
    /// assume scalar Int/Bool state.
    pub(super) fn bv_native_portfolio_config(&self, budget: Duration) -> PortfolioConfig {
        let pdr_config_val = PdrConfig {
            verbose: self.config.verbose,
            use_must_summaries: true,
            use_lemma_hints: true,
            max_frames: 50,
            ..PdrConfig::default()
        }
        .with_tla_trace_from_env();

        // #5877: BV bitblasting at deep BMC depths produces exponentially
        // larger formulas. On nested4 (9-branch BV32 transition), depths 0-5
        // complete in ~55ms total but depth 6 hangs for >25s because the
        // Tseitin+bitblast encoding itself is intractable (no mid-encoding
        // interrupt). The per_depth_timeout pre-encoding checks in
        // incremental.rs bail before encoding starts when cumulative depth
        // time exceeds the per-depth timeout — that guard is what makes depth
        // safe, so depth and per-depth budget SCALE with the lane budget
        // instead of the old hard 15/3 s caps that left competition budgets
        // unused while vmt-chc counterexamples sit at depths 16-40
        // (#chc25-lever-4). 15/3 s remain the floors for short probes.
        let scaled_depth = if budget >= Duration::from_mins(10) {
            64
        } else if budget >= Duration::from_mins(2) {
            40
        } else if budget >= Duration::from_secs(45) {
            24
        } else {
            15
        };
        let bmc_config = BmcConfig {
            max_depth: scaled_depth,
            per_depth_timeout: Some(
                (budget / 40)
                    .max(Duration::from_secs(3))
                    .min(Duration::from_secs(15)),
            ),
            ..BmcConfig::default()
        };

        let mut config = PortfolioConfig {
            external_cancellation: Some(self.cancellation_token.clone()),
            engines: vec![
                EngineConfig::Pdr(pdr_config_val),
                EngineConfig::Bmc(bmc_config),
            ],
            parallel: true,
            timeout: None,
            parallel_timeout: Some(budget),
            verbose: self.config.verbose,

            // Preprocessing already done via PreprocessSummary::build_bv_native.
            enable_preprocessing: false,
            engine_budgets: ay_core::kani_compat::DetHashMap::default(),
            memory_budget: self.config.memory_budget,
            strict_proofs: self.config.strict_proofs,
        };
        self.apply_staged_probe_budget_defaults(&mut config, StagedProbeBudgetProfile::CallerOnly);
        config
    }
}

#[cfg(test)]
mod tests {
    use crate::{AdaptiveConfig, ChcParser, PortfolioResult};
    use std::time::Duration;

    #[test]
    fn bv_array_counter_cell_candidate_recognizes_unsplit_store_loop() {
        let input = include_str!("../../../benchmarks/chc/test_array_pred.smt2");
        let problem = ChcParser::parse(input).expect("benchmark should parse");
        let candidate = super::bv_array_counter_cell_candidate(&problem)
            .expect("counter-cell pattern should be recognized");

        assert_eq!(candidate.array_arg_index, 0);
        assert_eq!(candidate.counter_arg_index, 1);
        assert_eq!(candidate.init_value, 42);
        assert_eq!(candidate.value_width, 32);
        assert_eq!(candidate.counter_width, 32);
    }

    #[test]
    fn bv_array_counter_cell_safe_route_validates_unsplit_store_loop() {
        let input = include_str!("../../../benchmarks/chc/test_array_pred.smt2");
        let problem = ChcParser::parse(input).expect("benchmark should parse");
        let portfolio = super::AdaptivePortfolio::new(problem, AdaptiveConfig::test_default());

        let Some((result, _)) =
            portfolio.try_bv_array_counter_cell_safe_route(Duration::from_secs(5))
        else {
            panic!("counter-cell route should validate");
        };
        assert!(matches!(result, PortfolioResult::Safe(_)));
    }

    #[test]
    fn direct_pdr_probe_merges_stats_for_cli_observability() {
        let source = include_str!("adaptive_bv_strategy.rs");
        let direct_probe = source
            .split("fn try_budgeted_pdr(")
            .nth(1)
            .and_then(|rest| rest.split("/// Run PDR on a specific problem").next())
            .expect("direct PDR helper should be present");

        assert!(
            direct_probe.contains("solver.solve_with_stats()"),
            "direct PDR probe must keep solver stats instead of calling solve()"
        );
        assert!(
            direct_probe.contains("portfolio.accumulate_stats(&result_with_stats.stats)"),
            "direct PDR probe must merge PDR stats into AdaptivePortfolio stats"
        );
    }

    #[test]
    fn dt_flattened_unsafe_requires_original_replay_9691() {
        let source = include_str!("adaptive_bv_strategy.rs");
        let dt_flattened_unsafe = source
            .split("PortfolioResult::Unsafe(cex) => {")
            .nth(1)
            .and_then(|rest| {
                rest.split("PortfolioResult::Unknown | PortfolioResult::NotApplicable")
                    .next()
            })
            .expect("DT-flattened PDR Unsafe arm should be present");

        assert!(
            dt_flattened_unsafe.contains("unsafe_backtranslation_complete"),
            "DT-flattened Unsafe must first require complete transform-memory backtranslation"
        );
        assert!(
            dt_flattened_unsafe.contains("validate_original_counterexample_with_budget"),
            "DT-flattened Unsafe must replay the translated witness on the original CHC before promotion"
        );
        assert!(
            dt_flattened_unsafe.contains("ValidationEvidence::CounterexampleVerification"),
            "accepted DT-flattened Unsafe must carry counterexample-verification evidence"
        );
    }
}
