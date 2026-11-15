// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground derivations read off an engine's own concrete linear trace.
//!
//! Transition-system engines (LAWI, TPA) decide Unsafe from a SAT model of an
//! unrolled path. That model IS the counterexample: a concrete state at every
//! step plus the values of each fired clause's locals. Engines used to drop
//! it and report a skeleton, and the portfolio then re-solved the unrolling
//! from scratch to certify the answer — on equality-heavy LRA systems the
//! re-solve never finishes, so correct Unsafe answers were discarded
//! (the development design notes, item 4).
//!
//! This module turns such a trace into a [`GroundDerivation`] over the
//! engine's problem (fact → transition × n → query, each step one clause
//! instance under a total concrete assignment). The trace only proposes
//! values: the result is returned only when [`super::validate_ground_derivation`]
//! accepts it, and every consumer re-validates it on its own clauses.
//!
//! # How values are chosen
//!
//! The chain is built FORWARD. A step's body arguments are pinned to the
//! head values the previous step actually evaluated to (never to the model's
//! claim), so premise links hold by construction. The engine's state at the
//! step's own head and its local values are hints: first tried as fixed pins
//! (this also attributes the step to the clause the engine fired), then only
//! as completion fallbacks, with ground unit propagation and the bounded
//! per-clause witness solve ([`super::complete`]) filling what they leave.

use super::complete::complete_env_for_clause_with_fallback;
use super::{eval_ground, validate_ground_derivation, GroundDerivation, GroundDerivationStep};
use crate::clause::{ClauseHead, HornClause};
use crate::smt::SmtValue;
use crate::transition_system::TransitionSystem;
use crate::{CancellationToken, ChcExpr, ChcProblem, ChcSort, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;
use num_rational::BigRational;
use std::time::Duration;

mod counterexample;
mod ts_model;
pub(crate) use counterexample::{counterexample_from_linear_trace, engine_trace_counterexample};
pub(crate) use ts_model::{ts_locals_with_suffix, ts_state_at};

/// Wall-clock allowance for turning one engine trace into ground evidence.
/// Building is pure evaluation plus, at worst, small bounded per-clause
/// witness solves; the cap only bounds pathological traces.
const TRACE_WITNESS_BUDGET: Duration = Duration::from_secs(5);

/// Deadline for one trace-to-evidence build: [`TRACE_WITNESS_BUDGET`] from
/// now, never past the thread's solve deadline.
pub(crate) fn trace_witness_deadline() -> Instant {
    let local = Instant::now() + TRACE_WITNESS_BUDGET;
    crate::smt::current_thread_solve_deadline().map_or(local, |solve| solve.min(local))
}

/// What the engine knows about one edge of its path.
#[derive(Debug, Clone, Default)]
pub(crate) struct TraceEdgeHint {
    /// The clause the engine fired on this edge, when it knows it.
    pub(crate) clause: Option<usize>,
    /// Model values for `clause`'s variables, keyed by that clause's own
    /// variable names. Ignored for any other clause.
    pub(crate) clause_values: FxHashMap<String, SmtValue>,
    /// Model values keyed by transition-system local names
    /// (`{TsClauseDisjunct::local_prefix}{clause variable}`, version suffix
    /// stripped). Valid for whichever clause is tried on this edge.
    pub(crate) ts_locals: FxHashMap<String, SmtValue>,
    /// Model values keyed by the fired clause's own variable names when the
    /// engine does not know which clause fired (an encoding that keeps clause
    /// locals unprefixed). Hints for whichever clause is tried on this edge.
    pub(crate) clause_locals: FxHashMap<String, SmtValue>,
}

/// A concrete counterexample path of a single-predicate linear system.
#[derive(Debug, Clone)]
pub(crate) struct LinearTrace {
    /// The system's (only) predicate.
    pub(crate) predicate: PredicateId,
    /// `states[j][i]`: the engine's value of argument `i` after `j`
    /// transitions (`None` when its model is silent).
    pub(crate) states: Vec<Vec<Option<SmtValue>>>,
    /// `states.len() + 1` edges: the fact entering `states[0]`, the
    /// transition into each `states[j]` (`j >= 1`), and the query on the last
    /// state. A short list is padded with empty hints.
    pub(crate) edges: Vec<TraceEdgeHint>,
}

/// A value of `sort` equal to `value`, or `None` when the two cannot agree.
fn coerce_to_sort(value: &SmtValue, sort: &ChcSort) -> Option<SmtValue> {
    match (sort, value) {
        (ChcSort::Int, SmtValue::Int(_) | SmtValue::BigInt(_)) => Some(value.clone()),
        (ChcSort::Int, SmtValue::Real(r)) if r.is_integer() => {
            Some(SmtValue::int_from_bigint(r.to_integer()))
        }
        (ChcSort::Real, SmtValue::Real(_)) => Some(value.clone()),
        (ChcSort::Real, SmtValue::Int(i)) => Some(SmtValue::Real(BigRational::from_integer(
            num_bigint::BigInt::from(*i),
        ))),
        (ChcSort::Real, SmtValue::BigInt(i)) => Some(SmtValue::Real(BigRational::from_integer(
            i.as_ref().clone(),
        ))),
        (ChcSort::Bool, SmtValue::Bool(_)) => Some(value.clone()),
        (ChcSort::BitVec(w), SmtValue::BitVec(_, vw) | SmtValue::BigBitVec(_, vw)) if w == vw => {
            Some(value.clone())
        }
        (ChcSort::Int | ChcSort::Real | ChcSort::Bool | ChcSort::BitVec(_), _) => None,
        // Aggregates: the validator's sort check decides.
        _ => Some(value.clone()),
    }
}

fn values_equal(a: &SmtValue, b: &SmtValue) -> bool {
    crate::expr::evaluate::smt_values_equal(a, b) == Some(true)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Role {
    Fact,
    Transition,
    Query,
}

fn clause_role(clause: &HornClause, pred: PredicateId) -> Option<Role> {
    let body_is_pred = match clause.body.predicates.as_slice() {
        [] => false,
        [(p, _)] if *p == pred => true,
        _ => return None,
    };
    match (&clause.head, body_is_pred) {
        (ClauseHead::Predicate(p, _), false) if *p == pred => Some(Role::Fact),
        (ClauseHead::Predicate(p, _), true) if *p == pred => Some(Role::Transition),
        (ClauseHead::False, true) => Some(Role::Query),
        _ => None,
    }
}

/// Bind every bare-variable argument to its value; `false` on a conflict
/// (the same variable at two positions with different values) or a value
/// that does not fit the variable's sort.
fn pin_args(
    args: &[ChcExpr],
    values: &[Option<SmtValue>],
    env: &mut FxHashMap<String, SmtValue>,
) -> bool {
    for (arg, value) in args.iter().zip(values) {
        let (ChcExpr::Var(var), Some(value)) = (arg, value) else {
            continue;
        };
        let Some(value) = coerce_to_sort(value, &var.sort) else {
            return false;
        };
        match env.get(&var.name) {
            Some(existing) if !values_equal(existing, &value) => return false,
            Some(_) => {}
            None => {
                env.insert(var.name.clone(), value);
            }
        }
    }
    true
}

/// Evaluate `args` under `env`, each coerced to its declared sort.
fn eval_args(
    args: &[ChcExpr],
    sorts: &[ChcSort],
    env: &FxHashMap<String, SmtValue>,
) -> Option<Vec<SmtValue>> {
    if args.len() != sorts.len() {
        return None;
    }
    args.iter()
        .zip(sorts)
        .map(|(arg, sort)| coerce_to_sort(&eval_ground(arg, env)?, sort))
        .collect()
}

/// Record (ground-bt debug only) the first argument `eval_args` refuses.
fn log_unevaluable(
    args: &[ChcExpr],
    sorts: &[ChcSort],
    env: &FxHashMap<String, SmtValue>,
) -> &'static str {
    if super::ground_backtranslation_debug() {
        let refused = args
            .iter()
            .zip(sorts)
            .enumerate()
            .find_map(|(idx, (arg, sort))| {
                let value = eval_ground(arg, env);
                let fits = value
                    .as_ref()
                    .and_then(|v| coerce_to_sort(v, sort))
                    .is_some();
                (!fits).then(|| (idx, sort, value, arg))
            });
        if let Some((idx, sort, value, arg)) = refused {
            let unbound: Vec<String> = arg
                .vars()
                .into_iter()
                .filter(|var| !env.contains_key(&var.name))
                .map(|var| var.name)
                .collect();
            let text = arg.to_string();
            super::log_ground_translation_detail(format_args!(
                "linear-trace: head arg {idx} ({sort:?}) evaluates to {value:?}; unbound {unbound:?}; \
                 expr {}",
                text.chars().take(400).collect::<String>()
            ));
        }
    }
    "head args unevaluable"
}

/// Everything needed to try one clause on one edge.
struct EdgeAttempt<'a> {
    clause: &'a HornClause,
    arg_sorts: &'a [ChcSort],
    /// Definitive body state (the previous step's evaluated head).
    body_state: Option<&'a [SmtValue]>,
    /// The engine's claim for this step's head state.
    head_hint: Option<&'a [Option<SmtValue>]>,
    /// Model values for this clause's own variables.
    hints: FxHashMap<String, SmtValue>,
}

/// Fire one clause: a total environment satisfying the clause whose body
/// arguments equal `body_state`, and the head values it produces.
/// `Err` names the first check that failed (for the ground-bt debug log).
fn fire(
    attempt: &EdgeAttempt<'_>,
    strict: bool,
) -> Result<(FxHashMap<String, SmtValue>, Vec<SmtValue>), &'static str> {
    let clause = attempt.clause;
    let mut env = FxHashMap::default();
    if let Some((_, body_args)) = clause.body.predicates.first() {
        let state = attempt.body_state.ok_or("no body state")?;
        let as_options: Vec<Option<SmtValue>> = state.iter().cloned().map(Some).collect();
        if !pin_args(body_args, &as_options, &mut env) {
            return Err("body pins conflict");
        }
    }
    let mut fallback = attempt.hints.clone();
    if let (Some(head_hint), ClauseHead::Predicate(_, head_args)) =
        (attempt.head_hint, &clause.head)
    {
        if strict {
            if !pin_args(head_args, head_hint, &mut env) {
                return Err("head pins conflict");
            }
        } else {
            for (arg, value) in head_args.iter().zip(head_hint) {
                if let (ChcExpr::Var(var), Some(value)) = (arg, value) {
                    if let Some(value) = coerce_to_sort(value, &var.sort) {
                        fallback.entry(var.name.clone()).or_insert(value);
                    }
                }
            }
        }
    }
    if strict {
        // Strict attempts also pin the engine's local values: this is the
        // exact instance the engine's model satisfied.
        for var in clause.vars() {
            if env.contains_key(&var.name) {
                continue;
            }
            if let Some(value) = fallback
                .get(&var.name)
                .and_then(|v| coerce_to_sort(v, &var.sort))
            {
                env.insert(var.name.clone(), value);
            }
        }
    }
    if !complete_env_for_clause_with_fallback(clause, &mut env, &fallback) {
        return Err("completion failed");
    }
    // Project onto the clause's own variables, each value in its declared
    // sort (a solver may report an integral Real as an Int).
    let mut projected = FxHashMap::default();
    for var in clause.vars() {
        let value = env
            .get(&var.name)
            .and_then(|v| coerce_to_sort(v, &var.sort));
        projected.insert(var.name, value.ok_or("variable left unassigned")?);
    }
    let env = projected;
    if let Some(constraint) = &clause.body.constraint {
        if !matches!(eval_ground(constraint, &env), Some(SmtValue::Bool(true))) {
            return Err("constraint not true");
        }
    }
    if let (Some((_, body_args)), Some(state)) =
        (clause.body.predicates.first(), attempt.body_state)
    {
        let values =
            eval_args(body_args, attempt.arg_sorts, &env).ok_or("body args unevaluable")?;
        if !values.iter().zip(state).all(|(a, b)| values_equal(a, b)) {
            return Err("body args differ from the state");
        }
    }
    let head = match &clause.head {
        ClauseHead::Predicate(_, head_args) => eval_args(head_args, attempt.arg_sorts, &env)
            .ok_or_else(|| log_unevaluable(head_args, attempt.arg_sorts, &env))?,
        ClauseHead::False => Vec::new(),
    };
    if strict {
        if let Some(head_hint) = attempt.head_hint {
            let agrees = head
                .iter()
                .zip(head_hint)
                .all(|(value, hint)| hint.as_ref().map_or(true, |hint| values_equal(value, hint)));
            if !agrees {
                return Err("head differs from the engine's state");
            }
        }
    }
    Ok((env, head))
}

/// The clauses a linear trace is replayed against, classified once.
struct TraceClauses<'a> {
    clauses: &'a [HornClause],
    arg_sorts: &'a [ChcSort],
    roles: Vec<Option<Role>>,
    /// Local-name prefix the transition-system extraction gives each clause.
    local_prefixes: FxHashMap<usize, String>,
}

impl<'a> TraceClauses<'a> {
    fn new(problem: &'a ChcProblem, pred: PredicateId, arg_sorts: &'a [ChcSort]) -> Self {
        let local_prefixes = TransitionSystem::clause_disjuncts(problem)
            .map(|disjuncts| {
                disjuncts
                    .facts
                    .into_iter()
                    .chain(disjuncts.transitions)
                    .chain(disjuncts.queries)
                    .map(|d| (d.clause_idx, d.local_prefix))
                    .collect()
            })
            .unwrap_or_default();
        let clauses = problem.clauses();
        Self {
            clauses,
            arg_sorts,
            roles: clauses.iter().map(|c| clause_role(c, pred)).collect(),
            local_prefixes,
        }
    }

    /// The hints `edge` gives for the variables of clause `clause_idx`.
    fn clause_hints(&self, clause_idx: usize, edge: &TraceEdgeHint) -> FxHashMap<String, SmtValue> {
        let mut hints = FxHashMap::default();
        if Some(clause_idx) == edge.clause {
            hints.extend(
                edge.clause_values
                    .iter()
                    .map(|(k, v)| (k.clone(), v.clone())),
            );
        }
        let prefix = self.local_prefixes.get(&clause_idx);
        for var in self.clauses[clause_idx].vars() {
            let value = prefix
                .and_then(|prefix| edge.ts_locals.get(&format!("{prefix}{}", var.name)))
                .or_else(|| edge.clause_locals.get(&var.name));
            if let Some(value) = value {
                hints
                    .entry(var.name.clone())
                    .or_insert_with(|| value.clone());
            }
        }
        hints
    }

    /// Fire the first clause of `role` that instantiates this edge (the
    /// engine's own clause first, strict before relaxed): its index, total
    /// environment and head values. `None` when none fires or `stopped`.
    fn fire_edge(
        &self,
        role: Role,
        edge: &TraceEdgeHint,
        body_state: Option<&[SmtValue]>,
        head_hint: Option<&[Option<SmtValue>]>,
        stopped: &dyn Fn() -> bool,
    ) -> Option<(usize, FxHashMap<String, SmtValue>, Vec<SmtValue>)> {
        let has_role = |c: usize| self.roles.get(c).copied().flatten() == Some(role);
        let hinted = edge.clause.filter(|&c| has_role(c));
        let others = (0..self.clauses.len()).filter(|&c| Some(c) != hinted && has_role(c));
        let mut misses = Vec::new();
        for clause_idx in hinted.into_iter().chain(others) {
            let attempt = EdgeAttempt {
                clause: &self.clauses[clause_idx],
                arg_sorts: self.arg_sorts,
                body_state,
                head_hint,
                hints: self.clause_hints(clause_idx, edge),
            };
            for strict in [true, false] {
                if stopped() {
                    return None;
                }
                match fire(&attempt, strict) {
                    Ok((env, head)) => return Some((clause_idx, env, head)),
                    Err(miss) => misses.push((clause_idx, strict, miss)),
                }
            }
        }
        super::log_ground_translation_detail(format_args!(
            "linear-trace: no {role:?} clause fires (clause, strict, miss): {misses:?}"
        ));
        None
    }
}

/// Build and validate a ground derivation of `false` over `problem` from an
/// engine's linear trace.
///
/// Returns `None` whenever any step cannot be instantiated, the deadline or
/// cancellation fires, or the assembled derivation does not validate against
/// `problem` — the caller then keeps its witness-less behaviour.
pub(crate) fn ground_derivation_from_linear_trace(
    problem: &ChcProblem,
    trace: &LinearTrace,
    deadline: Option<Instant>,
    cancellation: &CancellationToken,
) -> Option<GroundDerivation> {
    let stopped = || {
        cancellation.is_cancelled() || deadline.is_some_and(|deadline| Instant::now() >= deadline)
    };
    let pred = problem.get_predicate(trace.predicate)?;
    let arg_sorts = pred.arg_sorts.as_slice();
    let n = trace.states.len().checked_sub(1)?;
    if trace
        .states
        .iter()
        .any(|state| state.len() != arg_sorts.len())
    {
        return None;
    }
    let clauses = TraceClauses::new(problem, trace.predicate, arg_sorts);
    let _witness_budget =
        super::witness::ScopedWitnessChainBudget::new_bounded(deadline, cancellation.clone());
    let empty_hint = TraceEdgeHint::default();
    let mut steps: Vec<GroundDerivationStep> = Vec::with_capacity(n + 2);
    let mut current: Option<Vec<SmtValue>> = None;
    for edge in 0..=n + 1 {
        let role = match edge {
            0 => Role::Fact,
            e if e <= n => Role::Transition,
            _ => Role::Query,
        };
        let head_hint = (edge <= n).then(|| trace.states[edge].as_slice());
        let edge_hint = trace.edges.get(edge).unwrap_or(&empty_hint);
        let Some((clause_index, env, head)) =
            clauses.fire_edge(role, edge_hint, current.as_deref(), head_hint, &stopped)
        else {
            super::log_ground_translation_detail(format_args!(
                "linear-trace: edge {edge}/{} failed (state values known: {}/{}, hints: {})",
                n + 1,
                head_hint.map_or(0, |h| h.iter().filter(|v| v.is_some()).count()),
                arg_sorts.len(),
                edge_hint.clause_values.len() + edge_hint.ts_locals.len(),
            ));
            return None;
        };
        let premises = if edge == 0 {
            Vec::new()
        } else {
            vec![edge - 1]
        };
        steps.push(GroundDerivationStep {
            clause_index,
            env,
            premises,
        });
        current = Some(head);
    }
    let derivation = GroundDerivation {
        query_step: steps.len() - 1,
        steps,
    };
    match validate_ground_derivation(problem, &derivation) {
        Ok(()) => Some(derivation),
        Err(err) => {
            super::log_ground_translation_detail(format_args!(
                "linear-trace derivation rejected on the engine's own problem: {err}"
            ));
            None
        }
    }
}

#[cfg(test)]
#[path = "linear_trace_tests.rs"]
mod tests;
