// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded per-clause SMT witness solve for ground-environment completion.
//!
//! Ground unit propagation ([`super::complete`]) recovers a clause variable
//! whenever some equality conjunct DETERMINES it from already-bound values.
//! That covers most of an original clause, but not a variable a clause
//! constrains only through an ITE, a datatype tester or a disjunction: those
//! carry real information, just not in the shape propagation reads. Completion
//! previously fell back to a SORT DEFAULT there, which the validator then
//! rejects as soon as the default contradicts the clause.
//!
//! This module asks a solver for those values instead: pin every variable the
//! environment already binds, assert the clause's own constraint, and read the
//! remaining variables off the model.
//!
//! # Why this needs its own deadline scope
//!
//! A bounded solve was tried here before and recorded as useless — the note it
//! left claimed the executor "returns Unknown on those clauses in ~97ms
//! whatever timeout it is given" and called that a DT+array+BV theory gap.
//! That reading was wrong, and measurably so: all 357 constraint-bearing
//! original clauses of the `iterator_count` archetype are decided SAT by this
//! very solver in <=40ms each (z3 agrees on all 357). There is no theory gap.
//!
//! The real mechanism is scope. Back-translation runs INSIDE the BMC probe's
//! [`crate::smt::deadline::ScopedSmtDeadline`], after the probe has spent
//! nearly all of it, and `ScopedSmtDeadline` by design only ever TIGHTENS. So a
//! nested witness solve receives `min(request, few-ms remainder)` however much
//! it asks for — 100ms and 5000ms are the same request — and an already-expired
//! deadline returns Unknown before solving at all. That is the "~97ms whatever
//! timeout" signature: a budget artifact read as a theory failure.
//!
//! [`crate::smt::deadline::ScopedSmtDeadlineOverride`] is what lets this solve
//! actually receive the tens of milliseconds it needs.
//!
//! # Soundness
//!
//! This module cannot change any verdict. It only ever ADDS bindings to a
//! candidate environment that
//! [`super::validate_ground_derivation`] re-evaluates from scratch against the
//! ORIGINAL clauses; that validator is and remains the sole acceptance anchor.
//! A witness value that is wrong makes a constraint evaluate to `false` or stay
//! indeterminate, and the derivation is rejected — exactly as a bad sort
//! default is today. Every failure path (refused query, exhausted budget,
//! Unknown, Unsat, non-concrete model value) leaves `env` untouched, so
//! behavior falls back to today's sort-default completion.

use super::is_concrete;
use crate::clause::HornClause;
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::cell::Cell;
use std::time::Duration;

/// Per-witness-solve wall-clock budget.
///
/// The measured cost of the shapes this targets is 10-40ms; 2s is generous
/// headroom, not an expectation.
fn witness_budget() -> Duration {
    static MS: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    Duration::from_millis(*MS.get_or_init(|| {
        std::env::var("AY_CHC_GROUND_WITNESS_BUDGET_MS")
            .ok()
            .and_then(|v| v.parse::<u64>().ok())
            .unwrap_or(2_000)
    }))
}

/// Total wall-clock budget for ALL witness solves in one back-translation.
///
/// A long expansion has hundreds of steps; without a chain cap the per-solve
/// budget would multiply. When this is exhausted every further solve is
/// skipped and completion reverts to sort defaults.
fn witness_chain_budget() -> Duration {
    static MS: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    Duration::from_millis(*MS.get_or_init(|| {
        std::env::var("AY_CHC_GROUND_WITNESS_TOTAL_MS")
            .ok()
            .and_then(|v| v.parse::<u64>().ok())
            .unwrap_or(30_000)
    }))
}

/// Whether the witness solve is enabled at all (kill switch).
fn witness_enabled() -> bool {
    static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *FLAG.get_or_init(|| {
        !std::env::var("AY_CHC_DISABLE_GROUND_WITNESS")
            .map(|value| value != "0")
            .unwrap_or(false)
    })
}

thread_local! {
    /// Wall-clock already spent on witness solves in the current chain.
    static CHAIN_SPENT: Cell<Duration> = const { Cell::new(Duration::ZERO) };
}

/// RAII guard resetting the per-chain witness budget for one back-translation.
///
/// Installed at the back-translation landing sites so each attempt gets its own
/// chain budget and a previous attempt's spend cannot starve it. Restores the
/// enclosing chain's spend on drop so nested chains compose.
pub(crate) struct ScopedWitnessChainBudget(Duration);

impl ScopedWitnessChainBudget {
    pub(crate) fn new() -> Self {
        Self(CHAIN_SPENT.with(|cell| cell.replace(Duration::ZERO)))
    }
}

impl Drop for ScopedWitnessChainBudget {
    fn drop(&mut self) {
        CHAIN_SPENT.with(|cell| cell.set(self.0));
    }
}

/// Remaining chain budget, or `None` when it is exhausted.
fn chain_remaining() -> Option<Duration> {
    let spent = CHAIN_SPENT.with(Cell::get);
    witness_chain_budget()
        .checked_sub(spent)
        .filter(|r| !r.is_zero())
}

/// Turn a concrete [`SmtValue`] into a literal of `sort`, when the two agree.
///
/// Deliberately strict: a value whose kind does not match the declared sort is
/// refused rather than coerced, so a pin can never assert something the clause
/// does not mean.
fn value_to_literal(value: &SmtValue, sort: &ChcSort) -> Option<ChcExpr> {
    match (sort, value) {
        (ChcSort::Int, SmtValue::Int(i)) => Some(ChcExpr::int(*i)),
        (ChcSort::Bool, SmtValue::Bool(b)) => Some(ChcExpr::Bool(*b)),
        (ChcSort::BitVec(w), SmtValue::BitVec(v, vw)) if w == vw => Some(ChcExpr::BitVec(*v, *w)),
        _ => None,
    }
}

/// True when `value` is a usable binding for a variable of `sort`.
///
/// Datatype values are checked STRUCTURALLY against the sort's own constructor
/// table: the constructor must be one this sort declares, the field count must
/// match that constructor's arity, and every field must itself fit its declared
/// selector sort. Admitting a datatype value that does not belong to the sort
/// would let a later ground evaluation read a selector that does not exist and
/// abstain, silently costing the step; refusing it here just falls back to the
/// sort default, which is the pre-existing behavior.
///
/// This case matters: it is the archetype's actual blocker. The variable the
/// expansion stalls on (`__switchint_sort_coerce_23`) is `Option_u8`-sorted,
/// so a numeric-only filter drops the very value the witness solve found.
fn value_fits_sort(value: &SmtValue, sort: &ChcSort) -> bool {
    match (sort, value) {
        (ChcSort::Int, SmtValue::Int(_) | SmtValue::BigInt(_)) => true,
        (ChcSort::Bool, SmtValue::Bool(_)) => true,
        (ChcSort::BitVec(w), SmtValue::BitVec(_, vw)) => w == vw,
        (ChcSort::Real, SmtValue::Real(_) | SmtValue::Int(_)) => true,
        (ChcSort::Datatype { constructors, .. }, SmtValue::Datatype(ctor, fields)) => constructors
            .iter()
            .find(|c| &c.name == ctor)
            .is_some_and(|c| {
                c.selectors.len() == fields.len()
                    && c.selectors
                        .iter()
                        .zip(fields.iter())
                        .all(|(selector, field)| value_fits_sort(field, &selector.sort))
            }),
        (ChcSort::Array(_, element), SmtValue::ConstArray(default)) => {
            value_fits_sort(default, element)
        }
        _ => false,
    }
}

/// Try to witness values for `unbound` from `clause`'s own constraint.
///
/// Returns the number of variables newly bound in `env`. Never removes or
/// overwrites an existing binding.
pub(crate) fn witness_unbound_vars(
    clause: &HornClause,
    conjuncts: &[ChcExpr],
    unbound: &[ChcVar],
    env: &mut FxHashMap<String, SmtValue>,
) -> usize {
    if !witness_enabled() || unbound.is_empty() || conjuncts.is_empty() {
        return 0;
    }
    let Some(remaining) = chain_remaining() else {
        super::log_ground_translation_detail(format_args!(
            "witness: chain budget exhausted, {} vars fall back to sort defaults",
            unbound.len()
        ));
        return 0;
    };
    let budget = witness_budget().min(remaining);

    // Pin every variable the environment already determined. Only concrete
    // values of a matching sort become pins; anything else is simply left
    // unpinned (the solver may then choose it freely, which is sound here —
    // the validator re-checks every binding we keep).
    let mut query_parts: Vec<ChcExpr> = conjuncts.to_vec();
    let all_vars = clause_var_sorts(clause);
    for (name, value) in env.iter() {
        if !is_concrete(value) {
            continue;
        }
        let Some(sort) = all_vars.get(name) else {
            continue;
        };
        let Some(literal) = value_to_literal(value, sort) else {
            continue;
        };
        query_parts.push(ChcExpr::eq(
            ChcExpr::Var(ChcVar::new(name, sort.clone())),
            literal,
        ));
    }
    let query = ChcExpr::and_all(query_parts);

    // Cheap well-formedness pre-check BEFORE spending any budget. A query the
    // frontend would refuse returns Unknown indistinguishably from a theory
    // failure at this call site -- which is precisely how the original
    // misdiagnosis happened. Refusals are logged with their reason.
    if let Some(reason) = crate::smt::executor_sort_guard::unsupported_executor_expr_reason(&query)
    {
        super::log_ground_translation_detail(format_args!(
            "witness: query refused before solving ({reason}); {} vars fall back to sort defaults",
            unbound.len()
        ));
        return 0;
    }

    let started = ay_core::time::Instant::now();
    let result = {
        // Replace the (exhausted) enclosing BMC-probe deadline: see the module
        // note. Verdict-neutral -- this only buys wall-clock for a terminal,
        // re-validated side computation.
        let _deadline = crate::smt::deadline::ScopedSmtDeadlineOverride::install(budget);
        // The no-progress breaker is THREAD-local, not per-context, and its only
        // other production reset is in the PDR main loop; on this (BMC/adaptive)
        // lane a trip anywhere would otherwise latch every later check_sat on
        // the thread. A fresh context alone does not clear it.
        let _breaker = crate::smt::ScopedNoProgressBreaker::new();
        // A FRESH context so the per-context sticky latches (conversion-budget
        // strikes, term-memory) cannot carry in from the enclosing engine.
        let mut ctx = crate::smt::SmtContext::new();
        let _timeout = ctx.scoped_check_timeout(Some(budget));
        // The completeness-oriented lane: plain `check_sat` is documented as the
        // graceful-degradation lane whose callers WANT Unknown. A witness solve
        // needs an answer.
        ctx.check_sat_with_executor_fallback(&query)
    };
    let elapsed = started.elapsed();
    CHAIN_SPENT.with(|cell| cell.set(cell.get().saturating_add(elapsed)));

    let model = match result {
        crate::smt::SmtResult::Sat(model) => model,
        other => {
            super::log_ground_translation_detail(format_args!(
                "witness: {} vars undetermined -> {:?} in {}ms; sort defaults",
                unbound.len(),
                std::mem::discriminant(&other),
                elapsed.as_millis()
            ));
            return 0;
        }
    };

    let mut bound = 0usize;
    for var in unbound {
        if env.contains_key(&var.name) {
            continue;
        }
        let Some(value) = model.get(&var.name) else {
            continue;
        };
        if !is_concrete(value) || !value_fits_sort(value, &var.sort) {
            continue;
        }
        env.insert(var.name.clone(), value.clone());
        bound += 1;
    }
    super::log_ground_translation_detail(format_args!(
        "witness: solved {}/{} previously-undetermined vars in {}ms",
        bound,
        unbound.len(),
        elapsed.as_millis()
    ));
    bound
}

/// Name -> sort for every variable occurring in the clause.
fn clause_var_sorts(clause: &HornClause) -> FxHashMap<String, ChcSort> {
    let mut map: FxHashMap<String, ChcSort> = FxHashMap::default();
    for var in clause.body.vars() {
        map.entry(var.name.clone()).or_insert(var.sort.clone());
    }
    for var in clause.head.vars() {
        map.entry(var.name.clone()).or_insert(var.sort.clone());
    }
    map
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ChcDtConstructor, ChcDtSelector};
    use std::sync::Arc;

    /// `Option_u8 ::= None | Some(val: BitVec 8)` — the archetype's datatype.
    fn option_u8() -> ChcSort {
        ChcSort::Datatype {
            name: "Option_u8".to_string(),
            constructors: Arc::new(vec![
                ChcDtConstructor {
                    name: "None_Option_u8".to_string(),
                    selectors: vec![],
                },
                ChcDtConstructor {
                    name: "Some_Option_u8".to_string(),
                    selectors: vec![ChcDtSelector {
                        name: "val".to_string(),
                        sort: ChcSort::BitVec(8),
                    }],
                },
            ]),
        }
    }

    /// The regression this module's second fix is about: a datatype-sorted
    /// witness value must be ACCEPTED. Rejecting it sent the archetype's
    /// `__switchint_sort_coerce_23` back to its `None` sort default, which is
    /// exactly the value that falsifies clause 297's tester conjunct.
    #[test]
    fn datatype_witness_values_are_accepted() {
        let sort = option_u8();
        assert!(value_fits_sort(
            &SmtValue::Datatype("None_Option_u8".to_string(), vec![]),
            &sort
        ));
        assert!(value_fits_sort(
            &SmtValue::Datatype("Some_Option_u8".to_string(), vec![SmtValue::BitVec(7, 8)]),
            &sort
        ));
    }

    /// ...but only when it structurally belongs to the sort. These are the
    /// escapes the constructor-table check exists to close; each must fall
    /// back to the sort default rather than be admitted.
    #[test]
    fn ill_formed_datatype_witness_values_are_refused() {
        let sort = option_u8();
        // Constructor this sort does not declare.
        assert!(!value_fits_sort(
            &SmtValue::Datatype("Ok_Result_u8".to_string(), vec![]),
            &sort
        ));
        // Right constructor, wrong arity (nullary given a field).
        assert!(!value_fits_sort(
            &SmtValue::Datatype("None_Option_u8".to_string(), vec![SmtValue::BitVec(1, 8)]),
            &sort
        ));
        // Right constructor, missing field.
        assert!(!value_fits_sort(
            &SmtValue::Datatype("Some_Option_u8".to_string(), vec![]),
            &sort
        ));
        // Right constructor and arity, field of the wrong width.
        assert!(!value_fits_sort(
            &SmtValue::Datatype("Some_Option_u8".to_string(), vec![SmtValue::BitVec(7, 32)]),
            &sort
        ));
        // Right constructor and arity, field of the wrong kind entirely.
        assert!(!value_fits_sort(
            &SmtValue::Datatype("Some_Option_u8".to_string(), vec![SmtValue::Int(7)]),
            &sort
        ));
        // A non-datatype value for a datatype sort.
        assert!(!value_fits_sort(&SmtValue::Int(0), &sort));
    }

    /// Scalar sorts stay strict: a BV witness of the wrong width must not be
    /// coerced into a variable's binding.
    #[test]
    fn scalar_witness_values_are_width_and_kind_checked() {
        assert!(value_fits_sort(
            &SmtValue::BitVec(3, 8),
            &ChcSort::BitVec(8)
        ));
        assert!(!value_fits_sort(
            &SmtValue::BitVec(3, 8),
            &ChcSort::BitVec(32)
        ));
        assert!(!value_fits_sort(&SmtValue::Bool(true), &ChcSort::BitVec(8)));
        assert!(!value_fits_sort(&SmtValue::Int(1), &ChcSort::Bool));
        assert!(value_fits_sort(&SmtValue::Bool(false), &ChcSort::Bool));
    }

    /// A pin is only emitted for a value that matches its variable's declared
    /// sort; a mismatch must produce no pin rather than a coerced one.
    #[test]
    fn pins_are_only_built_for_sort_matched_values() {
        assert!(value_to_literal(&SmtValue::BitVec(5, 8), &ChcSort::BitVec(8)).is_some());
        assert!(value_to_literal(&SmtValue::BitVec(5, 8), &ChcSort::BitVec(16)).is_none());
        assert!(value_to_literal(&SmtValue::Int(5), &ChcSort::BitVec(8)).is_none());
        assert!(value_to_literal(&SmtValue::Bool(true), &ChcSort::Bool).is_some());
    }
}
