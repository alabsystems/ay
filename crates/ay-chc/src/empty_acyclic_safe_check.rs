// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Independent re-check of an empty-model acyclic CHC SAFE.
//!
//! An empty invariant model is a SAFE claim with no invariant to check: for an
//! acyclic clause system it asserts that no derivation of `false` exists. The
//! acyclic BMC engine makes that claim. Until 2026-09-29 the validators that
//! admitted it (`engines::validate_external_invariant_model`,
//! `external_invariant_model_excludes_error`, the adaptive finalize gate, the
//! proof-grade PDR prepass) re-ran that same engine, or trusted its label, and
//! asked nothing else, so one encoding defect was both the proof and its
//! validation. Each of them now also requires this check. The defect was
//! real: `BmcSolver::mk_rule_vars` kept head-only clause variables under their
//! source names, so the unsafe system
//!
//! ```text
//! P(x + 1).   P(a) => Q(a, x + 2).   Q(a, c) /\ c = a + 5 => false
//! ```
//!
//! (x = a - 1 in the first clause, x = a + 3 in the second) was proved SAFE,
//! validated SAFE, published under `--rigor certified` and accepted as proof
//! in-process with `strict_proofs = true`.
//!
//! This module decides the claim without the engine. It unrolls the ORIGINAL
//! clauses of the query cone with fresh constants per clause instance, and
//! asks a fresh `ay-dpll` executor for `unsat`:
//!
//! - a linear cone (at most one body predicate per clause) uses the path
//!   encoding in [`linear_path`], one variable copy per clause and per
//!   predicate, polynomial in the clause system;
//! - any other cone uses the full inlining of
//!   [`crate::proof_metadata::replay_check::acyclic_exhaustion_query_formulas`],
//!   the same formula the strict checked replay discharges (size-capped).
//!
//! Only `unsat` on every formula confirms. A timeout, cancellation, executor
//! `unknown`/`sat`/error, a cycle in the query cone, an unsupported theory, an
//! encoding cap, or a cone clause that could defeat renaming apart (it
//! reaches the expression depth cap, or a source variable already carries a
//! fresh prefix) all refuse (the caller then publishes `unknown`). A script
//! this check already decided `unsat` in this process is not decided again
//! ([`memo`]).
//!
//! The executor sheds its internal proof cycle, so its `unsat` is the raw
//! verdict `--rigor fast` publishes, not a checked refutation: the value of
//! this check is a second decision procedure on a second encoding. The
//! certified discharge of the same obligations remains the strict checked
//! replay's. (Proof-carrying, the executor took 12-24 s on a 40-level BV64
//! chain it decides raw in 0.04 s; at the finalize gate that would demote
//! genuine SAFEs.)

use crate::smt::executor_adapter::{
    collect_dt_declarations_for_expr, collect_uninterpreted_function_declarations, detect_logic,
    emit_declare_datatypes, emit_declare_uninterpreted_function, quote_symbol, sort_to_smtlib,
    InterruptObserver, ReplayCancellation,
};
use crate::{CancellationToken, ChcExpr, ChcProblem, InvariantModel};
use ay_core::time::Instant;
use std::fmt::Write as _;
use std::panic::AssertUnwindSafe;
use std::time::Duration;

mod linear_path;
mod memo;
#[cfg(test)]
mod memory_tests;
#[cfg(test)]
mod tests;

/// Cap on one finalize-time re-check. The finalize gate also intersects it
/// with the whole-run deadline.
const FINALIZE_RECHECK_BUDGET: Duration = Duration::from_secs(20);

/// Why an empty-model acyclic SAFE was not confirmed. Every variant means the
/// same thing to a caller (refuse); the distinction is diagnostic.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum NotConfirmed {
    /// Zero/expired budget, cancellation or term-memory refusal before a verdict.
    Budget,
    /// Arrays, reals or recursive datatypes: outside the admitted class
    /// ([`decides_theory_of`]).
    UnsupportedTheory,
    /// The query cone is cyclic, so a fixed unrolling is not exhaustive.
    CyclicQueryCone,
    /// The encoding could not be built (arity mismatch, expansion cap, ...).
    Encoding(String),
    /// The executor failed (parse or execution error, interrupt observer).
    Executor(String),
    /// The executor did not answer `unsat` (the payload is what it answered).
    NotUnsat(Option<String>),
}

/// Decide an empty-model SAFE claim for `problem` independently of any CHC
/// engine. `Ok(())` only when every derivation-of-`false` formula of the query
/// cone is `unsat` on a fresh executor within `budget`.
pub(crate) fn check(
    problem: &ChcProblem,
    budget: Duration,
    cancellation: Option<&CancellationToken>,
) -> Result<(), NotConfirmed> {
    let memory = crate::bmc::memory::Budget::capture(None, None);
    let _memory_scope = memory.install();
    if !memory.open()
        || budget.is_zero()
        || cancellation.is_some_and(CancellationToken::is_cancelled)
    {
        return Err(NotConfirmed::Budget);
    }
    let deadline = Instant::now()
        .checked_add(budget)
        .ok_or(NotConfirmed::Budget)?;
    let control =
        crate::smt::replay_control::ScopedReplayControl::install_until(deadline, cancellation);
    if !control.open() {
        return Err(NotConfirmed::Budget);
    }
    if !decides_theory_of(problem) {
        return Err(NotConfirmed::UnsupportedTheory);
    }
    let formulas = derivation_formulas(problem)?;
    let observed = control.cancellation().map(ReplayCancellation::new);
    for formula in &formulas {
        if !control.open() {
            return Err(NotConfirmed::Budget);
        }
        if matches!(formula, ChcExpr::Bool(false)) {
            continue;
        }
        let script = render(formula)?;
        // This check's own earlier `unsat` for the byte-identical script (the
        // finalize gate, then the discharge gate or an external backstop,
        // decide the same claim in one process). Never an engine's claim.
        if memo::confirmed_before(&script) {
            continue;
        }
        let verdict = decide(&script, control.deadline(), observed.as_ref())?;
        if verdict.as_deref() != Some("unsat") {
            return Err(NotConfirmed::NotUnsat(verdict));
        }
        memo::record_confirmed(script);
    }
    if control.open() {
        Ok(())
    } else {
        Err(NotConfirmed::Budget)
    }
}

/// Whether [`check`] decides `problem`'s theory: not arrays, reals or
/// recursive datatypes (the empty-model certificate class excludes them, so
/// no caller that admits such a problem is weakened by the exclusion).
pub(crate) fn decides_theory_of(problem: &ChcProblem) -> bool {
    !(problem.has_array_sorts()
        || problem.has_real_sorts()
        || problem.has_recursive_datatype_sorts())
}

/// Whether `problem`'s query cone is acyclic, which [`check`] requires before
/// it decides anything ([`NotConfirmed::CyclicQueryCone`]). A stutter rule
/// `P(x) /\ C => P(x)` in the cone counts as a cycle here, although the
/// classifier ignores it.
pub(crate) fn query_cone_is_acyclic(problem: &ChcProblem) -> bool {
    linear_path::QueryCone::of(problem).is_acyclic()
}

/// The first output of `script` on a fresh proof-shedding executor (see the
/// module documentation). A verdict that arrives after `deadline` or after
/// cancellation is refused like a timeout.
fn decide(
    script: &str,
    deadline: Instant,
    cancellation: Option<&ReplayCancellation>,
) -> Result<Option<String>, NotConfirmed> {
    let memory = crate::bmc::memory::Budget::capture(None, None);
    let stopped = || {
        !memory.open()
            || Instant::now() >= deadline
            || cancellation.is_some_and(ReplayCancellation::is_cancelled)
            || ay_core::TermStore::global_memory_exceeded()
    };
    if stopped() {
        return Err(NotConfirmed::Budget);
    }
    let commands = ay_frontend::parse(script)
        .map_err(|error| NotConfirmed::Executor(format!("parse: {error}")))?;
    let mut observer = cancellation
        .map(InterruptObserver::new)
        .transpose()
        .map_err(|error| NotConfirmed::Executor(error.to_string()))?;
    let mut executor = ay_dpll::Executor::new();
    if !memory.constrain(&mut executor) {
        return Err(NotConfirmed::Budget);
    }
    executor.set_competition_mode(true);
    executor.set_deadline(Some(deadline));
    if let Some(observer) = &observer {
        executor.set_interrupt(observer.interrupt());
    }
    let outputs = ay_core::catch_ay_panics(
        AssertUnwindSafe(|| {
            executor
                .execute_all(&commands)
                .map_err(|error| error.to_string())
        }),
        Err,
    );
    let memory_open = memory.executor_open(&executor);
    crate::smt::resource_observation::note_executor_refusal(executor.unknown_reason());
    drop(executor);
    let observer_clean = observer.as_mut().map_or(true, InterruptObserver::finish);
    if !memory_open || !observer_clean || stopped() {
        return Err(NotConfirmed::Budget);
    }
    let outputs = outputs.map_err(NotConfirmed::Executor)?;
    Ok(outputs.into_iter().next())
}

/// [`check`] as a verdict gate: `true` only on confirmation.
pub(crate) fn confirmed(
    problem: &ChcProblem,
    budget: Duration,
    cancellation: Option<&CancellationToken>,
) -> bool {
    match check(problem, budget, cancellation) {
        Ok(()) => true,
        Err(reason) => {
            tracing::debug!(
                ?reason,
                "empty-model acyclic SAFE not confirmed by the independent re-check"
            );
            false
        }
    }
}

/// [`confirmed`] for the adaptive finalize gate: the remaining whole-run
/// budget capped at [`FINALIZE_RECHECK_BUDGET`], cancelled by the portfolio's
/// own token or the caller's.
pub(crate) fn confirmed_at_finalize(
    problem: &ChcProblem,
    remaining: Option<Duration>,
    portfolio: &CancellationToken,
    external: Option<&CancellationToken>,
) -> bool {
    let budget = remaining.map_or(FINALIZE_RECHECK_BUDGET, |remaining| {
        remaining.min(FINALIZE_RECHECK_BUDGET)
    });
    let mut cancellation = portfolio.child();
    if let Some(external) = external {
        cancellation.link_upstream(external);
    }
    confirmed(problem, budget, Some(&cancellation))
}

/// One formula per decision: satisfiable iff some derivation of `false`
/// exists. Built from the ORIGINAL clauses; no engine state is consulted.
fn derivation_formulas(problem: &ChcProblem) -> Result<Vec<ChcExpr>, NotConfirmed> {
    let cone = linear_path::QueryCone::of(problem);
    if !cone.is_acyclic() {
        return Err(NotConfirmed::CyclicQueryCone);
    }
    // The renamed-apart guard below reads variable NAMES, and renaming (like
    // `ChcExpr::vars`) stops at the expression depth cap. A source variable
    // spelled in a fresh namespace would then alias a fresh constant
    // unnoticed, so refuse a cone clause that mentions one anywhere (the walk
    // has no depth cut-off) or that reaches the depth cap.
    if cone.clauses().any(clause_defeats_renaming) {
        return Err(NotConfirmed::Encoding(
            "a clause reaches the renaming depth cap or uses a reserved name".to_string(),
        ));
    }
    let (formulas, fresh_prefix) = if cone.is_linear() {
        (vec![cone.path_formula(problem)?], linear_path::FRESH_PREFIX)
    } else {
        let formulas =
            crate::proof_metadata::replay_check::acyclic_exhaustion_query_formulas(problem)
                .map_err(|error| NotConfirmed::Encoding(error.to_string()))?;
        (
            formulas.into_iter().map(|(_, formula)| formula).collect(),
            INLINING_PREFIX,
        )
    };
    // Both encodings rename every clause variable apart. `ChcExpr::substitute`
    // leaves a subtree unrenamed when it hits its node or depth budget, which
    // would re-share a source variable between clause instances: the very
    // defect this check exists to catch. Refuse unless renaming was complete.
    let renamed_apart = formulas.iter().all(|formula| {
        formula
            .vars()
            .iter()
            .all(|var| var.name.starts_with(fresh_prefix))
    });
    if !renamed_apart {
        return Err(NotConfirmed::Encoding(
            "a source variable survived renaming".to_string(),
        ));
    }
    Ok(formulas)
}

/// Name prefix of the full inlining's constants (`replay_check`).
const INLINING_PREFIX: &str = "__acx";

/// Whether renaming `clause` apart could be incomplete or ambiguous: some
/// expression reaches the depth at which `ChcExpr::substitute` and
/// `ChcExpr::vars` stop, or some variable already carries a fresh prefix.
fn clause_defeats_renaming(clause: &crate::HornClause) -> bool {
    let defeats = |expr: &ChcExpr| {
        crate::expr::dag::longest_path_at_least(expr, crate::expr::MAX_EXPR_RECURSION_DEPTH)
            || !crate::expr::dag::all_distinct(expr, |node| {
                !matches!(node, ChcExpr::Var(var)
                    if var.name.starts_with(linear_path::FRESH_PREFIX)
                        || var.name.starts_with(INLINING_PREFIX))
            })
    };
    let head_arguments: &[ChcExpr] = match &clause.head {
        crate::ClauseHead::Predicate(_, arguments) => arguments,
        crate::ClauseHead::False => &[],
    };
    clause.body.constraint.iter().any(defeats)
        || clause
            .body
            .predicates
            .iter()
            .flat_map(|(_, arguments)| arguments)
            .any(defeats)
        || head_arguments.iter().any(defeats)
}

/// One self-contained SMT-LIB query for `formula`.
fn render(formula: &ChcExpr) -> Result<String, NotConfirmed> {
    let encoding = |reason: String| NotConfirmed::Encoding(reason);
    let vars = formula.vars();
    let datatypes = collect_dt_declarations_for_expr(&vars, formula)
        .map_err(|error| encoding(format!("datatype declarations: {error}")))?;
    let functions = collect_uninterpreted_function_declarations(formula)
        .map_err(|error| encoding(format!("function declarations: {error}")))?;
    let mut script = format!("(set-logic {})\n", detect_logic(&vars, formula));
    script.push_str(
        &emit_declare_datatypes(&datatypes)
            .map_err(|error| encoding(format!("datatype declarations: {error}")))?,
    );
    for function in &functions {
        script.push_str(&emit_declare_uninterpreted_function(function));
    }
    for var in &vars {
        let _ = writeln!(
            script,
            "(declare-const {} {})",
            quote_symbol(&var.name),
            sort_to_smtlib(&var.sort)
        );
    }
    let _ = writeln!(
        script,
        "(assert {})\n(check-sat)",
        InvariantModel::expr_to_smtlib(formula)
    );
    Ok(script)
}
