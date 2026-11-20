// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Monolithic Safe validation for single-predicate problems.
//!
//! When every ORIGINAL clause is a fact (`φ ⇒ P(t)`), a linear transition
//! (`P(s) ∧ φ ⇒ P(t)`) or a query (`P(s) ∧ φ ⇒ false`) over ONE predicate `P`,
//! a candidate interpretation `I` of `P` is a safety proof exactly when, for
//! every clause, `body(I) ∧ ¬head(I)` is unsatisfiable:
//!
//! - initiation: `φ ∧ ¬I(t)`,
//! - consecution: `I(s) ∧ φ ∧ ¬I(t)`,
//! - safety: `I(s) ∧ φ`.
//!
//! Each obligation is built from the clause exactly as authored (no ITE or
//! disjunction splitting, no clause rewriting) and handed to a fresh
//! Verification-lane [`SmtContext`] whole, so ITE terms and disjunctions are
//! the SMT solver's to case-split. The interpretation is instantiated with
//! [`ChcExpr::substitute_let_shared`]: it keeps the invariant's DAG sharing
//! (IMC's reached-set invariants are ~700x shared, which is what lets the
//! executor script be `let`-printed) and, having no node budget, can never
//! leave a binder unsubstituted.
//!
//! The result is three-valued. `Valid` needs every obligation UNSAT and the
//! per-rule validator's two cross-checks of an UNSAT answer passed: the
//! executor's on large obligations (#6787), and the concrete evaluation of
//! Int and small-BV assignments (#5381 / #5803), on every Safety obligation
//! while its 1 s budget lasts and on the first ten Initiation/Consecution
//! UNSATs (then one in a hundred), exactly as `model_safety.rs` and
//! `model_inductive.rs` run it. `Invalid` needs an obligation whose SAT model,
//! or a cross-check's witness, makes the obligation evaluate to exactly true
//! (a confirmed counterexample to the submitted interpretation). Anything
//! else — an undecided check, a cross-check the solve's end interrupted, or a
//! solve deadline already passed — is `Unknown`, and the caller runs the full
//! per-rule validator.
//!
//! Every check is clamped to the solve deadline the caller passes (as the
//! per-rule validator's `cap_timeout` clamps its clauses), so the pass never
//! runs past the end of the solve.

use super::*;
use crate::pdr::{ConcreteAnswer, ConcreteBudget, ConcreteStop};
use crate::smt::{SmtContext, SmtResult, SmtValue};
use ay_core::time::Instant;
use std::sync::Arc;

/// Wall-clock allowance of one monolithic obligation check. An obligation
/// that is not decided in it sends the whole model to the per-rule
/// validator, so this bounds the cost of the fast path when it fails.
pub(super) const MONOLITHIC_CHECK_TIMEOUT: Duration = Duration::from_secs(3);

/// Allowance of the executor cross-check of one large UNSAT obligation
/// (same as the per-rule validator's, `model_inductive.rs`).
const MONOLITHIC_CROSS_CHECK_TIMEOUT: Duration = Duration::from_millis(500);

/// UNSAT obligations at least this large (in nodes) are cross-checked by
/// the executor, as in the per-rule validator.
const MONOLITHIC_CROSS_CHECK_MIN_NODES: usize = 100;

/// Budget of the concrete cross-check over one monolithic pass: the per-rule
/// validator's (`verify_model_impl`, 1 s per verifier run).
pub(super) const MONOLITHIC_CONCRETE_BUDGET: Duration = Duration::from_secs(1);

/// Initiation/Consecution UNSATs always cross-checked concretely before the
/// one-in-[`CONCRETE_SAMPLE_PERIOD`] rate applies (#7410, as in
/// `model_inductive.rs`).
const CONCRETE_ALWAYS_CHECKED: u64 = 10;
const CONCRETE_SAMPLE_PERIOD: u64 = 100;

/// Which proof obligation of a single-predicate system a check discharges.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ObligationKind {
    /// Fact clause: the initial states satisfy the invariant.
    Initiation,
    /// Transition clause: the invariant is closed under the step.
    Consecution,
    /// Query clause: the invariant excludes the bad states.
    Safety,
}

/// One clause's validity query: the clause holds under the model iff
/// `query` is unsatisfiable.
#[derive(Clone, Debug)]
pub(super) struct Obligation {
    pub(super) clause_idx: usize,
    pub(super) kind: ObligationKind,
    /// The clause body under the model (`I(s) ∧ φ`, or `φ` for a fact): the
    /// conjuncts the concrete cross-check reads its Int bounds from, as the
    /// per-rule validator passes it.
    pub(super) body: ChcExpr,
    pub(super) query: ChcExpr,
}

/// Outcome of the monolithic validation of one model.
#[derive(Clone, Debug)]
pub(in crate::portfolio) enum MonolithicVerdict {
    /// Every obligation is UNSAT: the model is inductive and safe for the
    /// original clauses.
    Valid,
    /// An obligation has a confirmed satisfying assignment: the model is
    /// not a safety proof.
    Invalid(String),
    /// Some obligation is undecided (and none is refuted).
    Unknown(String),
}

/// Instantiate `interp` at `args`: a parallel, sharing-preserving
/// substitution of the binders, or `None` when the arity or binder sorts do
/// not match.
fn instantiate(interp: &PredicateInterpretation, args: &[ChcExpr]) -> Option<ChcExpr> {
    if interp.vars.len() != args.len() {
        return None;
    }
    let map: FxHashMap<&ChcVar, Arc<ChcExpr>> = interp
        .vars
        .iter()
        .zip(args)
        .map(|(var, arg)| (var, Arc::new(arg.clone())))
        .collect();
    let formula = Arc::new(interp.formula.clone());
    let applied = ChcExpr::substitute_let_shared(&formula, &map);
    Some(Arc::try_unwrap(applied).unwrap_or_else(|shared| (*shared).clone()))
}

/// The obligations of `model` on `problem`, or `None` when `problem` is not
/// a single-predicate fact/transition/query system or `model` cannot be
/// checked on it by these obligations alone.
///
/// `None` also covers every model the per-rule validator rejects before any
/// SMT check (missing interpretation, a binder list that does not match the
/// predicate's signature, free variables outside the binders, and the #5930
/// rule that a Real-argument predicate needs a Real-mentioning
/// interpretation), so those keep exactly their existing outcome.
pub(super) fn single_predicate_obligations(
    problem: &ChcProblem,
    model: &InvariantModel,
) -> Option<Vec<Obligation>> {
    let [pred] = problem.predicates() else {
        return None;
    };
    let interp = model.get(&pred.id)?;
    if interp.vars.len() != pred.arg_sorts.len()
        || interp
            .vars
            .iter()
            .zip(&pred.arg_sorts)
            .any(|(var, sort)| &var.sort != sort)
    {
        return None;
    }
    let formula_vars = interp.formula.vars();
    if formula_vars.iter().any(|v| !interp.vars.contains(v)) {
        return None;
    }
    if pred.arg_sorts.iter().any(|s| matches!(s, ChcSort::Real))
        && !formula_vars.iter().any(|v| v.sort == ChcSort::Real)
    {
        return None;
    }

    let mut obligations = Vec::with_capacity(problem.clauses().len());
    for (clause_idx, clause) in problem.clauses().iter().enumerate() {
        let body_inv = match clause.body.predicates.as_slice() {
            [] => None,
            [(id, args)] if *id == pred.id => Some(instantiate(interp, args)?),
            _ => return None,
        };
        let head_inv = match &clause.head {
            crate::ClauseHead::Predicate(id, args) if *id == pred.id => {
                Some(instantiate(interp, args)?)
            }
            crate::ClauseHead::Predicate(..) => return None,
            crate::ClauseHead::False => None,
        };
        let kind = match (&body_inv, &head_inv) {
            (None, Some(_)) => ObligationKind::Initiation,
            (Some(_), Some(_)) => ObligationKind::Consecution,
            (Some(_), None) => ObligationKind::Safety,
            // A predicate-free clause is not part of this shape.
            (None, None) => return None,
        };
        let mut body_parts = Vec::with_capacity(2);
        body_parts.extend(body_inv);
        body_parts.extend(clause.body.constraint.clone());
        let body = ChcExpr::and_all(body_parts);
        let query = match head_inv {
            Some(head) => ChcExpr::and(body.clone(), ChcExpr::not(head)),
            None => body.clone(),
        };
        obligations.push(Obligation {
            clause_idx,
            kind,
            body,
            query,
        });
    }
    Some(obligations)
}

fn is_unsat(result: &SmtResult) -> bool {
    matches!(
        result,
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
    )
}

/// Whether `model` makes `query` exactly true.
fn confirms(query: &ChcExpr, model: &FxHashMap<String, SmtValue>) -> bool {
    matches!(
        crate::expr::evaluate_expr(query, model),
        Some(SmtValue::Bool(true))
    )
}

/// What the SMT check of one obligation answered.
#[derive(Debug, PartialEq, Eq)]
enum SmtVerdict {
    /// UNSAT, and the executor cross-check (when it applies) found no model.
    Unsat,
    /// A model that makes the obligation exactly true.
    Refuted,
    /// Neither.
    Undecided,
}

/// Test seam: what every obligation's SMT check answers instead of the
/// solver's own answer.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ForcedSmt {
    /// UNSAT, as a solver false-UNSAT would answer: shows what the
    /// cross-checks after it catch.
    Unsat,
    /// Unknown: drives the fallback to the per-rule validator.
    Undecided,
}

#[cfg(test)]
thread_local! {
    static FORCED_SMT: std::cell::Cell<Option<ForcedSmt>> = const { std::cell::Cell::new(None) };
}

/// Run `f` with every monolithic SMT check answering `forced` (test seam).
#[cfg(test)]
pub(super) fn with_forced_smt<T>(forced: ForcedSmt, f: impl FnOnce() -> T) -> T {
    struct Reset;
    impl Drop for Reset {
        fn drop(&mut self) {
            FORCED_SMT.with(|cell| cell.set(None));
        }
    }
    FORCED_SMT.with(|cell| cell.set(Some(forced)));
    let _reset = Reset;
    f()
}

#[cfg(test)]
fn forced_smt_result() -> Option<SmtResult> {
    FORCED_SMT
        .with(std::cell::Cell::get)
        .map(|forced| match forced {
            ForcedSmt::Unsat => SmtResult::Unsat,
            ForcedSmt::Undecided => SmtResult::Unknown,
        })
}

#[cfg(not(test))]
fn forced_smt_result() -> Option<SmtResult> {
    None
}

/// The SMT check of one obligation, within `timeout` of wall clock (the
/// caller has clamped it to the solve deadline).
fn smt_check_obligation(obligation: &Obligation, timeout: Duration) -> SmtVerdict {
    let check_deadline = Instant::now() + timeout;
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(check_deadline);
    let mut smt = SmtContext::new();
    let result = forced_smt_result()
        .unwrap_or_else(|| smt.check_sat_with_timeout(&obligation.query, timeout));
    match result {
        SmtResult::Sat(model) if confirms(&obligation.query, &model) => SmtVerdict::Refuted,
        result if is_unsat(&result) => {
            // #6787 cross-check, as the per-rule validator does for large
            // UNSAT clause queries: an executor model that satisfies the
            // original obligation refutes the UNSAT answer.
            let left = check_deadline.saturating_duration_since(Instant::now());
            if !left.is_zero()
                && obligation
                    .query
                    .node_count(MONOLITHIC_CROSS_CHECK_MIN_NODES)
                    >= MONOLITHIC_CROSS_CHECK_MIN_NODES
            {
                let cross = smt.check_sat_via_executor(
                    &obligation.query,
                    &FxHashMap::default(),
                    MONOLITHIC_CROSS_CHECK_TIMEOUT.min(left),
                );
                if let SmtResult::Sat(model) = cross {
                    tracing::warn!(
                        clause_idx = obligation.clause_idx,
                        "monolithic validation: executor cross-check found a model of an UNSAT obligation (#6787)"
                    );
                    return if confirms(&obligation.query, &model) {
                        SmtVerdict::Refuted
                    } else {
                        SmtVerdict::Undecided
                    };
                }
            }
            SmtVerdict::Unsat
        }
        _ => SmtVerdict::Undecided,
    }
}

/// Where a monolithic pass must stop: the solve's cancellation token and
/// deadline (`None`: unbounded), and any further boundary `stopped` reports.
pub(super) struct PassBoundary<'a, F: FnMut() -> bool> {
    pub(super) cancellation: Option<&'a crate::CancellationToken>,
    pub(super) deadline: Option<Instant>,
    pub(super) stopped: F,
}

impl<F: FnMut() -> bool> PassBoundary<'_, F> {
    fn closed(&mut self) -> bool {
        self.cancellation
            .is_some_and(crate::CancellationToken::is_cancelled)
            || self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
            || (self.stopped)()
    }

    /// `per_check` clamped to what is left before the deadline.
    fn clamp(&self, per_check: Duration) -> Duration {
        match self.deadline {
            Some(deadline) => per_check.min(deadline.saturating_duration_since(Instant::now())),
            None => per_check,
        }
    }
}

/// Check `obligations` (safety first, then initiation, then consecution),
/// each in a fresh Verification-lane context with `per_check` wall clock
/// (clamped to the boundary's deadline), and cross-check every UNSAT answer
/// as the module docs describe.
///
/// Stops at the first refuted obligation (`Invalid`) and at the first
/// undecided one (`Unknown`): the per-rule validator the caller then runs
/// re-checks every clause, so deciding the remaining obligations here would
/// only add to the cost of the fallback, which is bounded by one
/// `per_check` plus the obligations already decided and the 1 s concrete
/// budget. Also stops when the boundary closes.
pub(super) fn check_obligations<F: FnMut() -> bool>(
    obligations: &[Obligation],
    per_check: Duration,
    mut boundary: PassBoundary<'_, F>,
) -> MonolithicVerdict {
    let _verification_pin = crate::smt::lane::ScopedVerificationMode::install();
    let mut concrete = ConcreteBudget::new(
        MONOLITHIC_CONCRETE_BUDGET,
        ConcreteStop::of_caller(
            boundary.cancellation.into_iter().cloned().collect(),
            boundary.deadline,
        ),
    );
    let mut concrete_unsat_count: u64 = 0;
    let rank = |kind: ObligationKind| match kind {
        ObligationKind::Safety => 0,
        ObligationKind::Initiation => 1,
        ObligationKind::Consecution => 2,
    };
    let mut order: Vec<&Obligation> = obligations.iter().collect();
    order.sort_by_key(|o| (rank(o.kind), o.clause_idx));
    let closed = || MonolithicVerdict::Unknown("validation boundary closed".to_string());
    for obligation in order {
        if boundary.closed() {
            return closed();
        }
        let timeout = boundary.clamp(per_check);
        if timeout.is_zero() {
            return closed();
        }
        let undecided = || {
            MonolithicVerdict::Unknown(format!(
                "{:?} obligation of clause {} is undecided",
                obligation.kind, obligation.clause_idx
            ))
        };
        let refuted = || {
            MonolithicVerdict::Invalid(format!(
                "{:?} obligation of clause {} is satisfiable",
                obligation.kind, obligation.clause_idx
            ))
        };
        match smt_check_obligation(obligation, timeout) {
            SmtVerdict::Unsat => {}
            SmtVerdict::Refuted => return refuted(),
            SmtVerdict::Undecided => return undecided(),
        }
        // #5381 / #5803: concrete cross-check of the UNSAT answer, under the
        // per-rule validator's rule: Safety obligations always while the
        // budget lasts, the others first ten then one in a hundred.
        concrete_unsat_count += 1;
        let sampled = obligation.kind == ObligationKind::Safety
            || concrete_unsat_count <= CONCRETE_ALWAYS_CHECKED
            || concrete_unsat_count.is_multiple_of(CONCRETE_SAMPLE_PERIOD);
        if sampled && concrete.has_room() {
            match concrete.check(&obligation.body, &obligation.query) {
                ConcreteAnswer::Witness(cex_model) => {
                    tracing::warn!(
                        clause_idx = obligation.clause_idx,
                        ?cex_model,
                        "monolithic validation: SMT said UNSAT but the concrete check found a model (#5381/#5803)"
                    );
                    return refuted();
                }
                // The solve is over: no acceptance on an unfinished check.
                ConcreteAnswer::Interrupted => return closed(),
                ConcreteAnswer::NoWitness => {}
            }
        }
    }
    if boundary.closed() {
        return closed();
    }
    MonolithicVerdict::Valid
}

impl PortfolioSolver {
    /// Monolithic validation of an ALREADY-TRANSLATED Safe model against the
    /// ORIGINAL clauses, or `None` when the original problem is not a
    /// single-predicate fact/transition/query system (see the module docs).
    pub(in crate::portfolio) fn validate_safe_monolithic(
        &self,
        translated_model: &InvariantModel,
    ) -> Option<MonolithicVerdict> {
        let obligations = single_predicate_obligations(&self.original_problem, translated_model)?;
        let profile = accept_profile_enabled();
        let started = ay_core::time::Instant::now();
        let verdict = check_obligations(
            &obligations,
            MONOLITHIC_CHECK_TIMEOUT,
            PassBoundary {
                cancellation: Some(&self.cancellation_token),
                deadline: self.effective_solve_deadline(),
                stopped: || self.construction_boundary_exhausted(),
            },
        );
        if profile {
            safe_eprintln!(
                "[ACCEPT-PROF] monolithic verify dt={:.3}s obligations={} verdict={}",
                started.elapsed().as_secs_f64(),
                obligations.len(),
                match &verdict {
                    MonolithicVerdict::Valid => "valid",
                    MonolithicVerdict::Invalid(_) => "invalid",
                    MonolithicVerdict::Unknown(_) => "unknown",
                }
            );
        }
        Some(verdict)
    }
}
