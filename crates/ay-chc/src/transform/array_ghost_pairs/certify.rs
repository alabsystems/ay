// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Quantified certification of ghost-pair models on the ORIGINAL clauses.
//!
//! A ghost-pair `Safe` verdict claims the quantified model
//! `Q_P(args) := forall i_1..i_m. I'(args, i_s, select(arr_s, i_s))` solves the
//! original CHC system. `ChcExpr` has no quantifier node, so this module
//! discharges each original clause directly (agenda #16 gating):
//!
//! For a clause `phi ∧ B_1 ∧ .. ∧ B_k ⇒ H`:
//! - the head `forall` is skolemized: fresh constants `f_s` replace the bound
//!   indices (sound AND complete for a top-level `forall` conclusion),
//! - each body `forall` hypothesis is INSTANTIATED at every index term
//!   occurring in the clause plus the fresh head symbols (a sound weakening of
//!   the hypothesis: proving the implication from instances proves it from
//!   the full `forall`),
//! - the resulting quantifier-free query
//!   `phi ∧ instances ∧ ¬head_instance` must be UNSAT,
//! - if the instantiation round cannot prove it, a FULL quantified SMT check
//!   (explicit `forall` assertions through the ay-dpll executor, which has
//!   e-matching/MBQI quantifier instantiation) runs as fallback,
//! - anything else (SAT / Unknown / timeout / structural mismatch) fails the
//!   certification ⇒ the caller withholds the verdict (fail-closed).
//!
//! [`GhostPairCertificate`] is construction-sealed: the ONLY way to obtain one
//! is [`GhostPairCertificate::certify_and_seal`], which runs the full per-rule
//! discharge above on every original clause.

use std::sync::Arc;
use std::time::Duration;
// The workspace-wide monotonic clock shim (#wasm port): byte-identical to
// `std::time::Instant` on native targets, host-clock-backed on wasm32 (raw
// `std::time::Instant` panics there and breaks the wasm build).
use ay_core::time::Instant;

use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::quote_symbol;

use crate::smt::{SmtContext, SmtResult};
use crate::{ChcExpr, ChcProblem, ChcVar, ClauseHead, HornClause, InvariantModel, PredicateId};

use super::{
    collect_index_terms, fresh_int_vars, instantiation_tuples, GhostPairSpec, BODY_INSTANCE_CAP,
    INDEX_TERM_CAP,
};

/// Ceiling for a single clause's discharge budget.
const PER_RULE_BUDGET_CAP: Duration = Duration::from_secs(5);

/// Floor for a single clause's discharge budget: below this the SMT checks
/// cannot realistically finish, so certification fails closed anyway.
const PER_RULE_BUDGET_FLOOR: Duration = Duration::from_millis(100);

/// Sealed quantified array-invariant certificate.
///
/// Holds the quantifier-free PDR model over the ghost-extended signature plus
/// the ghost layout; together they denote the quantified original model
/// `forall i. I'(args, i, select(arr, i))`. Construction requires passing the
/// full per-rule discharge on the ORIGINAL clauses (`certify_and_seal`).
#[derive(Debug, Clone)]
pub(crate) struct GhostPairCertificate {
    spec: GhostPairSpec,
    model: InvariantModel,
}

impl GhostPairCertificate {
    /// Run the full quantified per-rule discharge of `model` (over the
    /// ghost-extended signature described by `spec`) against every clause of
    /// the ORIGINAL `problem`. Returns a sealed certificate only when every
    /// clause is discharged; any failure returns `None` (fail-closed).
    pub(crate) fn certify_and_seal(
        problem: &ChcProblem,
        spec: GhostPairSpec,
        model: InvariantModel,
        total_budget: Option<Duration>,
    ) -> Option<Arc<Self>> {
        let candidate = Self { spec, model };
        if discharge_all(problem, &candidate, total_budget, false) {
            Some(Arc::new(candidate))
        } else {
            None
        }
    }

    /// Number of ghost pairs per instrumented array argument.
    #[cfg(test)]
    pub(crate) fn ghost_pairs_per_array(&self) -> usize {
        self.spec.n
    }
}

/// Re-run the quantified discharge of a sealed certificate.
///
/// `query_only = true` checks only query/safety clauses (the runner's
/// excludes-error gate); `false` re-checks every clause. Fail-closed: any
/// undischarged clause returns `false`.
pub(crate) fn recheck_ghost_pair_certificate(
    problem: &ChcProblem,
    certificate: &GhostPairCertificate,
    total_budget: Option<Duration>,
    query_only: bool,
) -> bool {
    discharge_all(problem, certificate, total_budget, query_only)
}

fn discharge_all(
    problem: &ChcProblem,
    cert: &GhostPairCertificate,
    total_budget: Option<Duration>,
    query_only: bool,
) -> bool {
    // Structural gate: every predicate needs an interpretation over exactly
    // the ghost-extended parameter list, with no free non-parameter variables
    // (free variables would be captured by clause variables during
    // substitution, turning discharge queries vacuous).
    for pred in problem.predicates() {
        let Some(interp) = cert.model.get(&pred.id) else {
            return false;
        };
        let slots = cert
            .spec
            .preds
            .get(&pred.id)
            .map_or(0, |s| s.slots(cert.spec.n));
        if interp.vars.len() != pred.arity() + 2 * slots {
            return false;
        }
        let params: FxHashSet<&str> = interp.vars.iter().map(|v| v.name.as_str()).collect();
        if interp
            .formula
            .vars()
            .iter()
            .any(|v| !params.contains(v.name.as_str()))
        {
            return false;
        }
    }

    let clauses: Vec<&HornClause> = problem
        .clauses()
        .iter()
        .filter(|clause| !query_only || clause.is_query())
        .collect();
    if clauses.is_empty() {
        // A CHC problem with no (query) clauses has nothing to discharge only
        // when it genuinely has no clauses at all; a missing query clause on a
        // nonempty problem is fine (nothing to violate).
        return !query_only || problem.clauses().iter().all(|c| !c.is_query());
    }

    let deadline = total_budget.map(|b| Instant::now() + b);
    let per_rule = per_rule_budget(total_budget, clauses.len());
    if per_rule < PER_RULE_BUDGET_FLOOR {
        return false;
    }

    for clause in clauses {
        let remaining = match deadline {
            Some(d) => {
                let now = Instant::now();
                if now >= d {
                    return false;
                }
                per_rule.min(d - now)
            }
            None => per_rule,
        };
        if !discharge_clause(cert, clause, remaining) {
            return false;
        }
    }
    true
}

fn per_rule_budget(total: Option<Duration>, clause_count: usize) -> Duration {
    match total {
        None => PER_RULE_BUDGET_CAP,
        Some(total) => (total / clause_count.max(1) as u32).min(PER_RULE_BUDGET_CAP),
    }
}

/// Instantiate the certificate's interpretation of `pred_id` applied to
/// `args`, probing the ghost slots at `ghost_idx_terms`.
fn instantiate_interp(
    cert: &GhostPairCertificate,
    pred_id: PredicateId,
    args: &[ChcExpr],
    ghost_idx_terms: &[ChcExpr],
) -> Option<ChcExpr> {
    let interp = cert.model.get(&pred_id)?;
    let full_args = cert.spec.extend_args(pred_id, args, ghost_idx_terms);
    if interp.vars.len() != full_args.len() {
        return None;
    }
    let subst: Vec<(ChcVar, ChcExpr)> = interp.vars.iter().cloned().zip(full_args).collect();
    Some(interp.formula.substitute(&subst))
}

/// Skolemize the head `forall` of one original clause: fresh constants
/// replace the bound ghost indices (sound AND complete for a top-level
/// `forall` conclusion). Returns the negated skolemized head instance (`None`
/// for `false` heads) plus the fresh skolem variables, or `None` when the
/// certificate does not structurally cover the head predicate.
fn skolemize_head(
    cert: &GhostPairCertificate,
    clause: &HornClause,
    used: &mut FxHashSet<String>,
) -> Option<(Option<ChcExpr>, Vec<ChcVar>)> {
    match &clause.head {
        ClauseHead::Predicate(pred_id, args) => {
            let slots = cert
                .spec
                .preds
                .get(pred_id)
                .map_or(0, |s| s.slots(cert.spec.n));
            let fresh = fresh_int_vars("__gpc", slots, used);
            let fresh_exprs: Vec<ChcExpr> = fresh.iter().cloned().map(ChcExpr::var).collect();
            let instance = instantiate_interp(cert, *pred_id, args, &fresh_exprs)?;
            Some((Some(ChcExpr::not(instance)), fresh))
        }
        ClauseHead::False => Some((None, Vec::new())),
    }
}

/// Discharge one original clause under the quantified model semantics.
fn discharge_clause(cert: &GhostPairCertificate, clause: &HornClause, budget: Duration) -> bool {
    let cands = collect_index_terms(clause, INDEX_TERM_CAP);
    let mut used: FxHashSet<String> = clause.vars().into_iter().map(|v| v.name).collect();

    // Head forall -> fresh skolem constants.
    let Some((head_negation, fresh_vars)) = skolemize_head(cert, clause, &mut used) else {
        return false;
    };
    let fresh_exprs: Vec<ChcExpr> = fresh_vars.iter().cloned().map(ChcExpr::var).collect();

    // Body foralls -> finite instantiation at clause index terms + skolems.
    let Some(instances) = body_instance_conjuncts(cert, clause, &fresh_exprs, &cands) else {
        return false;
    };
    let mut conjuncts: Vec<ChcExpr> = Vec::new();
    if let Some(constraint) = &clause.body.constraint {
        conjuncts.push(constraint.clone());
    }
    conjuncts.extend(instances);
    if let Some(head_negation) = head_negation.clone() {
        conjuncts.push(head_negation);
    }
    let query = ChcExpr::and_all(conjuncts);

    // Round 1: quantifier-free instantiation-based discharge. The query
    // contains select/store terms, so route through the executor fallback
    // (the internal DPLL(T) loop has no array axiomatization and would
    // return Unknown).
    let round1 = budget / 2;
    if !round1.is_zero() {
        let mut smt = SmtContext::new();
        if matches!(
            smt.check_sat_with_executor_fallback_timeout(&query, round1),
            SmtResult::Unsat
        ) {
            return true;
        }
    }

    // Round 2: full quantified SMT check via the ay-dpll executor
    // (explicit forall bodies; the executor has e-matching/MBQI).
    quantified_clause_discharge(
        cert,
        clause,
        &fresh_vars,
        head_negation.as_ref(),
        &mut used,
        budget / 2,
    )
}

/// Finite instantiation of every ghost-carrying body atom at the clause's
/// index terms + head skolems (the round-1 premises). Each instance is a
/// consequence of the corresponding `forall` hypothesis, so the returned
/// conjuncts are a sound weakening of the quantified body. `None` when the
/// certificate does not structurally cover a body atom.
fn body_instance_conjuncts(
    cert: &GhostPairCertificate,
    clause: &HornClause,
    fresh_exprs: &[ChcExpr],
    cands: &[ChcExpr],
) -> Option<Vec<ChcExpr>> {
    let mut conjuncts: Vec<ChcExpr> = Vec::new();
    for (pred_id, args) in &clause.body.predicates {
        let slots = cert
            .spec
            .preds
            .get(pred_id)
            .map_or(0, |s| s.slots(cert.spec.n));
        if slots == 0 {
            conjuncts.push(instantiate_interp(cert, *pred_id, args, &[])?);
            continue;
        }
        for tuple in instantiation_tuples(slots, fresh_exprs, cands, BODY_INSTANCE_CAP) {
            conjuncts.push(instantiate_interp(cert, *pred_id, args, &tuple)?);
        }
    }
    Some(conjuncts)
}

/// Build and run the fully quantified discharge query for one clause:
/// clause constraint + `(forall (bound..) body-interpretation-instance)` per
/// ghost-carrying body atom + negated skolemized head instance. Returns `true`
/// only on a literal executor `unsat`.
fn quantified_clause_discharge(
    cert: &GhostPairCertificate,
    clause: &HornClause,
    fresh_vars: &[ChcVar],
    head_negation: Option<&ChcExpr>,
    used: &mut FxHashSet<String>,
    budget: Duration,
) -> bool {
    if budget.is_zero() {
        return false;
    }

    let timeout_ms = budget.as_millis();
    let timeout_ms = (timeout_ms > 0 && timeout_ms < u128::from(u64::MAX)).then_some(timeout_ms);
    let Some(smt) = quantified_discharge_smtlib(
        cert,
        clause,
        fresh_vars,
        head_negation,
        used,
        timeout_ms,
        &[],
    ) else {
        return false;
    };

    crate::smt::executor_adapter::check_unsat_smtlib_via_executor(&smt)
}

/// Render the fully quantified discharge query for one clause as standalone
/// SMT-LIB (see [`quantified_clause_discharge`] for the construction). The
/// query must be UNSAT exactly when the quantified model satisfies the
/// clause. `instance_hints` are additional premises that must each be a
/// consequence of the quantified body hypotheses (e.g. the round-1 finite
/// instantiations): asserting them keeps the query logically equivalent while
/// giving solvers with weak quantifier instantiation a concrete foothold.
/// Returns `None` when the certificate does not structurally cover a body
/// atom (fail-closed at the caller).
fn quantified_discharge_smtlib(
    cert: &GhostPairCertificate,
    clause: &HornClause,
    fresh_vars: &[ChcVar],
    head_negation: Option<&ChcExpr>,
    used: &mut FxHashSet<String>,
    timeout_ms: Option<u128>,
    instance_hints: &[ChcExpr],
) -> Option<String> {
    let mut smt = String::with_capacity(2048);
    smt.push_str("(set-logic ALL)\n");
    if let Some(timeout_ms) = timeout_ms {
        smt.push_str(&format!("(set-option :timeout {timeout_ms})\n"));
    }

    // Free constants: original clause variables + head skolems.
    for var in clause.vars().iter().chain(fresh_vars.iter()) {
        smt.push_str(&format!(
            "(declare-const {} {})\n",
            quote_symbol(&var.name),
            var.sort
        ));
    }

    if let Some(constraint) = &clause.body.constraint {
        smt.push_str(&format!(
            "(assert {})\n",
            InvariantModel::expr_to_smtlib(constraint)
        ));
    }

    for (pred_id, args) in &clause.body.predicates {
        let slots = cert
            .spec
            .preds
            .get(pred_id)
            .map_or(0, |s| s.slots(cert.spec.n));
        if slots == 0 {
            let instance = instantiate_interp(cert, *pred_id, args, &[])?;
            smt.push_str(&format!(
                "(assert {})\n",
                InvariantModel::expr_to_smtlib(&instance)
            ));
            continue;
        }
        let bound = fresh_int_vars("__gpb", slots, used);
        let bound_exprs: Vec<ChcExpr> = bound.iter().cloned().map(ChcExpr::var).collect();
        let instance = instantiate_interp(cert, *pred_id, args, &bound_exprs)?;
        let binders: Vec<String> = bound
            .iter()
            .map(|v| format!("({} Int)", quote_symbol(&v.name)))
            .collect();
        smt.push_str(&format!(
            "(assert (forall ({}) {}))\n",
            binders.join(" "),
            InvariantModel::expr_to_smtlib(&instance)
        ));
    }

    if !instance_hints.is_empty() {
        smt.push_str(
            "; redundant finite instantiations of the forall hypotheses above\n\
             ; (each is a consequence of them; they only help instantiation)\n",
        );
        for hint in instance_hints {
            smt.push_str(&format!(
                "(assert {})\n",
                InvariantModel::expr_to_smtlib(hint)
            ));
        }
    }

    if let Some(head_negation) = head_negation {
        smt.push_str(&format!(
            "(assert {})\n",
            InvariantModel::expr_to_smtlib(head_negation)
        ));
    }
    smt.push_str("(check-sat)\n");
    Some(smt)
}

/// Standalone SMT-LIB replay obligations for a sealed ghost-pair certificate.
///
/// One obligation per ORIGINAL clause, each the same fully quantified
/// discharge query [`quantified_clause_discharge`] runs in-process during
/// `certify_and_seal`: clause constraint + one `forall`-quantified
/// interpretation instance per ghost-carrying body atom + the negated
/// skolemized head instance. Every obligation must be UNSAT for the
/// quantified model `forall i. I'(args, i, select(arr, i))` to solve the
/// original system, so the set is externally checkable by any SMT solver
/// (the standard replay contract). The round-1 finite instantiations are
/// additionally asserted as redundant hints (each is a consequence of the
/// `forall` hypotheses) so external solvers with weak quantifier
/// instantiation can still discharge the query.
///
/// Sealing already discharged every clause: the instantiation round proves a
/// weakening of these premises, so a sealed certificate guarantees each
/// emitted query is genuinely UNSAT. Fail-closed: a clause the certificate
/// does not structurally cover is a verification error (sealed certificates
/// cannot hit this; it guards against model/problem mismatch).
pub(crate) fn ghost_pair_replay_obligations(
    problem: &ChcProblem,
    cert: &GhostPairCertificate,
) -> crate::ChcResult<Vec<crate::ChcReplayObligation>> {
    use std::fmt::Write;

    use crate::{ChcError, ChcReplayObligation, ChcReplayObligationKind};

    problem
        .clauses()
        .iter()
        .enumerate()
        .map(|(clause_index, clause)| {
            let structural_error = || {
                ChcError::Verification(format!(
                    "ghost-pair certificate does not cover clause {clause_index}"
                ))
            };
            let mut used: FxHashSet<String> = clause.vars().into_iter().map(|v| v.name).collect();
            let (head_negation, fresh_vars) =
                skolemize_head(cert, clause, &mut used).ok_or_else(structural_error)?;
            let fresh_exprs: Vec<ChcExpr> = fresh_vars.iter().cloned().map(ChcExpr::var).collect();
            let cands = collect_index_terms(clause, INDEX_TERM_CAP);
            let instance_hints = body_instance_conjuncts(cert, clause, &fresh_exprs, &cands)
                .ok_or_else(structural_error)?;
            let kind = match &clause.head {
                ClauseHead::Predicate(..) if clause.body.predicates.is_empty() => {
                    ChcReplayObligationKind::Initiation
                }
                ClauseHead::Predicate(..) => ChcReplayObligationKind::Consecution,
                ClauseHead::False => ChcReplayObligationKind::Safety,
            };
            let name = format!("clause-{clause_index}-{}", kind.as_str());

            let mut smtlib = String::new();
            let _ = writeln!(smtlib, "; AY CHC certificate replay obligation: {name}");
            let _ = writeln!(smtlib, "; kind: {}", kind.as_str());
            let _ = writeln!(smtlib, "; clause: {clause_index}");
            let _ = writeln!(
                smtlib,
                "; quantified array-invariant (ghost-pair) discharge; expected: unsat"
            );
            let body = quantified_discharge_smtlib(
                cert,
                clause,
                &fresh_vars,
                head_negation.as_ref(),
                &mut used,
                None,
                &instance_hints,
            )
            .ok_or_else(structural_error)?;
            smtlib.push_str(&body);
            Ok(ChcReplayObligation {
                name,
                kind,
                clause_index,
                smtlib,
            })
        })
        .collect()
}
