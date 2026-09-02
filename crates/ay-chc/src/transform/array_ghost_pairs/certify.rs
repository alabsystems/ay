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

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::quote_symbol;

use crate::smt::executor_adapter::{
    collect_uninterpreted_function_declarations_for_exprs, emit_declare_uninterpreted_function,
    sort_to_smtlib, UninterpretedFunctionDeclaration,
};
use crate::smt::{SmtContext, SmtResult};
#[cfg(test)]
use crate::PredicateInterpretation;
use crate::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseHead, HornClause, InvariantModel, PredicateId,
};

use super::{
    collect_index_terms, fresh_index_vars, instantiation_tuples, GhostPairSpec, BODY_INSTANCE_CAP,
    INDEX_TERM_CAP,
};

/// Ceiling for a single clause's discharge budget.
const PER_RULE_BUDGET_CAP: Duration = Duration::from_secs(5);

/// Smallest timeout that can be represented by the millisecond-granularity
/// executor option. Smaller shares fail closed instead of becoming unbounded.
const MIN_EXECUTOR_BUDGET: Duration = Duration::from_millis(1);

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
    /// Per-executor term-store ceiling used by the raw quantified executor.
    /// `AdaptiveConfig::memory_budget` would otherwise reach only the
    /// `SmtContext`-backed discharge round.
    executor_term_memory_limit: Option<usize>,
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
        Self::certify_and_seal_with_term_memory_limit(problem, spec, model, total_budget, None)
    }

    /// As [`Self::certify_and_seal`], while carrying the route's configured
    /// memory envelope into every raw quantified-executor discharge and later
    /// replay of the sealed certificate.
    pub(crate) fn certify_and_seal_with_term_memory_limit(
        problem: &ChcProblem,
        spec: GhostPairSpec,
        model: InvariantModel,
        total_budget: Option<Duration>,
        executor_term_memory_limit: Option<usize>,
    ) -> Option<Arc<Self>> {
        let candidate = Self {
            spec,
            model,
            executor_term_memory_limit,
        };
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

    /// Ghost interpretation retained by this sealed certificate.
    #[cfg(test)]
    pub(crate) fn ghost_interpretation(
        &self,
        pred_id: PredicateId,
    ) -> Option<&PredicateInterpretation> {
        self.model.get(&pred_id)
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
    // The caller's envelope includes structural validation and obligation
    // construction, not only time spent inside the two solver rounds.
    let deadline = total_budget.map(|budget| Instant::now() + budget);

    // Structural gate: every predicate needs an interpretation over exactly
    // the ghost-extended parameter list, with no free non-parameter variables
    // (free variables would be captured by clause variables during
    // substitution, turning discharge queries vacuous).
    for pred in problem.predicates() {
        if deadline.is_some_and(|limit| Instant::now() >= limit) {
            return false;
        }
        let Some(interp) = cert.model.get(&pred.id) else {
            return false;
        };
        let Some(expected_sorts) = cert.spec.extended_sorts(pred.id, &pred.arg_sorts) else {
            return false;
        };
        if interp.vars.len() != expected_sorts.len()
            || interp
                .vars
                .iter()
                .zip(&expected_sorts)
                .any(|(var, expected)| var.sort != *expected)
        {
            return false;
        }
        let mut param_names: FxHashSet<&str> = FxHashSet::default();
        if interp
            .vars
            .iter()
            .any(|var| !param_names.insert(var.name.as_str()))
        {
            return false;
        }
        let params: FxHashSet<ChcVar> = interp.vars.iter().cloned().collect();
        let Some(formula_vars) = certificate_formula_vars(&interp.formula) else {
            return false;
        };
        if formula_vars.iter().any(|var| !params.contains(var)) {
            return false;
        }
        if !matches!(
            crate::pdr::validate_qf_expression(problem, &interp.vars, &interp.formula),
            Ok(crate::ChcSort::Bool)
        ) {
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

    // First classify every rule using only bounded AST/replay construction.
    // Compiler wrapper graphs are dominated by syntactic `I(k) /\ !I(k)`
    // obligations. Removing those before allocating solver shares prevents an
    // early nontrivial init rule from receiving total_budget/all_rules while
    // 99 executor-free wrappers strand the rest of the envelope behind it.
    let mut solver_clauses = Vec::new();
    for clause in clauses {
        let preflight_deadline = match deadline {
            Some(deadline) => deadline,
            None => Instant::now() + PER_RULE_BUDGET_CAP,
        };
        match preclassify_clause(cert, clause, preflight_deadline) {
            Some(true) => {}
            Some(false) => solver_clauses.push(clause),
            None => return false,
        }
    }

    let clause_count = solver_clauses.len();
    for (clause_index, clause) in solver_clauses.into_iter().enumerate() {
        let rule_started = Instant::now();
        let remaining_total = match deadline {
            Some(d) => {
                if rule_started >= d {
                    return false;
                }
                Some(d - rule_started)
            }
            None => None,
        };
        let clauses_remaining = clause_count - clause_index;
        let rule_budget = per_rule_budget(remaining_total, clauses_remaining);
        let rule_deadline = rule_started + rule_budget;
        if rule_budget.is_zero() || !discharge_clause(cert, clause, rule_deadline) {
            return false;
        }
    }
    !deadline.is_some_and(|deadline| Instant::now() >= deadline)
}

/// Divide the remaining envelope fairly among the clauses still waiting.
///
/// Recomputing after every successful clause lets cheap obligations donate
/// their unused share to later ones. There is deliberately no minimum: a
/// small fair share is still a valid opportunity to discharge an easy rule,
/// while the enclosing deadline remains the hard total bound.
pub(super) fn per_rule_budget(
    remaining_total: Option<Duration>,
    clauses_remaining: usize,
) -> Duration {
    match remaining_total {
        None => PER_RULE_BUDGET_CAP,
        Some(remaining) => {
            let divisor = u32::try_from(clauses_remaining.max(1)).unwrap_or(u32::MAX);
            (remaining / divisor).min(PER_RULE_BUDGET_CAP)
        }
    }
}

/// Reserve a bounded executor slice from `remaining`. The executor timeout is
/// expressed in whole milliseconds, so a sub-millisecond slice cannot safely
/// launch a solver round.
pub(super) fn bounded_executor_budget(remaining: Duration, share_divisor: u32) -> Option<Duration> {
    let budget = remaining / share_divisor.max(1);
    (budget >= MIN_EXECUTOR_BUDGET).then_some(budget)
}

fn remaining_until(deadline: Instant) -> Option<Duration> {
    let now = Instant::now();
    (now < deadline).then_some(deadline - now)
}

/// Reserve every ordinary source/model function symbol before allocating
/// certificate skolems or quantified binders. SMT-LIB binders shadow nullary
/// UFs in the term namespace, which would otherwise change the obligation.
fn reserve_global_function_names(
    cert: &GhostPairCertificate,
    clause: &HornClause,
    used: &mut FxHashSet<String>,
) -> Option<()> {
    let mut expressions = Vec::new();
    expressions.extend(clause.body.constraint.iter());
    expressions.extend(
        clause
            .body
            .predicates
            .iter()
            .flat_map(|(_, args)| args.iter()),
    );
    if let ClauseHead::Predicate(_, args) = &clause.head {
        expressions.extend(args);
    }
    expressions.extend(cert.model.iter().map(|(_, interp)| &interp.formula));
    let declarations = collect_uninterpreted_function_declarations_for_exprs(expressions).ok()?;
    for declaration in declarations {
        if !used.insert(declaration.name) {
            return None;
        }
    }
    Some(())
}

/// Collect every variable at the certificate boundary, failing closed instead
/// of accepting the best-effort truncation used by general-purpose `vars()`.
fn certificate_formula_vars(expr: &ChcExpr) -> Option<FxHashSet<ChcVar>> {
    let mut remaining = crate::expr::MAX_PREPROCESSING_NODES;
    let mut vars = FxHashSet::default();
    collect_certificate_vars(expr, 0, &mut remaining, &mut vars)?;
    Some(vars)
}

/// Collect every source-clause variable without the best-effort truncation of
/// `HornClause::vars()`. This boundary must reject deep expressions instead of
/// allowing a generated quantifier to capture an undiscovered source symbol.
pub(super) fn exact_clause_vars(clause: &HornClause) -> Option<Vec<ChcVar>> {
    let mut remaining = crate::expr::MAX_PREPROCESSING_NODES;
    let mut vars = FxHashSet::default();
    let mut expressions = Vec::new();
    expressions.extend(clause.body.constraint.iter());
    expressions.extend(
        clause
            .body
            .predicates
            .iter()
            .flat_map(|(_, args)| args.iter()),
    );
    if let ClauseHead::Predicate(_, args) = &clause.head {
        expressions.extend(args);
    }
    for expression in expressions {
        collect_certificate_vars(expression, 0, &mut remaining, &mut vars)?;
    }

    let mut vars: Vec<ChcVar> = vars.into_iter().collect();
    vars.sort();
    if vars
        .windows(2)
        .any(|pair| pair[0].name == pair[1].name && pair[0].sort != pair[1].sort)
    {
        return None;
    }
    Some(vars)
}

fn collect_certificate_vars(
    expr: &ChcExpr,
    depth: usize,
    remaining: &mut usize,
    vars: &mut FxHashSet<ChcVar>,
) -> Option<()> {
    if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH || *remaining == 0 {
        return None;
    }
    *remaining -= 1;
    crate::expr::maybe_grow_expr_stack(|| {
        match expr {
            ChcExpr::Var(var) => {
                vars.insert(var.clone());
            }
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                for arg in args {
                    collect_certificate_vars(arg, depth + 1, remaining, vars)?;
                }
            }
            ChcExpr::ConstArray(_, value) => {
                collect_certificate_vars(value, depth + 1, remaining, vars)?;
            }
            ChcExpr::Real(_, denominator) if *denominator <= 0 => return None,
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {}
        }
        Some(())
    })
}

/// Parallel variable substitution for certificate discharge. Unlike the
/// general preprocessing substitution, exhaustion rejects the whole rewrite;
/// it can never leave a deep formal parameter available for name capture.
fn certificate_substitute(expr: &ChcExpr, subst: &FxHashMap<&ChcVar, &ChcExpr>) -> Option<ChcExpr> {
    let mut remaining = crate::expr::MAX_PREPROCESSING_NODES;
    substitute_certificate_expr(expr, subst, 0, &mut remaining)
}

fn substitute_certificate_expr(
    expr: &ChcExpr,
    subst: &FxHashMap<&ChcVar, &ChcExpr>,
    depth: usize,
    remaining: &mut usize,
) -> Option<ChcExpr> {
    if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH || *remaining == 0 {
        return None;
    }
    *remaining -= 1;
    crate::expr::maybe_grow_expr_stack(|| {
        Some(match expr {
            ChcExpr::Var(var) => subst
                .get(var)
                .map_or_else(|| expr.clone(), |replacement| (**replacement).clone()),
            ChcExpr::Op(op, args) => ChcExpr::Op(
                *op,
                args.iter()
                    .map(|arg| {
                        substitute_certificate_expr(arg, subst, depth + 1, remaining).map(Arc::new)
                    })
                    .collect::<Option<Vec<_>>>()?,
            ),
            ChcExpr::PredicateApp(name, pred_id, args) => ChcExpr::PredicateApp(
                name.clone(),
                *pred_id,
                args.iter()
                    .map(|arg| {
                        substitute_certificate_expr(arg, subst, depth + 1, remaining).map(Arc::new)
                    })
                    .collect::<Option<Vec<_>>>()?,
            ),
            ChcExpr::FuncApp(name, sort, args) => ChcExpr::FuncApp(
                name.clone(),
                sort.clone(),
                args.iter()
                    .map(|arg| {
                        substitute_certificate_expr(arg, subst, depth + 1, remaining).map(Arc::new)
                    })
                    .collect::<Option<Vec<_>>>()?,
            ),
            ChcExpr::ConstArray(key_sort, value) => ChcExpr::ConstArray(
                key_sort.clone(),
                Arc::new(substitute_certificate_expr(
                    value,
                    subst,
                    depth + 1,
                    remaining,
                )?),
            ),
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => expr.clone(),
        })
    })
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
    let full_args = cert.spec.extend_args(pred_id, args, ghost_idx_terms)?;
    if interp.vars.len() != full_args.len()
        || interp
            .vars
            .iter()
            .zip(&full_args)
            .any(|(var, arg)| var.sort != arg.sort())
    {
        return None;
    }
    let subst: FxHashMap<&ChcVar, &ChcExpr> = interp.vars.iter().zip(&full_args).collect();
    certificate_substitute(&interp.formula, &subst)
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
            let slot_sorts = cert
                .spec
                .preds
                .get(pred_id)
                .map_or_else(Vec::new, |spec| spec.slot_index_sorts(cert.spec.n));
            let fresh = fresh_index_vars("__gpc", &slot_sorts, used);
            let fresh_exprs: Vec<ChcExpr> = fresh.iter().cloned().map(ChcExpr::var).collect();
            let instance = instantiate_interp(cert, *pred_id, args, &fresh_exprs)?;
            Some((Some(ChcExpr::not(instance)), fresh))
        }
        ClauseHead::False => Some((None, Vec::new())),
    }
}

enum PreparedClauseDischarge {
    Discharged,
    RequiresSolver {
        finite_query: ChcExpr,
        quantified_smt: String,
    },
}

/// Detect the compiler-wrapper obligation `I(args) /\ !I(args)` without the
/// general expression simplifier. Hashing the already-built body instances
/// makes this linear in their admitted expression surface and also handles a
/// conjunctive interpretation as one exact term.
fn has_exact_forwarding_contradiction(
    instances: &[ChcExpr],
    head_negation: Option<&ChcExpr>,
) -> bool {
    let Some(ChcExpr::Op(crate::ChcOp::Not, negated_args)) = head_negation else {
        return false;
    };
    let [negated] = negated_args.as_slice() else {
        return false;
    };
    let body_instances: FxHashSet<&ChcExpr> = instances.iter().collect();
    body_instances.contains(negated.as_ref())
}

/// Build and boundedly simplify one original-clause obligation without
/// launching a solver. `None` means structural/resource failure.
fn prepare_clause_discharge(
    cert: &GhostPairCertificate,
    clause: &HornClause,
    deadline: Instant,
) -> Option<PreparedClauseDischarge> {
    if Instant::now() >= deadline {
        return None;
    }
    let cands = collect_index_terms(clause, INDEX_TERM_CAP);
    let clause_vars = exact_clause_vars(clause)?;
    let mut used: FxHashSet<String> = clause_vars.iter().map(|var| var.name.clone()).collect();
    reserve_global_function_names(cert, clause, &mut used)?;

    // Head forall -> fresh skolem constants.
    let (head_negation, fresh_vars) = skolemize_head(cert, clause, &mut used)?;
    let fresh_exprs: Vec<ChcExpr> = fresh_vars.iter().cloned().map(ChcExpr::var).collect();

    // Body foralls -> finite instantiation at clause index terms + skolems.
    let instances = body_instance_conjuncts(cert, clause, &fresh_exprs, &cands)?;
    let mut conjuncts: Vec<ChcExpr> = Vec::new();
    if let Some(constraint) = &clause.body.constraint {
        conjuncts.push(constraint.clone());
    }
    conjuncts.extend(instances.iter().cloned());
    if let Some(head_negation) = head_negation.clone() {
        conjuncts.push(head_negation);
    }
    let query = ChcExpr::and_all(conjuncts);

    if Instant::now() >= deadline {
        return None;
    }

    // Construct the externally replayable quantified obligation before
    // accepting either discharge round. This preflight rejects unsupported
    // sorts, namespace collisions, or incomplete serialization even when the
    // cheaper finite query happens to be UNSAT. Its construction time counts
    // against the absolute per-rule deadline.
    let mut quantified_used = used.clone();
    let quantified_smt = quantified_discharge_smtlib(
        cert,
        clause,
        &clause_vars,
        &fresh_vars,
        head_negation.as_ref(),
        &mut quantified_used,
        &instances,
    )?;

    // Pure forwarding rules commonly produce an exact `I(k) /\ !I(k)` pair.
    // The exact hash-set check avoids paying solver startup per wrapper and
    // covers conjunction-valued interpretations without the general
    // simplifier's wider rewrite surface. Keep this AFTER quantified replay
    // construction: even an easy finite
    // contradiction may seal only if the externally replayable obligation is
    // structurally complete.
    if Instant::now() >= deadline {
        return None;
    }
    if has_exact_forwarding_contradiction(&instances, head_negation.as_ref()) {
        return Some(PreparedClauseDischarge::Discharged);
    }
    Some(PreparedClauseDischarge::RequiresSolver {
        finite_query: query,
        quantified_smt,
    })
}

/// Return `Some(true)` for a bounded syntactic discharge, `Some(false)` when
/// solver work remains, and `None` on structural/resource failure.
fn preclassify_clause(
    cert: &GhostPairCertificate,
    clause: &HornClause,
    deadline: Instant,
) -> Option<bool> {
    prepare_clause_discharge(cert, clause, deadline)
        .map(|prepared| matches!(prepared, PreparedClauseDischarge::Discharged))
}

/// Discharge one nontrivial original clause under the quantified model
/// semantics. Re-preparing after the fast-only scheduling pass is deliberate:
/// retaining every generated formula/string until classification completed
/// would turn a bounded 512-clause input into a second unaccounted corpus-sized
/// memory resident set.
fn discharge_clause(cert: &GhostPairCertificate, clause: &HornClause, deadline: Instant) -> bool {
    let Some(prepared) = prepare_clause_discharge(cert, clause, deadline) else {
        return false;
    };
    let PreparedClauseDischarge::RequiresSolver {
        finite_query,
        quantified_smt,
    } = prepared
    else {
        return true;
    };

    // Round 1: quantifier-free instantiation-based discharge. The query
    // contains select/store terms, so route through the executor fallback
    // (the internal DPLL(T) loop has no array axiomatization and would
    // return Unknown).
    let Some(remaining) = remaining_until(deadline) else {
        return false;
    };
    let Some(round1_budget) = bounded_executor_budget(remaining, 2) else {
        return false;
    };
    let mut smt = SmtContext::new();
    // Rechecks can run after the route's thread-local guard has unwound. Carry
    // the sealed certificate's own budget into both this context and any
    // ay-dpll executor fallback it launches.
    smt.set_term_memory_budget(cert.executor_term_memory_limit);
    if matches!(
        smt.check_sat_with_executor_fallback_timeout(&finite_query, round1_budget),
        SmtResult::Unsat
    ) {
        return Instant::now() <= deadline;
    }

    // Round 2: full quantified SMT check via the ay-dpll executor (explicit
    // forall bodies; the executor has e-matching/MBQI). Recompute the budget
    // after round 1 so parser, construction, and solver time cannot borrow
    // beyond this rule's absolute deadline.
    let verdict = crate::smt::executor_adapter::smtlib_first_verdict_via_executor_until(
        &quantified_smt,
        deadline,
        cert.executor_term_memory_limit,
    );
    verdict.as_deref() == Some("unsat") && Instant::now() <= deadline
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
        let slot_sorts = cert
            .spec
            .preds
            .get(pred_id)
            .map_or_else(Vec::new, |spec| spec.slot_index_sorts(cert.spec.n));
        if slot_sorts.is_empty() {
            conjuncts.push(instantiate_interp(cert, *pred_id, args, &[])?);
            continue;
        }
        let tuples = instantiation_tuples(&slot_sorts, fresh_exprs, cands, BODY_INSTANCE_CAP);
        if tuples.is_empty() {
            return None;
        }
        for tuple in tuples {
            conjuncts.push(instantiate_interp(cert, *pred_id, args, &tuple)?);
        }
    }
    Some(conjuncts)
}

/// Reconstruct the ordinary UF declarations shared by one replay obligation.
fn replay_uf_declarations(
    cert: &GhostPairCertificate,
    clause: &HornClause,
    clause_vars: &[ChcVar],
    fresh_vars: &[ChcVar],
    head_negation: Option<&ChcExpr>,
    instance_hints: &[ChcExpr],
) -> Option<Vec<UninterpretedFunctionDeclaration>> {
    let declarations = collect_uninterpreted_function_declarations_for_exprs(
        clause
            .body
            .constraint
            .iter()
            .chain(
                clause
                    .body
                    .predicates
                    .iter()
                    .flat_map(|(_, args)| args.iter()),
            )
            .chain(head_negation)
            .chain(instance_hints)
            .chain(cert.model.iter().map(|(_, interp)| &interp.formula)),
    )
    .ok()?;
    if declarations.iter().any(|declaration| {
        clause_vars
            .iter()
            .chain(fresh_vars)
            .any(|var| var.name == declaration.name)
    }) {
        return None;
    }
    Some(declarations)
}

fn quantified_body_instances(
    cert: &GhostPairCertificate,
    clause: &HornClause,
    used: &mut FxHashSet<String>,
) -> Option<Vec<(Vec<ChcVar>, ChcExpr)>> {
    let mut instances = Vec::with_capacity(clause.body.predicates.len());
    for (pred_id, args) in &clause.body.predicates {
        let slot_sorts = cert
            .spec
            .preds
            .get(pred_id)
            .map_or_else(Vec::new, |spec| spec.slot_index_sorts(cert.spec.n));
        let bound = fresh_index_vars("__gpb", &slot_sorts, used);
        let bound_exprs: Vec<ChcExpr> = bound.iter().cloned().map(ChcExpr::var).collect();
        let instance = instantiate_interp(cert, *pred_id, args, &bound_exprs)?;
        instances.push((bound, instance));
    }
    Some(instances)
}

fn emit_quantified_body_instances(smt: &mut String, body_instances: &[(Vec<ChcVar>, ChcExpr)]) {
    for (bound, instance) in body_instances {
        if bound.is_empty() {
            smt.push_str(&format!(
                "(assert {})\n",
                InvariantModel::expr_to_smtlib(instance)
            ));
            continue;
        }
        let binders: Vec<String> = bound
            .iter()
            .map(|var| {
                format!(
                    "({} {})",
                    quote_symbol(&var.name),
                    sort_to_smtlib(&var.sort)
                )
            })
            .collect();
        smt.push_str(&format!(
            "(assert (forall ({}) {}))\n",
            binders.join(" "),
            InvariantModel::expr_to_smtlib(instance)
        ));
    }
}

/// Render the fully quantified discharge query for one clause as standalone
/// SMT-LIB. The query must be UNSAT exactly when the quantified model satisfies
/// the clause. `instance_hints` are additional premises that must each be a
/// consequence of the quantified body hypotheses (e.g. the round-1 finite
/// instantiations): asserting them keeps the query logically equivalent while
/// giving solvers with weak quantifier instantiation a concrete foothold.
/// Returns `None` when the certificate does not structurally cover a body
/// atom (fail-closed at the caller).
fn quantified_discharge_smtlib(
    cert: &GhostPairCertificate,
    clause: &HornClause,
    clause_vars: &[ChcVar],
    fresh_vars: &[ChcVar],
    head_negation: Option<&ChcExpr>,
    used: &mut FxHashSet<String>,
    instance_hints: &[ChcExpr],
) -> Option<String> {
    let mut smt = String::with_capacity(2048);
    smt.push_str("(set-logic ALL)\n");

    // `FuncApp` retains the typed application but not its original SMT-LIB
    // declaration.  Reconstruct every ordinary UF used by either the source
    // clause or the sealed interpretation before emitting assertions.  A
    // conflicting typed signature makes this proof obligation unavailable.
    let declarations = replay_uf_declarations(
        cert,
        clause,
        clause_vars,
        fresh_vars,
        head_negation,
        instance_hints,
    )?;
    used.extend(
        declarations
            .iter()
            .map(|declaration| declaration.name.clone()),
    );

    // Allocate every body binder and instantiate its interpretation before
    // emitting declarations. Expression-local sort annotations (notably
    // const arrays) must contribute their uninterpreted sorts to the header.
    let body_instances = quantified_body_instances(cert, clause, used)?;
    let mut emitted_expressions = Vec::new();
    emitted_expressions.extend(clause.body.constraint.iter());
    emitted_expressions.extend(head_negation);
    emitted_expressions.extend(instance_hints);
    emitted_expressions.extend(cert.model.iter().map(|(_, interp)| &interp.formula));
    emitted_expressions.extend(body_instances.iter().map(|(_, instance)| instance));

    for sort_name in certificate_uninterpreted_sort_names(
        cert,
        clause_vars,
        fresh_vars,
        &declarations,
        &emitted_expressions,
    )? {
        smt.push_str(&format!("(declare-sort {} 0)\n", quote_symbol(&sort_name)));
    }
    for declaration in &declarations {
        smt.push_str(&emit_declare_uninterpreted_function(declaration));
    }

    // Free constants: original clause variables + head skolems.
    for var in clause_vars.iter().chain(fresh_vars.iter()) {
        smt.push_str(&format!(
            "(declare-const {} {})\n",
            quote_symbol(&var.name),
            sort_to_smtlib(&var.sort)
        ));
    }

    if let Some(constraint) = &clause.body.constraint {
        smt.push_str(&format!(
            "(assert {})\n",
            InvariantModel::expr_to_smtlib(constraint)
        ));
    }

    emit_quantified_body_instances(&mut smt, &body_instances);

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

fn certificate_uninterpreted_sort_names(
    cert: &GhostPairCertificate,
    clause_vars: &[ChcVar],
    fresh_vars: &[ChcVar],
    declarations: &[UninterpretedFunctionDeclaration],
    expressions: &[&ChcExpr],
) -> Option<Vec<String>> {
    let mut names = Vec::new();
    for sort in clause_vars
        .iter()
        .chain(fresh_vars)
        .map(|var| &var.sort)
        .chain(
            cert.model
                .iter()
                .flat_map(|(_, interp)| interp.vars.iter().map(|var| &var.sort)),
        )
        .chain(declarations.iter().flat_map(|declaration| {
            declaration
                .argument_sorts
                .iter()
                .chain(std::iter::once(&declaration.return_sort))
        }))
    {
        collect_uninterpreted_sort_names(sort, &mut names)?;
    }
    let mut remaining = crate::expr::MAX_PREPROCESSING_NODES;
    for expression in expressions {
        collect_expression_uninterpreted_sort_names(expression, 0, &mut remaining, &mut names)?;
    }
    names.sort();
    names.dedup();
    Some(names)
}

fn collect_expression_uninterpreted_sort_names(
    expr: &ChcExpr,
    depth: usize,
    remaining: &mut usize,
    names: &mut Vec<String>,
) -> Option<()> {
    if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH || *remaining == 0 {
        return None;
    }
    *remaining -= 1;
    crate::expr::maybe_grow_expr_stack(|| {
        match expr {
            ChcExpr::Var(var) => collect_uninterpreted_sort_names(&var.sort, names)?,
            ChcExpr::FuncApp(_, sort, args) => {
                collect_uninterpreted_sort_names(sort, names)?;
                for arg in args {
                    collect_expression_uninterpreted_sort_names(arg, depth + 1, remaining, names)?;
                }
            }
            ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => {
                for arg in args {
                    collect_expression_uninterpreted_sort_names(arg, depth + 1, remaining, names)?;
                }
            }
            ChcExpr::ConstArray(key_sort, value) => {
                collect_uninterpreted_sort_names(key_sort, names)?;
                collect_expression_uninterpreted_sort_names(value, depth + 1, remaining, names)?;
            }
            ChcExpr::ConstArrayMarker(sort) => collect_uninterpreted_sort_names(sort, names)?,
            ChcExpr::Real(_, denominator) if *denominator <= 0 => return None,
            ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::IsTesterMarker(_) => {}
        }
        Some(())
    })
}

fn collect_uninterpreted_sort_names(sort: &ChcSort, names: &mut Vec<String>) -> Option<()> {
    match sort {
        ChcSort::Uninterpreted(name) => {
            // The shared expression serializer still renders const-array
            // annotations with `ChcSort::Display`. Reject names that require
            // quoting until that general serializer boundary is sort-aware.
            if quote_symbol(name) != *name || is_predeclared_sort_name(name) {
                return None;
            }
            names.push(name.clone());
        }
        ChcSort::Array(key, value) => {
            collect_uninterpreted_sort_names(key, names)?;
            collect_uninterpreted_sort_names(value, names)?;
        }
        ChcSort::Datatype { .. } => return None,
        ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_) => {}
    }
    Some(())
}

fn is_predeclared_sort_name(name: &str) -> bool {
    matches!(
        name,
        "Array"
            | "Bag"
            | "BitVec"
            | "Bool"
            | "Char"
            | "Float16"
            | "Float32"
            | "Float64"
            | "Float128"
            | "FloatingPoint"
            | "Int"
            | "Real"
            | "RegLan"
            | "RoundingMode"
            | "Seq"
            | "Set"
            | "String"
    )
}

/// Standalone SMT-LIB replay obligations for a sealed ghost-pair certificate.
///
/// One obligation per ORIGINAL clause, each the same fully quantified
/// discharge query [`quantified_discharge_smtlib`] builds in-process during
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
            let clause_vars = exact_clause_vars(clause).ok_or_else(structural_error)?;
            let mut used: FxHashSet<String> =
                clause_vars.iter().map(|var| var.name.clone()).collect();
            reserve_global_function_names(cert, clause, &mut used).ok_or_else(structural_error)?;
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
                &clause_vars,
                &fresh_vars,
                head_negation.as_ref(),
                &mut used,
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
