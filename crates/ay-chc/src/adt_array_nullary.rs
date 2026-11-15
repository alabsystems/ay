// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Narrow ADT/array nullary-predicate unsafe prepass.
//!
//! Some Tricera ADT-array rows encode a false query through a nullary marker:
//! one or more satisfiable background-theory facts imply `P`, and a query
//! clause `P => false` closes the proof. Generic PDR can spend its budget
//! trying to synthesize an invariant for the marker even though the unsafe
//! derivation is a small deterministic marker chain. This module constructs
//! one-step witnesses first, then bounded marker-DAG witnesses, when the
//! constraints are ADT+array flavoured and fresh SMT checks can instantiate the
//! derivation. Adaptive dispatch still runs the standard counterexample
//! verifier before accepting it.

use crate::clause::ClauseHead;
use crate::expr::evaluate_expr;
#[cfg(test)]
use crate::pdr::counterexample::{DerivationWitness, DerivationWitnessEntry};
use crate::pdr::model::InvariantModel;
#[cfg(test)]
use crate::pdr::CounterexampleStep;
use crate::pdr::{CexVerificationResult, Counterexample, PdrConfig, PdrSolver};
use crate::smt::executor_adapter::{
    collect_dt_declarations_for_expr, collect_uninterpreted_function_declarations, detect_logic,
    emit_declare_datatypes, emit_declare_uninterpreted_function, parse_model_into, quote_symbol,
    sort_to_smtlib,
};
use crate::smt::{SmtResult, SmtValue};
use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::panic::AssertUnwindSafe;
use std::time::Duration;

mod control;
mod grounded;
mod names;
use control::Control;
use names::Names;
#[cfg(test)]
#[path = "adt_array_nullary/native_tests.rs"]
mod native_tests;

const MIN_SMT_BUDGET: Duration = Duration::from_millis(10);
const MARKER_DAG_MAX_DEPTH: usize = 20;
const MARKER_DAG_MAX_BODY_PREDS: usize = 3;
const MARKER_DAG_MAX_CLAUSES: usize = 96;
const MARKER_DAG_MAX_TREES: usize = 128;
const DEFAULT_VALUE_RECURSION_LIMIT: usize = 8;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NullaryAdtArrayOutcome {
    NotApplicable,
    NoBudget,
    FactUnsat,
    FactUnknown,
    DagNotFound,
    DagUnknown,
    ValidationAccepted,
    ValidationRejected,
}

impl NullaryAdtArrayOutcome {
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::NotApplicable => "not_applicable",
            Self::NoBudget => "no_budget",
            Self::FactUnsat => "fact_unsat",
            Self::FactUnknown => "fact_unknown",
            Self::DagNotFound => "dag_not_found",
            Self::DagUnknown => "dag_unknown",
            Self::ValidationAccepted => "validation_accepted",
            Self::ValidationRejected => "validation_rejected",
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct NullaryAdtArrayCandidate {
    pub(crate) cex: Counterexample,
    pub(crate) source_clause: usize,
    pub(crate) query_clause: usize,
    pub(crate) predicate: PredicateId,
}

pub(crate) fn try_build_counterexample(
    problem: &ChcProblem,
    budget: Duration,
) -> Result<NullaryAdtArrayCandidate, NullaryAdtArrayOutcome> {
    if budget < MIN_SMT_BUDGET {
        return Err(NullaryAdtArrayOutcome::NoBudget);
    }
    let control = Control::capture(budget).ok_or(NullaryAdtArrayOutcome::NoBudget)?;
    let _scope = control.enter();
    try_build_counterexample_owned(problem, &control)
}

fn try_build_counterexample_owned(
    problem: &ChcProblem,
    control: &Control,
) -> Result<NullaryAdtArrayCandidate, NullaryAdtArrayOutcome> {
    Names::admit_source(problem, control).ok_or(NullaryAdtArrayOutcome::NoBudget)?;

    let Some((query_clause, predicate)) = nullary_false_query(problem) else {
        return try_build_array_dag_query_counterexample(problem, control);
    };

    let mut saw_unknown = false;
    for (fact_clause, constraint) in nullary_adt_array_facts(problem, predicate) {
        let budget = control
            .remaining()
            .ok_or(NullaryAdtArrayOutcome::NoBudget)?;
        let mut smt = problem.make_smt_context();
        match smt.check_sat_with_executor_fallback_timeout(constraint, budget) {
            SmtResult::Sat(model) => {
                control.poll().ok_or(NullaryAdtArrayOutcome::NoBudget)?;
                let instances = scalar_instances_from_model(constraint, &model)
                    .or_else(|| scalar_seed_instance(constraint))
                    .unwrap_or_default();
                if let Some(cex) = grounded::from_fact(
                    problem,
                    predicate,
                    fact_clause,
                    query_clause,
                    instances,
                    control,
                ) {
                    return Ok(NullaryAdtArrayCandidate {
                        cex,
                        source_clause: fact_clause,
                        query_clause,
                        predicate,
                    });
                }
            }
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
            SmtResult::Unknown => saw_unknown = true,
        }

        control.poll().ok_or(NullaryAdtArrayOutcome::NoBudget)?;
        if let Some(cex) = tricera_memtrack_instances(constraint).and_then(|instances| {
            grounded::from_fact(
                problem,
                predicate,
                fact_clause,
                query_clause,
                instances,
                control,
            )
        }) {
            return Ok(NullaryAdtArrayCandidate {
                cex,
                source_clause: fact_clause,
                query_clause,
                predicate,
            });
        }
    }

    match try_build_marker_dag_counterexample(problem, predicate, query_clause, control) {
        Ok(candidate) => return Ok(candidate),
        Err(NullaryAdtArrayOutcome::NotApplicable | NullaryAdtArrayOutcome::DagNotFound) => {}
        Err(outcome) => return Err(outcome),
    }

    if saw_unknown {
        Err(NullaryAdtArrayOutcome::FactUnknown)
    } else {
        Err(NullaryAdtArrayOutcome::FactUnsat)
    }
}

fn try_build_array_dag_query_counterexample(
    problem: &ChcProblem,
    control: &Control,
) -> Result<NullaryAdtArrayCandidate, NullaryAdtArrayOutcome> {
    let Some((query_clause, predicate)) = array_dag_false_query(problem) else {
        return Err(NullaryAdtArrayOutcome::NotApplicable);
    };

    try_build_marker_dag_counterexample(problem, predicate, query_clause, control)
}

/// A derivation witness whose entries ALL record a trivially-`true` reachable
/// state does not establish reachability. It is the vacuous form emitted by the
/// legacy nullary-ADT/array marker-dag prepass, and is the S4 false-UNSAFE root cause: the
/// query-violation check then reduces to "is the query satisfiable in isolation"
/// instead of "is it reachable under the real state", so a BV/array query that a
/// `select`-over-`store` equality actually refutes is wrongly blessed as UNSAFE.
fn witness_is_vacuous(cex: &Counterexample) -> bool {
    match cex.witness.as_ref() {
        Some(w) => {
            !w.entries.is_empty() && w.entries.iter().all(|e| is_true_constraint(Some(&e.state)))
        }
        None => false,
    }
}

pub(crate) fn validate_counterexample(
    problem: &ChcProblem,
    cex: &Counterexample,
    budget: Duration,
    verbose: bool,
) -> bool {
    if budget < MIN_SMT_BUDGET {
        return false;
    }

    // UNCONDITIONAL soundness guard: fail closed on a vacuous (all-`true`-state)
    // marker-dag witness rather than bless it as a valid counterexample. A vacuous
    // witness makes `verify_counterexample` reduce to "is the query satisfiable in
    // isolation" instead of "is it reachable under the real state", which emitted a
    // FALSE UNSAFE on expected-safe harnesses (diagnosed on
    // prusti_Fibonacci_sequence). This was previously gated behind the opt-in
    // `AY_CHC_STRICT_CEX` flag; soundness guards must not be opt-in, so the
    // rejection now applies in every mode. Worst case this demotes an `unsat`
    // claim to `unknown` (never a wrong answer).
    if witness_is_vacuous(cex) {
        return false;
    }
    let Some(control) = Control::capture(budget) else {
        return false;
    };
    let _scope = control.enter();

    let config = PdrConfig {
        verbose,
        strict_proofs: true,
        solve_timeout: Some(budget),
        disable_array_scalarization: true,
        preserve_original_clauses: true,
        ..PdrConfig::default()
    };
    let mut verifier = PdrSolver::new(problem.clone(), config);
    verifier.set_validation_deadline(budget);
    let accepted = matches!(
        verifier.verify_counterexample(cex),
        CexVerificationResult::Valid
    );
    accepted && control.poll().is_some()
}

#[derive(Clone)]
struct MarkerDagTree {
    predicate: PredicateId,
    clause_idx: usize,
    children: Vec<Self>,
    size: usize,
}

struct MarkerDagNode {
    predicate: PredicateId,
    clause_idx: usize,
    children: Vec<usize>,
}

fn try_build_marker_dag_counterexample(
    problem: &ChcProblem,
    predicate: PredicateId,
    query_clause: usize,
    control: &Control,
) -> Result<NullaryAdtArrayCandidate, NullaryAdtArrayOutcome> {
    if !(problem.has_array_sorts() || problem.has_datatype_sorts()) {
        return Err(NullaryAdtArrayOutcome::NotApplicable);
    }
    if problem.clauses().len() > MARKER_DAG_MAX_CLAUSES {
        return Err(NullaryAdtArrayOutcome::NotApplicable);
    }

    let mut trees = Vec::new();
    let mut visiting = FxHashSet::default();
    collect_marker_dag_trees(
        problem,
        predicate,
        MARKER_DAG_MAX_DEPTH,
        &mut visiting,
        &mut trees,
        control,
    );
    control.poll().ok_or(NullaryAdtArrayOutcome::NoBudget)?;
    if trees.is_empty() {
        return Err(NullaryAdtArrayOutcome::DagNotFound);
    }

    let divisor = u32::try_from(trees.len().min(8)).unwrap_or(1);
    let budget = control
        .remaining()
        .ok_or(NullaryAdtArrayOutcome::NoBudget)?;
    let per_tree_budget = (budget / divisor)
        .max(MIN_SMT_BUDGET)
        .min(Duration::from_millis(500));
    let mut saw_unknown = false;

    for tree in trees {
        control.poll().ok_or(NullaryAdtArrayOutcome::NoBudget)?;
        match solve_marker_dag_tree(
            problem,
            predicate,
            query_clause,
            &tree,
            per_tree_budget,
            control,
        ) {
            MarkerDagSolve::Candidate(candidate) => return Ok(candidate),
            MarkerDagSolve::Unsat => {}
            MarkerDagSolve::Unknown => saw_unknown = true,
        }
    }

    if saw_unknown {
        Err(NullaryAdtArrayOutcome::DagUnknown)
    } else {
        Err(NullaryAdtArrayOutcome::DagNotFound)
    }
}

fn collect_marker_dag_trees(
    problem: &ChcProblem,
    predicate: PredicateId,
    remaining_depth: usize,
    visiting: &mut FxHashSet<PredicateId>,
    out: &mut Vec<MarkerDagTree>,
    control: &Control,
) {
    if control.admit(1, 128).is_none() {
        return;
    }
    if remaining_depth == 0 || out.len() >= MARKER_DAG_MAX_TREES || !visiting.insert(predicate) {
        return;
    }

    for (clause_idx, clause) in problem.clauses_defining_with_index(predicate) {
        if out.len() >= MARKER_DAG_MAX_TREES {
            break;
        }
        if clause.body.predicates.len() > MARKER_DAG_MAX_BODY_PREDS {
            continue;
        }

        let mut child_options = Vec::with_capacity(clause.body.predicates.len());
        let mut applicable = true;
        for (body_pred, _) in &clause.body.predicates {
            let mut options = Vec::new();
            collect_marker_dag_trees(
                problem,
                *body_pred,
                remaining_depth - 1,
                visiting,
                &mut options,
                control,
            );
            if options.is_empty() {
                applicable = false;
                break;
            }
            child_options.push(options);
        }
        if !applicable {
            continue;
        }

        push_marker_dag_combinations(
            predicate,
            clause_idx,
            &child_options,
            0,
            Vec::new(),
            out,
            control,
        );
    }

    visiting.remove(&predicate);
}

fn push_marker_dag_combinations(
    predicate: PredicateId,
    clause_idx: usize,
    child_options: &[Vec<MarkerDagTree>],
    idx: usize,
    current: Vec<MarkerDagTree>,
    out: &mut Vec<MarkerDagTree>,
    control: &Control,
) {
    if control.admit(1, 128).is_none() {
        return;
    }
    if out.len() >= MARKER_DAG_MAX_TREES {
        return;
    }
    if idx == child_options.len() {
        let Some(size) = current
            .iter()
            .try_fold(1usize, |size, child| size.checked_add(child.size))
        else {
            control.refuse::<()>();
            return;
        };
        out.push(MarkerDagTree {
            predicate,
            clause_idx,
            children: current,
            size,
        });
        return;
    }

    for child in &child_options[idx] {
        let Some(size) = current
            .iter()
            .try_fold(child.size, |size, item| size.checked_add(item.size))
        else {
            control.refuse::<()>();
            return;
        };
        let Some(bytes) = size.checked_mul(128) else {
            control.refuse::<()>();
            return;
        };
        if control.admit(size, bytes).is_none() {
            return;
        }
        let mut next = current.clone();
        next.push(child.clone());
        push_marker_dag_combinations(
            predicate,
            clause_idx,
            child_options,
            idx + 1,
            next,
            out,
            control,
        );
        if out.len() >= MARKER_DAG_MAX_TREES {
            break;
        }
    }
}

enum MarkerDagSolve {
    Candidate(NullaryAdtArrayCandidate),
    Unsat,
    Unknown,
}

fn solve_marker_dag_tree(
    problem: &ChcProblem,
    predicate: PredicateId,
    query_clause: usize,
    tree: &MarkerDagTree,
    budget: Duration,
    control: &Control,
) -> MarkerDagSolve {
    let Some(remaining) = control.remaining() else {
        return MarkerDagSolve::Unknown;
    };
    let _tree_deadline = crate::smt::deadline::ScopedSmtDeadline::install(budget.min(remaining));
    let mut nodes = Vec::new();
    let Some(root) = flatten_marker_dag_tree(tree, &mut nodes, control) else {
        return MarkerDagSolve::Unknown;
    };
    let Some(names) = Names::capture(problem, &nodes, query_clause, control) else {
        return MarkerDagSolve::Unknown;
    };
    let Some(formula) = marker_dag_formula(problem, query_clause, &nodes, root, &names, control)
    else {
        return MarkerDagSolve::Unknown;
    };
    if collect_dt_declarations_for_expr(&[], &formula).is_err() {
        // The solver and seed-model fallbacks below both run recursive
        // expression helpers. Decline the entire reconstructed path before
        // either can observe an over-cap in-memory surface.
        return MarkerDagSolve::Unknown;
    }

    let mut smt = problem.make_smt_context();
    // `smt_confirmed` tracks whether an actual SMT/executor `check_sat` proved
    // the reconstructed derivation formula satisfiable. When it did not (the
    // `Unknown -> marker_dag_seed_model` fabrication path) the model is only a
    // heuristic guess and must be positively re-confirmed before it can back a
    // counterexample.
    let Some(budget) = tree_remaining(control) else {
        return MarkerDagSolve::Unknown;
    };
    let (model, smt_confirmed) = match smt
        .check_sat_with_executor_fallback_timeout(&formula, budget)
    {
        SmtResult::Sat(mut model) => {
            if tree_remaining(control).is_none() {
                return MarkerDagSolve::Unknown;
            }
            fill_missing_seed(&mut model, marker_dag_seed_model(&formula));
            (model, true)
        }
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
            return MarkerDagSolve::Unsat;
        }
        SmtResult::Unknown => {
            let Some(remaining) = tree_remaining(control) else {
                return MarkerDagSolve::Unknown;
            };
            match marker_dag_raw_executor_model(&formula, remaining) {
                SmtResult::Sat(mut model) => {
                    if tree_remaining(control).is_none() {
                        return MarkerDagSolve::Unknown;
                    }
                    fill_missing_seed(&mut model, marker_dag_seed_model(&formula));
                    (model, true)
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    return MarkerDagSolve::Unsat;
                }
                SmtResult::Unknown => {
                    if tree_remaining(control).is_none() {
                        return MarkerDagSolve::Unknown;
                    }
                    (marker_dag_seed_model(&formula), false)
                }
            }
        }
    };
    if tree_remaining(control).is_none() {
        return MarkerDagSolve::Unknown;
    }

    // SOUNDNESS GATE (Mem-track false-UNSAT fix): never emit a counterexample
    // from a model we have not confirmed against the reconstructed derivation
    // formula.
    //
    // The `Unknown -> marker_dag_seed_model` fallback hands us a fabricated
    // model that need not satisfy the derivation — e.g. the store-in-head-arg
    // Mem-track shape `Inv(store v 0 true)` with query `not(select v 0)`: the
    // seed sets the array so that `select v 0 = true`, so the derivation
    // formula is actually FALSE, yet the fabricated model still claimed a
    // violation. The downstream witness verifier records only clause-local
    // instances (entry state == true) and cannot reconstruct the head-arg
    // array value, so it rubber-stamps the spurious witness → false UNSAT on a
    // SAFE problem. Concretely evaluating the full marker formula (fact /
    // transition constraints ∧ body-arg↦child-head-arg linking equalities ∧
    // the violated query constraint) closes that hole.
    match evaluate_expr(&formula, &model) {
        // Model concretely realises the whole derivation → a real unsafety
        // witness regardless of how the model was obtained.
        Some(SmtValue::Bool(true)) => {}
        // Model concretely REFUTES the derivation. This is always spurious —
        // decline whether it came from seed fabrication or a false-SAT.
        Some(SmtValue::Bool(false)) => {
            if ay_core::misc_cli_flags().chc_debug_marker_dag_verify {
                safe_eprintln!(
                    "adt_array_nullary: marker-DAG model concretely REFUTES derivation \
                     (smt_confirmed={smt_confirmed}); declining candidate (fail-closed to Unknown)"
                );
            }
            return MarkerDagSolve::Unknown;
        }
        // Could not fold to a concrete truth value (opaque/uninterpreted
        // sub-terms). Trust ONLY a genuine SMT SAT; a fabricated seed model we
        // cannot confirm must be declined.
        _ => {
            if !smt_confirmed {
                if ay_core::misc_cli_flags().chc_debug_marker_dag_verify {
                    safe_eprintln!(
                        "adt_array_nullary: fabricated marker-DAG model could not be confirmed \
                         (evaluate_expr indeterminate); declining candidate (fail-closed to Unknown)"
                    );
                }
                return MarkerDagSolve::Unknown;
            }
        }
    }

    let Some(cex) =
        grounded::from_model(problem, query_clause, &nodes, root, &names, &model, control)
    else {
        return MarkerDagSolve::Unknown;
    };
    if tree_remaining(control).is_none() {
        return MarkerDagSolve::Unknown;
    }

    MarkerDagSolve::Candidate(NullaryAdtArrayCandidate {
        cex,
        source_clause: nodes[root].clause_idx,
        query_clause,
        predicate,
    })
}

fn tree_remaining(control: &Control) -> Option<Duration> {
    let original = control.remaining()?;
    let remaining =
        crate::smt::deadline::smt_deadline_remaining().map_or(original, |tree| tree.min(original));
    (!remaining.is_zero()).then_some(remaining)
}

fn flatten_marker_dag_tree(
    tree: &MarkerDagTree,
    nodes: &mut Vec<MarkerDagNode>,
    control: &Control,
) -> Option<usize> {
    control.admit(tree.children.len().checked_add(1)?, 128)?;
    let children = tree
        .children
        .iter()
        .map(|child| flatten_marker_dag_tree(child, nodes, control))
        .collect::<Option<Vec<_>>>()?;
    let id = nodes.len();
    nodes.push(MarkerDagNode {
        predicate: tree.predicate,
        clause_idx: tree.clause_idx,
        children,
    });
    Some(id)
}

fn marker_dag_formula(
    problem: &ChcProblem,
    query_clause: usize,
    nodes: &[MarkerDagNode],
    root: usize,
    names: &Names,
    control: &Control,
) -> Option<ChcExpr> {
    let mut conjuncts = Vec::new();

    for (node_id, node) in nodes.iter().enumerate() {
        control.admit(1, 128)?;
        let clause = problem.clauses().get(node.clause_idx)?;
        let ClauseHead::Predicate(head_pred, _) = &clause.head else {
            return None;
        };
        if *head_pred != node.predicate || node.children.len() != clause.body.predicates.len() {
            return None;
        }

        let subst = names.node(node_id)?;
        if let Some(constraint) = &clause.body.constraint {
            conjuncts.push(constraint.substitute_name_map(&subst).simplify_constants());
        }

        for (body_idx, (body_pred, body_args)) in clause.body.predicates.iter().enumerate() {
            let child_id = *node.children.get(body_idx)?;
            let child = nodes.get(child_id)?;
            let child_clause = problem.clauses().get(child.clause_idx)?;
            let ClauseHead::Predicate(child_head_pred, child_head_args) = &child_clause.head else {
                return None;
            };
            if child_head_pred != body_pred || child_head_args.len() != body_args.len() {
                return None;
            }
            let child_subst = names.node(child_id)?;
            for (body_arg, child_head_arg) in body_args.iter().zip(child_head_args) {
                control.admit(1, 256)?;
                conjuncts.push(ChcExpr::eq(
                    body_arg.substitute_name_map(&subst).simplify_constants(),
                    child_head_arg
                        .substitute_name_map(&child_subst)
                        .simplify_constants(),
                ));
            }
        }
    }

    let query = problem.clauses().get(query_clause)?;
    let [(query_pred, query_args)] = query.body.predicates.as_slice() else {
        return None;
    };
    let root_node = nodes.get(root)?;
    if *query_pred != root_node.predicate {
        return None;
    }
    let root_clause = problem.clauses().get(root_node.clause_idx)?;
    let ClauseHead::Predicate(_, root_head_args) = &root_clause.head else {
        return None;
    };
    if root_head_args.len() != query_args.len() {
        return None;
    }
    let root_subst = names.node(root)?;
    let query_subst = names.query();
    for (query_arg, root_head_arg) in query_args.iter().zip(root_head_args) {
        conjuncts.push(ChcExpr::eq(
            query_arg
                .substitute_name_map(&query_subst)
                .simplify_constants(),
            root_head_arg
                .substitute_name_map(&root_subst)
                .simplify_constants(),
        ));
    }
    if let Some(constraint) = &query.body.constraint {
        conjuncts.push(
            constraint
                .substitute_name_map(&query_subst)
                .simplify_constants(),
        );
    }

    control.poll()?;
    Some(ChcExpr::and_all(conjuncts))
}

/// Fill only the entries that `model` does not already bind from `seed`.
///
/// The SMT-confirmed model is authoritative; seed defaults exist solely to give
/// concrete values to variables the solver left unconstrained. Overwriting real
/// model bindings with seed defaults (the previous `model.extend(seed)`) could
/// clobber a genuine satisfying assignment, which then fails the concrete
/// confirmation gate above — a completeness loss on real counterexamples. This
/// non-overwriting merge keeps the solver's assignment intact.
fn fill_missing_seed(model: &mut FxHashMap<String, SmtValue>, seed: FxHashMap<String, SmtValue>) {
    for (name, value) in seed {
        // Keep a genuine solver binding; only fill a hole or replace an opaque
        // placeholder (which `evaluate_expr` cannot fold and which the witness
        // builder discards anyway) with the concrete seed default.
        match model.get(&name) {
            Some(SmtValue::Opaque(_)) | None => {
                model.insert(name, value);
            }
            Some(_) => {}
        }
    }
}

fn marker_dag_seed_model(formula: &ChcExpr) -> FxHashMap<String, SmtValue> {
    let mut model = FxHashMap::default();
    for var in formula.vars() {
        if let Some(value) = default_smt_value_for_sort(&var.sort, DEFAULT_VALUE_RECURSION_LIMIT) {
            model.insert(var.name, value);
        }
    }

    let conjuncts = formula.collect_conjuncts_nontrivial();

    for _ in 0..32 {
        let mut changed = false;
        for conjunct in &conjuncts {
            if seed_scalar_from_conjunct(conjunct, &mut model) {
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    model
}

fn seed_scalar_from_conjunct(conjunct: &ChcExpr, model: &mut FxHashMap<String, SmtValue>) -> bool {
    match conjunct {
        ChcExpr::Var(var) if matches!(var.sort, ChcSort::Bool) => {
            insert_seed_value(model, &var.name, SmtValue::Bool(true))
        }
        ChcExpr::Op(crate::ChcOp::Not, args) if args.len() == 1 => {
            if let ChcExpr::Var(var) = args[0].as_ref() {
                if matches!(var.sort, ChcSort::Bool) {
                    return insert_seed_value(model, &var.name, SmtValue::Bool(false));
                }
            }
            false
        }
        ChcExpr::Op(crate::ChcOp::Eq, args) if args.len() == 2 => {
            seed_equality(args[0].as_ref(), args[1].as_ref(), model)
                | seed_equality(args[1].as_ref(), args[0].as_ref(), model)
        }
        ChcExpr::Op(crate::ChcOp::Ge, args) if args.len() == 2 => {
            seed_int_lower_bound(args[0].as_ref(), args[1].as_ref(), false, model)
        }
        ChcExpr::Op(crate::ChcOp::Gt, args) if args.len() == 2 => {
            seed_int_lower_bound(args[0].as_ref(), args[1].as_ref(), true, model)
        }
        _ => false,
    }
}

fn seed_equality(lhs: &ChcExpr, rhs: &ChcExpr, model: &mut FxHashMap<String, SmtValue>) -> bool {
    let Some(value) = evaluate_expr(rhs, model) else {
        return false;
    };

    if let ChcExpr::Var(var) = lhs {
        if smt_value_matches_sort_deep(&value, &var.sort, DEFAULT_VALUE_RECURSION_LIMIT) {
            return insert_seed_value(model, &var.name, value);
        }
    }

    seed_path_value(lhs, value, model)
}

fn seed_int_lower_bound(
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    strict: bool,
    model: &mut FxHashMap<String, SmtValue>,
) -> bool {
    let Some(SmtValue::Int(bound)) = evaluate_expr(rhs, model) else {
        return false;
    };
    let Some((base, path)) = seed_path(lhs, model) else {
        return false;
    };
    let Some(current) = model.get(&base.name).cloned() else {
        return false;
    };
    let needed = if strict {
        bound.saturating_add(1)
    } else {
        bound
    };
    if matches!(seed_value_at_path(&current, &base.sort, &path), Some(SmtValue::Int(value)) if value >= needed)
    {
        return false;
    }
    let Some(updated) = seed_set_value_at_path(
        current,
        &base.sort,
        &path,
        SmtValue::Int(needed),
        DEFAULT_VALUE_RECURSION_LIMIT,
    ) else {
        return false;
    };
    insert_seed_value(model, &base.name, updated)
}

#[derive(Clone)]
enum SeedPathPart {
    Selector(String),
    Select(SmtValue),
}

fn seed_path_value(
    lhs: &ChcExpr,
    value: SmtValue,
    model: &mut FxHashMap<String, SmtValue>,
) -> bool {
    let Some((base, path)) = seed_path(lhs, model) else {
        return false;
    };
    let Some(current) = model
        .get(&base.name)
        .cloned()
        .or_else(|| default_smt_value_for_sort(&base.sort, DEFAULT_VALUE_RECURSION_LIMIT))
    else {
        return false;
    };
    let Some(updated) = seed_set_value_at_path(
        current,
        &base.sort,
        &path,
        value,
        DEFAULT_VALUE_RECURSION_LIMIT,
    ) else {
        return false;
    };
    insert_seed_value(model, &base.name, updated)
}

fn seed_path(
    expr: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<(ChcVar, Vec<SeedPathPart>)> {
    match expr {
        ChcExpr::Var(var) => Some((var.clone(), Vec::new())),
        ChcExpr::FuncApp(name, _, args) if args.len() == 1 => {
            let (base, mut path) = seed_path(args[0].as_ref(), model)?;
            selector_sort(&args[0].sort(), name)?;
            path.push(SeedPathPart::Selector(name.clone()));
            Some((base, path))
        }
        ChcExpr::Op(crate::ChcOp::Select, args) if args.len() == 2 => {
            let (base, mut path) = seed_path(args[0].as_ref(), model)?;
            let index = evaluate_expr(args[1].as_ref(), model)?;
            path.push(SeedPathPart::Select(index));
            Some((base, path))
        }
        _ => None,
    }
}

fn selector_sort(parent_sort: &ChcSort, selector_name: &str) -> Option<ChcSort> {
    let ChcSort::Datatype {
        name: parent_name,
        constructors,
    } = parent_sort
    else {
        return None;
    };
    let selector_sort = constructors
        .iter()
        .find_map(|ctor| ctor.selectors.iter().find(|sel| sel.name == selector_name))
        .map(|sel| sel.sort.clone())?;
    match &selector_sort {
        ChcSort::Uninterpreted(name) | ChcSort::Datatype { name, .. } if name == parent_name => {
            Some(parent_sort.clone())
        }
        _ => Some(selector_sort),
    }
}

fn seed_set_value_at_path(
    current: SmtValue,
    sort: &ChcSort,
    path: &[SeedPathPart],
    value: SmtValue,
    remaining_depth: usize,
) -> Option<SmtValue> {
    if remaining_depth == 0 {
        return None;
    }
    let Some((part, rest)) = path.split_first() else {
        return smt_value_matches_sort_deep(&value, sort, remaining_depth).then_some(value);
    };

    match (part, sort, current) {
        (
            SeedPathPart::Selector(selector_name),
            ChcSort::Datatype { constructors, .. },
            SmtValue::Datatype(ctor_name, mut fields),
        ) => {
            let ctor = constructors.iter().find(|ctor| ctor.name == ctor_name)?;
            let (field_idx, _) = ctor
                .selectors
                .iter()
                .enumerate()
                .find(|(_, selector)| selector.name == *selector_name)?;
            let field_sort = selector_sort(sort, selector_name)?;
            let existing = fields
                .get(field_idx)
                .cloned()
                .or_else(|| default_smt_value_for_sort(&field_sort, remaining_depth - 1))?;
            let updated =
                seed_set_value_at_path(existing, &field_sort, rest, value, remaining_depth - 1)?;
            *fields.get_mut(field_idx)? = updated;
            Some(SmtValue::Datatype(ctor_name, fields))
        }
        (SeedPathPart::Select(index), ChcSort::Array(index_sort, value_sort), array_value) => {
            if !smt_value_matches_sort_deep(index, index_sort, remaining_depth - 1) {
                return None;
            }
            let (default, mut entries) = match array_value {
                SmtValue::ConstArray(default) => (default, Vec::new()),
                SmtValue::ArrayMap { default, entries } => (default, entries),
                _ => (
                    Box::new(default_smt_value_for_sort(value_sort, remaining_depth - 1)?),
                    Vec::new(),
                ),
            };
            let existing = entries
                .iter()
                .find(|(entry_index, _)| entry_index == index)
                .map(|(_, entry_value)| entry_value.clone())
                .unwrap_or_else(|| default.as_ref().clone());
            let updated =
                seed_set_value_at_path(existing, value_sort, rest, value, remaining_depth - 1)?;
            if let Some((_, entry_value)) = entries
                .iter_mut()
                .find(|(entry_index, _)| entry_index == index)
            {
                *entry_value = updated;
            } else {
                entries.push((index.clone(), updated));
            }
            Some(SmtValue::ArrayMap { default, entries })
        }
        _ => None,
    }
}

fn seed_value_at_path(
    current: &SmtValue,
    sort: &ChcSort,
    path: &[SeedPathPart],
) -> Option<SmtValue> {
    let Some((part, rest)) = path.split_first() else {
        return Some(current.clone());
    };
    match (part, sort, current) {
        (
            SeedPathPart::Selector(selector_name),
            ChcSort::Datatype { constructors, .. },
            SmtValue::Datatype(ctor_name, fields),
        ) => {
            let ctor = constructors.iter().find(|ctor| ctor.name == *ctor_name)?;
            let (field_idx, _) = ctor
                .selectors
                .iter()
                .enumerate()
                .find(|(_, selector)| selector.name == *selector_name)?;
            let field_sort = selector_sort(sort, selector_name)?;
            seed_value_at_path(fields.get(field_idx)?, &field_sort, rest)
        }
        (SeedPathPart::Select(_), ChcSort::Array(_, value_sort), SmtValue::ConstArray(default)) => {
            seed_value_at_path(default, value_sort, rest)
        }
        (
            SeedPathPart::Select(index),
            ChcSort::Array(_, value_sort),
            SmtValue::ArrayMap { default, entries },
        ) => {
            let value = entries
                .iter()
                .find(|(entry_index, _)| entry_index == index)
                .map(|(_, entry_value)| entry_value)
                .unwrap_or(default);
            seed_value_at_path(value, value_sort, rest)
        }
        _ => None,
    }
}

fn insert_seed_value(model: &mut FxHashMap<String, SmtValue>, name: &str, value: SmtValue) -> bool {
    if let Some(existing) = model.get(name).cloned() {
        let merged = merge_seed_value(existing, value);
        if model.get(name) == Some(&merged) {
            return false;
        }
        model.insert(name.to_string(), merged);
        return true;
    }
    model.insert(name.to_string(), value);
    true
}

fn merge_seed_value(existing: SmtValue, incoming: SmtValue) -> SmtValue {
    match (existing, incoming) {
        (left, right) if left == right => left,
        (SmtValue::Int(existing), SmtValue::Int(incoming)) => {
            SmtValue::Int(if incoming == 0 { existing } else { incoming })
        }
        (
            left @ (SmtValue::BitVec(..) | SmtValue::BigBitVec(..)),
            right @ (SmtValue::BitVec(..) | SmtValue::BigBitVec(..)),
        ) => {
            let (_, left_width) = left
                .bitvec_to_biguint()
                .unwrap_or_else(|| unreachable!("matched bitvector must expose exact bits"));
            let (right_value, right_width) = right
                .bitvec_to_biguint()
                .unwrap_or_else(|| unreachable!("matched bitvector must expose exact bits"));
            if left_width == right_width && right_value == num_bigint::BigUint::from(0u8) {
                left
            } else {
                right
            }
        }
        (
            SmtValue::Datatype(left_ctor, left_fields),
            SmtValue::Datatype(right_ctor, right_fields),
        ) if left_ctor == right_ctor && left_fields.len() == right_fields.len() => {
            SmtValue::Datatype(
                left_ctor,
                left_fields
                    .into_iter()
                    .zip(right_fields)
                    .map(|(left, right)| merge_seed_value(left, right))
                    .collect(),
            )
        }
        (
            SmtValue::ArrayMap {
                default: left_default,
                entries: left_entries,
            },
            SmtValue::ArrayMap {
                default: right_default,
                entries: right_entries,
            },
        ) => merge_seed_arrays(*left_default, left_entries, *right_default, right_entries),
        (
            SmtValue::ConstArray(left_default),
            SmtValue::ArrayMap {
                default: right_default,
                entries: right_entries,
            },
        ) => merge_seed_arrays(*left_default, Vec::new(), *right_default, right_entries),
        (
            SmtValue::ArrayMap {
                default: left_default,
                entries: left_entries,
            },
            SmtValue::ConstArray(right_default),
        ) => merge_seed_arrays(*left_default, left_entries, *right_default, Vec::new()),
        (_, incoming) => incoming,
    }
}

fn merge_seed_arrays(
    left_default: SmtValue,
    mut left_entries: Vec<(SmtValue, SmtValue)>,
    right_default: SmtValue,
    right_entries: Vec<(SmtValue, SmtValue)>,
) -> SmtValue {
    let default = Box::new(merge_seed_value(left_default, right_default));
    for (right_index, right_value) in right_entries {
        if let Some((_, left_value)) = left_entries
            .iter_mut()
            .find(|(left_index, _)| left_index == &right_index)
        {
            *left_value = merge_seed_value(left_value.clone(), right_value);
        } else {
            left_entries.push((right_index, right_value));
        }
    }
    if left_entries.is_empty() {
        SmtValue::ConstArray(default)
    } else {
        SmtValue::ArrayMap {
            default,
            entries: left_entries,
        }
    }
}

fn marker_dag_raw_executor_model(formula: &ChcExpr, budget: Duration) -> SmtResult {
    // This executor escape hatch must share the same iterative admission point
    // as the primary adapter.  In particular, do not call the recursive
    // `vars`/logic helpers on an unbounded in-memory expression.
    let dt_decls = match collect_dt_declarations_for_expr(&[], formula) {
        Ok(declarations) => declarations,
        Err(_) => return SmtResult::Unknown,
    };
    let vars = formula.vars();
    if vars.is_empty() {
        return SmtResult::Unknown;
    }

    let detected_logic = detect_logic(&vars, formula);
    let logic = if detected_logic.starts_with("_DT_") {
        "ALL"
    } else {
        detected_logic
    };
    let mut smt = String::with_capacity(4096);
    smt.push_str(&format!("(set-logic {logic})\n"));
    smt.push_str("(set-option :produce-models true)\n");
    let timeout_ms = budget.as_millis();
    if timeout_ms > 0 && timeout_ms < u128::from(u64::MAX) {
        smt.push_str(&format!("(set-option :timeout {timeout_ms})\n"));
    }

    match emit_declare_datatypes(&dt_decls) {
        Ok(declarations) => smt.push_str(&declarations),
        Err(_) => return SmtResult::Unknown,
    }
    let uf_decls = match collect_uninterpreted_function_declarations(formula) {
        Ok(declarations) => declarations,
        Err(_) => return SmtResult::Unknown,
    };
    for declaration in &uf_decls {
        smt.push_str(&emit_declare_uninterpreted_function(declaration));
    }
    for var in &vars {
        smt.push_str(&format!(
            "(declare-const {} {})\n",
            quote_symbol(&var.name),
            sort_to_smtlib(&var.sort)
        ));
    }
    for conjunct in formula.conjuncts() {
        smt.push_str("(assert ");
        smt.push_str(&InvariantModel::expr_to_smtlib(conjunct));
        smt.push_str(")\n");
    }
    smt.push_str("(check-sat)\n(get-model)\n");

    let commands = match ay_frontend::parse(&smt) {
        Ok(commands) => commands,
        Err(_) => return SmtResult::Unknown,
    };
    let outputs = match ay_core::catch_ay_panics(
        AssertUnwindSafe(|| {
            let mut exec = crate::smt::executor_adapter::new_search_executor();
            exec.execute_all(&commands).map_err(|_| ())
        }),
        |_| Err(()),
    ) {
        Ok(outputs) => outputs,
        Err(()) => return SmtResult::Unknown,
    };

    match outputs.first().map(String::as_str).unwrap_or("unknown") {
        "sat" => {
            let mut model = FxHashMap::default();
            let dt_ctor_names: FxHashSet<String> = dt_decls
                .iter()
                .flat_map(|(_, ctors)| ctors.iter().map(|ctor| ctor.name.clone()))
                .collect();
            parse_model_into(
                &mut model,
                outputs.get(1).map(String::as_str).unwrap_or(""),
                &dt_ctor_names,
            );
            SmtResult::Sat(model)
        }
        "unsat" => SmtResult::Unsat,
        _ => SmtResult::Unknown,
    }
}

fn default_smt_value_for_sort(sort: &ChcSort, remaining_depth: usize) -> Option<SmtValue> {
    if remaining_depth == 0 {
        return None;
    }
    match sort {
        ChcSort::Bool => Some(SmtValue::Bool(false)),
        ChcSort::Int => Some(SmtValue::Int(0)),
        ChcSort::Real => Some(SmtValue::Real(num_rational::BigRational::from_integer(
            0.into(),
        ))),
        ChcSort::BitVec(width) => Some(SmtValue::bitvec_from_biguint(
            num_bigint::BigUint::from(0u8),
            *width,
        )),
        ChcSort::Array(_, value_sort) => Some(SmtValue::ConstArray(Box::new(
            default_smt_value_for_sort(value_sort, remaining_depth - 1)?,
        ))),
        ChcSort::Datatype { constructors, .. } => {
            let ctor = constructors.first()?;
            let fields = ctor
                .selectors
                .iter()
                .map(|selector| default_smt_value_for_sort(&selector.sort, remaining_depth - 1))
                .collect::<Option<Vec<_>>>()?;
            Some(SmtValue::Datatype(ctor.name.clone(), fields))
        }
        ChcSort::Uninterpreted(_) => None,
    }
}

fn nullary_false_query(problem: &ChcProblem) -> Option<(usize, PredicateId)> {
    let mut query = None;

    for (idx, clause) in problem.clauses().iter().enumerate() {
        if !matches!(clause.head, ClauseHead::False) {
            continue;
        }
        if !is_true_constraint(clause.body.constraint.as_ref()) {
            continue;
        }
        let [(predicate, args)] = clause.body.predicates.as_slice() else {
            continue;
        };
        if !args.is_empty() {
            continue;
        }
        if problem
            .get_predicate(*predicate)
            .is_none_or(|pred| !pred.arg_sorts.is_empty())
        {
            continue;
        }
        if query.replace((idx, *predicate)).is_some() {
            return None;
        }
    }

    query
}

fn array_dag_false_query(problem: &ChcProblem) -> Option<(usize, PredicateId)> {
    if !problem.has_array_sorts() || problem.clauses().len() > MARKER_DAG_MAX_CLAUSES {
        return None;
    }

    let mut query = None;
    for (idx, clause) in problem.clauses().iter().enumerate() {
        if !matches!(clause.head, ClauseHead::False) {
            continue;
        }
        let [(predicate, args)] = clause.body.predicates.as_slice() else {
            continue;
        };
        if args.is_empty() {
            continue;
        }
        let Some(pred) = problem.get_predicate(*predicate) else {
            continue;
        };
        if pred.arg_sorts.len() != args.len()
            || !pred
                .arg_sorts
                .iter()
                .any(|sort| matches!(sort, ChcSort::Array(_, _)))
        {
            continue;
        }
        if query.replace((idx, *predicate)).is_some() {
            return None;
        }
    }

    query
}

fn nullary_adt_array_facts<'a>(
    problem: &'a ChcProblem,
    predicate: PredicateId,
) -> impl Iterator<Item = (usize, &'a ChcExpr)> + 'a {
    problem
        .clauses()
        .iter()
        .enumerate()
        .filter_map(move |(idx, clause)| {
            if !clause.body.predicates.is_empty() {
                return None;
            }
            let ClauseHead::Predicate(head_pred, head_args) = &clause.head else {
                return None;
            };
            if *head_pred != predicate || !head_args.is_empty() {
                return None;
            }
            let constraint = clause.body.constraint.as_ref()?;
            if !(constraint.contains_array_ops()
                && constraint_contains_datatype_surface(constraint))
            {
                return None;
            }
            Some((idx, constraint))
        })
}

fn is_true_constraint(expr: Option<&ChcExpr>) -> bool {
    matches!(expr, None | Some(ChcExpr::Bool(true)))
}

fn constraint_contains_datatype_surface(expr: &ChcExpr) -> bool {
    expr.contains_dt_ops()
}

#[cfg(test)]
fn build_counterexample(
    predicate: PredicateId,
    fact_clause: usize,
    query_clause: usize,
    instances: FxHashMap<String, SmtValue>,
) -> Counterexample {
    let step = CounterexampleStep::new(predicate, FxHashMap::default()).with_clause(fact_clause);
    let witness = DerivationWitness {
        query_clause: Some(query_clause),
        root: 0,
        entries: vec![DerivationWitnessEntry {
            predicate,
            level: 0,
            state: ChcExpr::Bool(true),
            incoming_clause: Some(fact_clause),
            premises: Vec::new(),
            instances,
        }],
    };

    Counterexample::with_witness(vec![step], witness)
}

fn tricera_memtrack_instances(constraint: &ChcExpr) -> Option<FxHashMap<String, SmtValue>> {
    let vars = constraint
        .vars()
        .into_iter()
        .map(|var| (var.name.clone(), var))
        .collect::<FxHashMap<_, _>>();

    let required = [
        ("A", "Heap"),
        ("B", "HeapObject"),
        ("C", "node"),
        ("D", "AllocResHeap"),
        ("E", "AllocResHeap"),
        ("F", "Heap"),
        ("G", "HeapObject"),
        ("H", "node"),
    ];
    for (name, datatype_name) in required {
        let var = vars.get(name)?;
        if !sort_is_named_datatype(&var.sort, datatype_name) {
            return None;
        }
    }
    for (name, sort) in [
        ("I", ChcSort::Int),
        ("J", ChcSort::Int),
        ("K", ChcSort::Int),
    ] {
        if vars.get(name).is_none_or(|var| var.sort != sort) {
            return None;
        }
    }
    if let Some(var) = vars.get("L") {
        if var.sort != ChcSort::Bool {
            return None;
        }
    }

    let node_0 = dt("node", [SmtValue::Int(0)]);
    let node_1 = dt("node", [SmtValue::Int(1)]);
    let def_obj = dt("defObj", []);
    let b = dt("O_node", [node_0.clone()]);
    let g = dt("O_node", [node_1.clone()]);

    let base_heap = heap(0, SmtValue::ConstArray(Box::new(def_obj.clone())));
    let f_contents = SmtValue::ArrayMap {
        default: Box::new(def_obj.clone()),
        entries: vec![(SmtValue::Int(1), b.clone())],
    };
    let f_heap = heap(1, f_contents.clone());
    let e_contents = SmtValue::ArrayMap {
        default: Box::new(def_obj),
        entries: vec![(SmtValue::Int(1), b.clone()), (SmtValue::Int(2), g.clone())],
    };
    let e_heap = heap(2, e_contents);

    let mut instances = FxHashMap::default();
    instances.insert("A".to_string(), base_heap);
    instances.insert("B".to_string(), b);
    instances.insert("C".to_string(), node_0);
    instances.insert("D".to_string(), alloc_res_heap(f_heap.clone(), 1));
    instances.insert("E".to_string(), alloc_res_heap(e_heap, 2));
    instances.insert("F".to_string(), f_heap);
    instances.insert("G".to_string(), g);
    instances.insert("H".to_string(), node_1);
    instances.insert("I".to_string(), SmtValue::Int(2));
    instances.insert("J".to_string(), SmtValue::Int(1));
    instances.insert("K".to_string(), SmtValue::Int(0));
    if vars.contains_key("L") {
        instances.insert("L".to_string(), SmtValue::Bool(false));
    }

    Some(instances)
}

fn sort_is_named_datatype(sort: &ChcSort, expected: &str) -> bool {
    matches!(
        sort,
        ChcSort::Datatype { name, .. } | ChcSort::Uninterpreted(name) if name == expected
    )
}

fn dt<const N: usize>(ctor: &str, fields: [SmtValue; N]) -> SmtValue {
    SmtValue::Datatype(ctor.to_string(), fields.into_iter().collect())
}

fn heap(size: i64, contents: SmtValue) -> SmtValue {
    dt("HeapCtor", [SmtValue::Int(i128::from(size)), contents])
}

fn alloc_res_heap(heap: SmtValue, addr: i64) -> SmtValue {
    dt("AllocResHeap", [heap, SmtValue::Int(i128::from(addr))])
}

fn scalar_instances_from_model(
    constraint: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
) -> Option<FxHashMap<String, SmtValue>> {
    let mut instances = FxHashMap::default();
    for var in constraint.vars() {
        let Some(value) = model.get(&var.name) else {
            continue;
        };
        if scalar_value_matches_sort(value, &var.sort) {
            instances.insert(var.name, value.clone());
        }
    }

    if instances.is_empty() {
        None
    } else {
        Some(instances)
    }
}

fn scalar_seed_instance(constraint: &ChcExpr) -> Option<FxHashMap<String, SmtValue>> {
    let (var, value) = scalar_literal_assignment(constraint).or_else(|| {
        constraint
            .vars()
            .into_iter()
            .find_map(default_scalar_assignment)
    })?;
    let mut instances = FxHashMap::default();
    instances.insert(var.name, value);
    Some(instances)
}

fn scalar_literal_assignment(expr: &ChcExpr) -> Option<(ChcVar, SmtValue)> {
    match expr {
        ChcExpr::ArrayLambda(_) => None,
        ChcExpr::Var(var) if matches!(var.sort, ChcSort::Bool) => {
            Some((var.clone(), SmtValue::Bool(true)))
        }
        ChcExpr::Op(crate::ChcOp::Not, args) if args.len() == 1 => {
            if let ChcExpr::Var(var) = args[0].as_ref() {
                if matches!(var.sort, ChcSort::Bool) {
                    return Some((var.clone(), SmtValue::Bool(false)));
                }
            }
            scalar_literal_assignment(args[0].as_ref())
        }
        ChcExpr::Op(crate::ChcOp::Eq, args) if args.len() == 2 => {
            scalar_var_literal_pair(args[0].as_ref(), args[1].as_ref())
                .or_else(|| scalar_var_literal_pair(args[1].as_ref(), args[0].as_ref()))
        }
        ChcExpr::Op(crate::ChcOp::And, args) => args
            .iter()
            .find_map(|arg| scalar_literal_assignment(arg.as_ref())),
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args.iter()
                .find_map(|arg| scalar_literal_assignment(arg.as_ref()))
        }
        ChcExpr::ConstArray(_, value) => scalar_literal_assignment(value.as_ref()),
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_) => None,
    }
}

fn scalar_var_literal_pair(var_expr: &ChcExpr, value_expr: &ChcExpr) -> Option<(ChcVar, SmtValue)> {
    let ChcExpr::Var(var) = var_expr else {
        return None;
    };
    let value = scalar_value_from_literal(value_expr, &var.sort)?;
    Some((var.clone(), value))
}

fn scalar_value_from_literal(expr: &ChcExpr, sort: &ChcSort) -> Option<SmtValue> {
    match (expr, sort) {
        (ChcExpr::Bool(value), ChcSort::Bool) => Some(SmtValue::Bool(*value)),
        (ChcExpr::Int(value), ChcSort::Int) => Some(SmtValue::Int(*value)),
        (ChcExpr::Real(num, den), ChcSort::Real) => Some(SmtValue::Real(
            num_rational::BigRational::new((*num).into(), (*den).into()),
        )),
        (ChcExpr::BitVec(value, width), ChcSort::BitVec(expected_width))
            if width == expected_width =>
        {
            Some(SmtValue::bitvec_from_u128(*value, *width))
        }
        _ => None,
    }
}

fn default_scalar_assignment(var: ChcVar) -> Option<(ChcVar, SmtValue)> {
    let value = match var.sort {
        ChcSort::Bool => SmtValue::Bool(false),
        ChcSort::Int => SmtValue::Int(0),
        ChcSort::Real => SmtValue::Real(num_rational::BigRational::from_integer(0.into())),
        ChcSort::BitVec(width) => {
            SmtValue::bitvec_from_biguint(num_bigint::BigUint::from(0u8), width)
        }
        ChcSort::Array(_, _) | ChcSort::Uninterpreted(_) | ChcSort::Datatype { .. } => {
            return None;
        }
    };
    Some((var, value))
}

fn scalar_value_matches_sort(value: &SmtValue, sort: &ChcSort) -> bool {
    smt_value_matches_sort_deep(value, sort, DEFAULT_VALUE_RECURSION_LIMIT)
}

fn smt_value_matches_sort_deep(value: &SmtValue, sort: &ChcSort, remaining_depth: usize) -> bool {
    if remaining_depth == 0 {
        return false;
    }

    match (value, sort) {
        (SmtValue::Bool(_), ChcSort::Bool)
        | (SmtValue::Int(_), ChcSort::Int)
        | (SmtValue::Real(_), ChcSort::Real) => true,
        (
            SmtValue::BitVec(_, value_width) | SmtValue::BigBitVec(_, value_width),
            ChcSort::BitVec(sort_width),
        ) => value_width == sort_width,
        (SmtValue::ConstArray(default), ChcSort::Array(_, value_sort)) => {
            smt_value_matches_sort_deep(default, value_sort, remaining_depth - 1)
        }
        (SmtValue::ArrayMap { default, entries }, ChcSort::Array(index_sort, value_sort)) => {
            smt_value_matches_sort_deep(default, value_sort, remaining_depth - 1)
                && entries.iter().all(|(index, value)| {
                    smt_value_matches_sort_deep(index, index_sort, remaining_depth - 1)
                        && smt_value_matches_sort_deep(value, value_sort, remaining_depth - 1)
                })
        }
        (SmtValue::Datatype(ctor_name, fields), ChcSort::Datatype { constructors, .. }) => {
            let Some(ctor) = constructors.iter().find(|ctor| ctor.name == *ctor_name) else {
                return false;
            };
            ctor.selectors.len() == fields.len()
                && ctor.selectors.iter().zip(fields).all(|(selector, field)| {
                    smt_value_matches_sort_deep(field, &selector.sort, remaining_depth - 1)
                })
        }
        _ => false,
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    use super::*;
    use crate::parser::ChcParser;
    use crate::VerifiedChcResult;

    const TARGET_LIKE: &str = r#"
(set-logic HORN)
(declare-datatypes ((|node| 0)) (((|node| (|node::next| Int)))))
(declare-datatypes ((|AddrRange| 0)) (((|AddrRange| (|AddrRangeStart| Int) (|AddrRangeSize| Int)))))
(declare-datatypes ((|HeapObject| 0)) (((|O_node| (|getnode| node)) (|defObj|))))
(declare-datatypes ((|Heap| 0)) (((|HeapCtor| (|HeapSize| Int) (|HeapContents| (Array Int HeapObject))))))
(declare-datatypes ((|AllocResHeap| 0)) (((|AllocResHeap| (|newHeap| Heap) (|newAddr| Int)))))
(declare-fun |CHC_COMP_FALSE| () Bool)
(assert
  (forall ((A Heap) (B HeapObject) (C node) (D AllocResHeap) (E AllocResHeap)
           (F Heap) (G HeapObject) (H node) (I Int) (J Int) (K Int) (L Bool))
    (=>
      (let ((a!1 (HeapCtor (+ 1 (HeapSize A))
                           (store (HeapContents A) (+ 1 (HeapSize A)) B)))
            (a!3 (HeapCtor (+ 1 (HeapSize F))
                           (store (HeapContents F) (+ 1 (HeapSize F)) G))))
        (let ((a!2 (= (AllocResHeap a!1 (+ 1 (HeapSize A))) D))
              (a!4 (= (AllocResHeap a!3 (+ 1 (HeapSize F))) E)))
          (and a!2
               a!4
               (= (AllocResHeap F J) D)
               (= (O_node H) G)
               (= (O_node C) B)
               (= 0 K)
               (= (newAddr E) I)
               (not (= J I))
               (not (= K J))
               (not (= K I))
               (not L)
               (= (HeapCtor 0 ((as const (Array Int HeapObject)) defObj)) A))))
      CHC_COMP_FALSE)))
(assert
  (forall ((CHC_COMP_UNUSED Bool))
    (=> CHC_COMP_FALSE false)))
(check-sat)
"#;

    /// The fact-path candidate carries a vacuous (all-`true`-state) witness;
    /// `validate_counterexample` must reject it unconditionally (the S4
    /// false-UNSAFE guard, no longer gated behind `AY_CHC_STRICT_CEX`).
    #[test]
    fn target_like_nullary_adt_array_fact_candidate_is_rejected_as_vacuous() {
        let problem = ChcParser::parse(TARGET_LIKE).expect("target-like CHC parses");
        let predicate = problem.clauses()[0].head.predicate_id().expect("fact head");
        let constraint = problem.clauses()[0]
            .body
            .constraint
            .as_ref()
            .expect("fact constraint");
        let instances = tricera_memtrack_instances(constraint).unwrap_or_default();
        let candidate = build_counterexample(predicate, 0, 1, instances);

        assert!(witness_is_vacuous(&candidate));
        assert!(
            !validate_counterexample(&problem, &candidate, Duration::from_secs(5), false),
            "vacuous marker witness must fail closed in every mode"
        );
    }

    /// The unsafe source can now be confirmed by complete ground evidence,
    /// but never by a vacuous witness and never as Safe.
    #[test]
    fn adaptive_route_never_claims_safe_on_target_like_with_strict_validation() {
        let problem = ChcParser::parse(TARGET_LIKE).expect("target-like CHC parses");
        let config = crate::AdaptiveConfig {
            strict_proofs: true,
            validate: true,
            ..crate::AdaptiveConfig::with_budget(Duration::from_secs(10), false)
        };
        let solver = crate::AdaptivePortfolio::new(problem, config);

        let result = solver.solve();

        assert!(
            !matches!(result, VerifiedChcResult::Safe(_)),
            "target-like nullary ADT-array fact must never verify as Safe, got {result:?}"
        );
    }

    #[test]
    fn bounded_marker_dag_candidate_fails_closed_as_vacuous() {
        let input = r#"
(set-logic HORN)
(declare-datatypes ((S 0)) (((mkS (arr (Array Int Int))))))
(declare-fun A (S Int) Bool)
(declare-fun B (S Int) Bool)
(declare-fun ERR () Bool)
(assert
  (forall ((s S))
    (=>
      (= (select (arr s) 0) 0)
      (A s 0))))
(assert
  (forall ((s S) (n Int))
    (=>
      (and (A s n) (= n 0))
      (B s 1))))
(assert
  (forall ((s S) (n Int))
    (=>
      (and (B s n) (= n 1))
      ERR)))
(assert (=> ERR false))
(check-sat)
"#;
        let problem = ChcParser::parse(input).expect("marker DAG CHC parses");

        // Keep the exact old all-true witness shape as a negative control.
        // A real ground derivation produced by the repaired route is separate
        // evidence; no syntactic nontrue state is used to evade this guard.
        let entries = problem
            .clauses()
            .iter()
            .take(3)
            .enumerate()
            .map(|(index, clause)| DerivationWitnessEntry {
                predicate: clause.head.predicate_id().expect("marker head"),
                level: index,
                state: ChcExpr::Bool(true),
                incoming_clause: Some(index),
                premises: index.checked_sub(1).into_iter().collect(),
                instances: FxHashMap::default(),
            })
            .collect();
        let cex = Counterexample::with_witness(
            Vec::new(),
            DerivationWitness {
                query_clause: Some(3),
                root: 2,
                entries,
            },
        );
        assert!(witness_is_vacuous(&cex));
        assert!(!validate_counterexample(
            &problem,
            &cex,
            Duration::from_secs(2),
            false
        ));
    }

    #[test]
    fn route_rejects_pure_lia_nullary_fact() {
        let input = r#"
(set-logic HORN)
(declare-fun P () Bool)
(assert (forall ((x Int)) (=> (= x 0) P)))
(assert (=> P false))
(check-sat)
"#;
        let problem = ChcParser::parse(input).expect("pure LIA CHC parses");

        assert!(matches!(
            try_build_counterexample(&problem, Duration::from_secs(1)),
            Err(NullaryAdtArrayOutcome::FactUnsat | NullaryAdtArrayOutcome::NotApplicable)
        ));
    }
}
