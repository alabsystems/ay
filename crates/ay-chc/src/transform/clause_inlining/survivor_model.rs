// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded, untrusted model candidates for a single acyclic survivor.
//! Exhaustive BMC can return no interpretations. The inliner reconstructs
//! eliminated predicates, not survivors; this fills that witness gap only.

use super::{ClauseInliner, InliningBackTranslator};
use crate::bmc::memory::Budget;
use crate::smt::{smt_deadline_expired, ScopedSmtDeadline};
use crate::{
    CancellationToken, ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause,
    InvariantModel, Predicate, PredicateInterpretation,
};
use ay_core::time::Instant;
use std::cell::Cell;

const MAX_CLAUSES: usize = 256;
const MAX_ARGUMENTS: usize = 256;
const MAX_NODES: usize = 65_536;
const MAX_DEPTH: usize = 128;

pub(crate) struct AcyclicSurvivor {
    predicate: Predicate,
    definitions: Vec<HornClause>,
}

#[derive(Debug, thiserror::Error)]
#[error("acyclic survivor reconstruction stopped")]
pub(crate) struct SurvivorSynthesisStopped;

/// A stop is terminal, unlike declining this optional synthesis route.
struct Boundary<'a> {
    deadline: Instant,
    cancellation: &'a CancellationToken,
    memory: Budget,
    stopped: Cell<bool>,
}

impl<'a> Boundary<'a> {
    fn new(deadline: Instant, cancellation: &'a CancellationToken) -> Self {
        Self {
            deadline,
            cancellation,
            memory: Budget::capture(None, None),
            stopped: Cell::new(false),
        }
    }

    fn open(&self) -> bool {
        let open = !self.stopped.get()
            && !self.cancellation.is_cancelled()
            && Instant::now() < self.deadline
            && !smt_deadline_expired()
            && self.memory.open();
        self.stopped.set(!open);
        open
    }

    fn finish<T>(&self, candidate: Option<T>) -> Result<Option<T>, SurvivorSynthesisStopped> {
        if self.open() {
            Ok(candidate)
        } else {
            Err(SurvivorSynthesisStopped)
        }
    }
}

impl ClauseInliner {
    /// Capture only bounded eligible definitions, before cloning any clauses.
    /// All live clauses, including queries, are checked; no query slice decides
    /// which incoming definitions contribute to the candidate interpretation.
    pub(crate) fn capture_acyclic_survivor_until(
        problem: &ChcProblem,
        deadline: Instant,
        cancellation: &CancellationToken,
    ) -> Result<Option<AcyclicSurvivor>, SurvivorSynthesisStopped> {
        let boundary = Boundary::new(deadline, cancellation);
        let candidate = capture(problem, &|| boundary.open());
        boundary.finish(candidate)
    }
}

fn capture(problem: &ChcProblem, open: &impl Fn() -> bool) -> Option<AcyclicSurvivor> {
    if !open()
        || problem.predicates().len() != 1
        || problem.clauses().len() > MAX_CLAUSES
        || !problem.datatype_defs().is_empty()
    {
        return None;
    }
    let predicate = problem.predicates().first()?;
    if predicate.arg_sorts.len() > MAX_ARGUMENTS || !predicate.arg_sorts.iter().all(supported_sort)
    {
        return None;
    }
    let mut definitions = Vec::new();
    for clause in problem.clauses() {
        if !open() || clause.body.predicates.len() > 1 {
            return None;
        }
        if let ClauseHead::Predicate(_, _) = &clause.head {
            // With one predicate, any defining premise would be recursive.
            if !clause.body.predicates.is_empty() {
                return None;
            }
            definitions.push(clause);
        }
    }
    if definitions.is_empty() || !open() {
        return None;
    }
    bounded_live_scalar_types(problem, open)?;
    let definitions = definitions.into_iter().cloned().collect();
    open().then(|| AcyclicSurvivor {
        predicate: predicate.clone(),
        definitions,
    })
}

impl AcyclicSurvivor {
    pub(crate) fn materialize_until(
        &self,
        deadline: Instant,
        cancellation: &CancellationToken,
    ) -> Result<Option<InvariantModel>, SurvivorSynthesisStopped> {
        // Tighten the deadline, but do NOT replace an enclosing lane's token
        // or interrupt authority. Explicit cancellation is polled around each
        // opaque projection; existing SMT calls retain the ambient lane scope.
        let _deadline = ScopedSmtDeadline::install_until(deadline);
        let boundary = Boundary::new(deadline, cancellation);
        let candidate = self.materialize(&|| boundary.open());
        boundary.finish(candidate)
    }

    fn materialize(&self, open: &impl Fn() -> bool) -> Option<InvariantModel> {
        let mut normalized = Vec::with_capacity(self.definitions.len());
        for definition in &self.definitions {
            if !open() {
                return None;
            }
            let clause = ClauseInliner::normalize_head_for_back_translation(definition);
            if !open() {
                return None;
            }
            normalized.push(clause);
        }
        let mut typed = ChcProblem::new();
        let id = typed.declare_predicate(&self.predicate.name, self.predicate.arg_sorts.clone());
        if id != self.predicate.id || !open() {
            return None;
        }
        let normalized = typed.with_raw_source_clauses(normalized).ok()?;
        bounded_live_scalar_types(&normalized, open)?;
        let clauses: Vec<_> = normalized.clauses().iter().collect();
        let empty = InvariantModel::default();
        let interpretation =
            InliningBackTranslator::synthesize_disjunctive_while(&clauses, &empty, open)?;
        if !open() || !closed_and_typed(&interpretation, &self.predicate, open) {
            return None;
        }
        // No induction/convergence flags: projection can be incomplete. Only
        // strict validation of the back-translated ORIGINAL model admits Safe.
        let mut model = InvariantModel::default();
        model.set(self.predicate.id, interpretation);
        open().then_some(model)
    }
}

fn closed_and_typed(
    interpretation: &PredicateInterpretation,
    predicate: &Predicate,
    open: &impl Fn() -> bool,
) -> bool {
    let vars = &interpretation.vars;
    if vars.len() != predicate.arg_sorts.len()
        || vars
            .iter()
            .zip(&predicate.arg_sorts)
            .any(|(var, sort)| &var.sort != sort)
        || vars
            .iter()
            .enumerate()
            .any(|(index, var)| vars[..index].iter().any(|v| v.name == var.name))
    {
        return false;
    }
    let mut remaining = MAX_NODES;
    if census(&interpretation.formula, &mut remaining, Some(vars), open).is_none() {
        return false;
    }
    let mut typed = ChcProblem::new();
    let id = typed.declare_predicate(&predicate.name, predicate.arg_sorts.clone());
    let clause = HornClause::new(
        ClauseBody::constraint(interpretation.formula.clone()),
        ClauseHead::Predicate(id, vars.iter().cloned().map(ChcExpr::var).collect()),
    );
    // Do not simplify an unvalidated synthesized expression while constructing
    // the checking surface: malformed operators must reach the strict checker.
    let Ok(typed) = typed.with_raw_source_clauses(vec![clause]) else {
        return false;
    };
    bounded_live_scalar_types(&typed, open).is_some()
}

fn supported_sort(sort: &ChcSort) -> bool {
    matches!(
        sort,
        ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(1..=256)
    )
}

/// Unlike depth-limited `vars()`/`node_count()`, a truncated census declines.
fn census<'a>(
    root: &'a ChcExpr,
    remaining: &mut usize,
    allowed: Option<&[ChcVar]>,
    open: &impl Fn() -> bool,
) -> Option<Vec<&'a ChcExpr>> {
    let mut pending = vec![(root, 0usize)];
    let mut operators = Vec::new();
    while let Some((expr, depth)) = pending.pop() {
        if !open() || depth > MAX_DEPTH || *remaining == 0 {
            return None;
        }
        *remaining -= 1;
        match expr {
            ChcExpr::PredicateApp(..)
            | ChcExpr::FuncApp(..)
            | ChcExpr::ConstArray(..)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => return None,
            ChcExpr::Real(_, 0) => return None,
            ChcExpr::Var(var) if !supported_sort(&var.sort) => return None,
            ChcExpr::BitVec(_, width) if !(1..=256).contains(width) => return None,
            ChcExpr::Var(var) if allowed.is_some_and(|vars| !vars.contains(var)) => return None,
            ChcExpr::Op(_, args) => {
                if args.len().checked_add(pending.len())? > *remaining {
                    return None;
                }
                operators.push(expr);
                pending.extend(args.iter().map(|arg| (arg.as_ref(), depth + 1)));
            }
            _ => {}
        }
    }
    Some(operators)
}

/// Structural bounds precede strict bottom-up typing; only then is `sort()`
/// safe, including inside predicate-application validation. Use the same order
/// for original definitions, normalized clauses, and synthesized candidates.
fn bounded_live_scalar_types(problem: &ChcProblem, open: &impl Fn() -> bool) -> Option<()> {
    if !open() || !problem.datatype_defs().is_empty() {
        return None;
    }
    let mut remaining = MAX_NODES;
    let mut operators = Vec::new();
    for clause in problem.clauses() {
        if !open() {
            return None;
        }
        if let Some(constraint) = &clause.body.constraint {
            operators.extend(census(constraint, &mut remaining, None, open)?);
        }
        for (_, arguments) in &clause.body.predicates {
            for argument in arguments {
                operators.extend(census(argument, &mut remaining, None, open)?);
            }
        }
        if let ClauseHead::Predicate(_, arguments) = &clause.head {
            for argument in arguments {
                operators.extend(census(argument, &mut remaining, None, open)?);
            }
        }
    }
    if !open() {
        return None;
    }
    problem.validate_live_background_theory_expressions().ok()?;
    if !open() {
        return None;
    }
    problem.validate_live_predicate_applications().ok()?;
    if !open() {
        return None;
    }
    problem.validate_live_typed_function_applications().ok()?;
    if !open() {
        return None;
    }
    for expr in operators {
        if !open() || !supported_sort(&expr.sort()) || !open() {
            return None;
        }
    }
    Some(())
}

#[cfg(test)]
mod tests;
