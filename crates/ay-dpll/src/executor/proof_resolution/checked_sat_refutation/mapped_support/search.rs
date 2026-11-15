// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Small, controlled SAT search used only to decline an untranslatable proof.

use super::*;
use std::cell::RefCell;

/// Callback observations survive recovery of a live flag or RSS reading. SAT's
/// own typed stop is also retained: it can observe controls between callbacks.
struct SatStop<'a> {
    meter: RefCell<&'a mut CheckedRefutationMeter>,
    stopped: RefCell<Option<ScreenFailure>>,
}

impl<'a> SatStop<'a> {
    fn new(meter: &'a mut CheckedRefutationMeter) -> Self {
        Self {
            meter: RefCell::new(meter),
            stopped: RefCell::new(None),
        }
    }

    fn should_stop(&self) -> bool {
        if self.stopped.borrow().is_some() {
            return true;
        }
        if let Err(error) = self.meter.borrow_mut().charge(1, 0) {
            *self.stopped.borrow_mut() = Some(error.into());
            return true;
        }
        false
    }

    fn finish(self, reason: Option<ay_sat::SatUnknownReason>) -> ScreenResult<()> {
        if reason == Some(ay_sat::SatUnknownReason::DeadlineExceeded) {
            return Err(ResolutionValidationError::DeadlineExceeded.into());
        }
        if let Some(error) = self.stopped.into_inner() {
            // Our own local debit can stop SAT via its callback. That is an
            // ordinary screen decline, not an externally observed interrupt.
            return Err(error);
        }
        if reason == Some(ay_sat::SatUnknownReason::Interrupted) {
            return Err(ResolutionValidationError::Cancelled.into());
        }
        Ok(())
    }
}

/// The namespace depends only on admitted occurrences, never solver_num_vars.
fn dense_variables(
    clauses: &[&[Literal]],
    premises: &[Literal],
    meter: &mut CheckedRefutationMeter,
) -> ScreenResult<Vec<u32>> {
    meter.charge(clauses.len(), 0)?;
    if clauses.len().saturating_add(premises.len()) > MAX_SCREEN_CLAUSES {
        return Err(ScreenFailure::Decline);
    }
    let mut count = premises.len();
    for clause in clauses {
        count = count
            .checked_add(clause.len())
            .ok_or(ScreenFailure::Decline)?;
        if count > MAX_SCREEN_LITERALS {
            return Err(ScreenFailure::Decline);
        }
    }
    if count > MAX_SCREEN_LITERALS {
        return Err(ScreenFailure::Decline);
    }
    let mut variables = screen_vec(count, meter)?;
    for clause in clauses.iter().copied().chain(std::iter::once(premises)) {
        for chunk in clause.chunks(256) {
            meter.charge(chunk.len(), 0)?;
            variables.extend(
                chunk
                    .iter()
                    .map(|literal| literal.variable().index() as u32),
            );
        }
    }
    // Sorting is an opaque but shape-bounded interval; admit its comparisons
    // and the following dedup scan before either starts.
    meter.charge(count * (2 * search_work(count) + 1), 0)?;
    variables.sort_unstable();
    variables.dedup();
    meter.charge(0, 0)?;
    if variables.len() > MAX_SCREEN_VARIABLES {
        return Err(ScreenFailure::Decline);
    }
    Ok(variables)
}

fn dense_literal(literal: Literal, variables: &[u32]) -> ScreenResult<Literal> {
    let index = variables
        .binary_search(&(literal.variable().index() as u32))
        .map_err(|_| ScreenFailure::Decline)?;
    let variable = Variable::new(u32::try_from(index).map_err(|_| ScreenFailure::Decline)?);
    Ok(if literal.is_positive() {
        Literal::positive(variable)
    } else {
        Literal::negative(variable)
    })
}

fn add_clause(
    solver: &mut ay_sat::Solver,
    clause: &[Literal],
    variables: &[u32],
    meter: &mut CheckedRefutationMeter,
) -> ScreenResult<()> {
    meter.charge(clause.len() * search_work(variables.len()), 0)?;
    let mut renamed = screen_vec(clause.len(), meter)?;
    for chunk in clause.chunks(256) {
        meter.charge(chunk.len(), 0)?;
        for &literal in chunk {
            renamed.push(dense_literal(literal, variables)?);
        }
    }
    solver.add_clause(renamed);
    meter.charge(0, 0)?;
    Ok(())
}

/// Check the returned assignment against the BORROWED original clauses and
/// units, independently of SAT's renamed clause storage or result status.
fn model_satisfies(
    model: &[bool],
    variables: &[u32],
    clauses: &[&[Literal]],
    premises: &[Literal],
    meter: &mut CheckedRefutationMeter,
) -> ScreenResult<bool> {
    for clause in premises
        .iter()
        .map(std::slice::from_ref)
        .chain(clauses.iter().copied())
    {
        meter.charge(1, 0)?;
        let mut satisfied = false;
        for &literal in clause {
            meter.charge(search_work(variables.len()), 0)?;
            let dense = dense_literal(literal, variables)?;
            if model
                .get(dense.variable().index())
                .is_some_and(|&value| value == dense.is_positive())
            {
                satisfied = true;
                break;
            }
        }
        if !satisfied {
            return Ok(false);
        }
    }
    Ok(true)
}

pub(super) fn mapped_originals_satisfiable(
    clauses: &[&[Literal]],
    premises: &[Literal],
    meter: &mut CheckedRefutationMeter,
    interrupt: Option<Arc<AtomicBool>>,
) -> ScreenResult<bool> {
    let variables = dense_variables(clauses, premises, meter)?;
    let count = variables.len().max(1);
    let clause_count = clauses.len() + premises.len();
    meter.charge(clauses.len(), 0)?;
    let literal_count = clauses.iter().map(|clause| clause.len()).sum::<usize>() + premises.len();
    // Price the bounded solver shape before its infallible internal allocations:
    // variable state, input storage, and allowance for conflict-learned clauses.
    // This is a conservative admission price, NOT a hard allocator/RSS bound.
    // Individual SAT allocations and BCP remain opaque; the caller's memory
    // ceiling is polled before/after construction, additions and during solve.
    let solver_bytes = count * 4_096
        + clause_count * 64
        + literal_count * 16
        + MAPPED_SUPPORT_CONFLICT_BUDGET as usize * (64 + count * 16);
    meter.charge(count + clause_count + literal_count, solver_bytes)?;
    let mut solver = ay_sat::Solver::with_clause_hint(count, clause_count);
    meter.charge(0, 0)?;
    solver.set_preprocess_enabled(false);
    solver.disable_all_inprocessing();
    solver.set_walk_enabled(false);
    solver.set_solve_deadline(meter.limits.deadline);
    solver.set_interrupt_handle(interrupt);
    solver.set_conflict_budget(Some(MAPPED_SUPPORT_CONFLICT_BUDGET));
    solver.set_decision_budget(Some(MAPPED_SUPPORT_DECISION_BUDGET));
    for clause in clauses {
        add_clause(&mut solver, clause, &variables, meter)?;
    }
    for premise in premises {
        add_clause(
            &mut solver,
            std::slice::from_ref(premise),
            &variables,
            meter,
        )?;
    }
    let stop = SatStop::new(meter);
    let result = solver.solve_interruptible(|| stop.should_stop());
    stop.finish(solver.last_unknown_reason())?;
    meter.charge(0, 0)?;
    match result.model() {
        Some(model) => model_satisfies(model, &variables, clauses, premises, meter),
        None => Ok(false),
    }
}

#[cfg(test)]
#[path = "search_tests.rs"]
mod tests;
