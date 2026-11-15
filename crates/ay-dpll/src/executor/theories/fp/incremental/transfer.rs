// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Keep global definitions and scoped activations in the same disposable trial.

use ay_core::TermId;
use ay_sat::Solver as SatSolver;

use crate::executor_types::UnknownOrigin;
use crate::incremental_state::IncrementalFpState;

use super::super::stop::FpStop;
use super::prepare::PreparedIncrementalFp;
use super::{checkpoint, IncrementalFpPhase};

fn offset(literal: i32, delta: i32, stop: &FpStop) -> Result<i32, UnknownOrigin> {
    let translated = if literal > 0 {
        literal.checked_add(delta)
    } else {
        literal.checked_sub(delta)
    };
    translated.ok_or_else(|| stop.refuse(UnknownOrigin::DeterministicResourceBudget))
}

fn global_clause(
    solver: &mut SatSolver,
    literals: impl IntoIterator<Item = Result<i32, UnknownOrigin>>,
    phase: IncrementalFpPhase,
    stop: &FpStop,
    observe: &impl Fn(IncrementalFpPhase),
) -> Result<(), UnknownOrigin> {
    checkpoint(stop, observe, phase)?;
    let mut converted = Vec::new();
    for (index, literal) in literals.into_iter().enumerate() {
        if index % 256 == 0 {
            stop.check()?;
        }
        converted.push(crate::cnf_lit_to_sat(literal?));
    }
    stop.check()?;
    solver.add_clause_global(converted);
    stop.check()
}

fn equivalence(
    solver: &mut SatSolver,
    tseitin: i32,
    fp: i32,
    phase: IncrementalFpPhase,
    stop: &FpStop,
    observe: &impl Fn(IncrementalFpPhase),
) -> Result<(), UnknownOrigin> {
    global_clause(solver, [Ok(-tseitin), Ok(fp)], phase, stop, observe)?;
    global_clause(solver, [Ok(tseitin), Ok(-fp)], phase, stop, observe)
}

pub(super) fn load(
    solver: &mut SatSolver,
    trial: &mut IncrementalFpState,
    prepared: &mut PreparedIncrementalFp,
    assertions: &[TermId],
    stop: &FpStop,
    observe: &impl Fn(IncrementalFpPhase),
) -> Result<(), UnknownOrigin> {
    stop.check()?;
    for clause in std::mem::take(&mut prepared.definitions) {
        global_clause(
            solver,
            clause.literals().iter().copied().map(Ok),
            IncrementalFpPhase::GlobalDefinition,
            stop,
            observe,
        )?;
    }
    for clause in std::mem::take(&mut prepared.fp_clauses) {
        global_clause(
            solver,
            clause
                .literals()
                .iter()
                .map(|&lit| offset(lit, prepared.offset, stop)),
            IncrementalFpPhase::GlobalFpClause,
            stop,
            observe,
        )?;
    }
    for (tseitin, fp) in std::mem::take(&mut prepared.predicate_links) {
        equivalence(
            solver,
            tseitin,
            offset(fp, prepared.offset, stop)?,
            IncrementalFpPhase::PredicateLink,
            stop,
            observe,
        )?;
    }
    for (fp, tseitin) in std::mem::take(&mut prepared.condition_links) {
        let fp = i32::try_from(fp)
            .map_err(|_| stop.refuse(UnknownOrigin::DeterministicResourceBudget))?;
        let tseitin = i32::try_from(tseitin)
            .map_err(|_| stop.refuse(UnknownOrigin::DeterministicResourceBudget))?;
        equivalence(
            solver,
            tseitin,
            offset(fp, prepared.offset, stop)?,
            IncrementalFpPhase::ConditionLink,
            stop,
            observe,
        )?;
    }
    for (tseitin, fp) in std::mem::take(&mut prepared.bool_links) {
        equivalence(
            solver,
            tseitin,
            offset(fp, prepared.offset, stop)?,
            IncrementalFpPhase::BoolLink,
            stop,
            observe,
        )?;
    }
    // These root units, and only these, belong to the current scope. Global
    // definitions stay valid after pop; activation records do not.
    for &assertion in assertions {
        stop.check()?;
        let Some(&root) = trial.encoded_assertions.get(&assertion) else {
            continue;
        };
        if trial
            .assertion_activation_scope
            .get(&assertion)
            .is_none_or(|&depth| depth > trial.scope_depth)
        {
            checkpoint(stop, observe, IncrementalFpPhase::Activation)?;
            solver.add_clause(vec![crate::cnf_lit_to_sat(root)]);
            trial
                .assertion_activation_scope
                .insert(assertion, trial.scope_depth);
            stop.check()?;
        }
    }
    stop.check()
}
