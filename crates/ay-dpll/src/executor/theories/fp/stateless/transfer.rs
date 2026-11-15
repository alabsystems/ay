// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Stream clauses in their original order without a second full CNF copy.

use ay_sat::Solver as SatSolver;

use crate::executor_types::UnknownOrigin;

use super::super::congruence::PlanLit;
use super::super::stop::FpStop;
use super::prepare::PreparedFp;
use super::{checkpoint, FpPhase};

fn add_clause(
    solver: &mut SatSolver,
    literals: impl IntoIterator<Item = i32>,
    stop: &FpStop,
    observe: &impl Fn(FpPhase),
) -> Result<(), UnknownOrigin> {
    checkpoint(stop, observe, FpPhase::ClauseTransfer)?;
    let mut converted = Vec::new();
    for (index, literal) in literals.into_iter().enumerate() {
        // A large input clause must not become one opaque copy interval.
        if index % 256 == 0 {
            stop.check()?;
        }
        converted.push(crate::cnf_lit_to_sat(literal));
    }
    checkpoint(stop, observe, FpPhase::SatLoad)?;
    solver.add_clause(converted);
    stop.check()
}

pub(super) fn load(
    solver: &mut SatSolver,
    prepared: &mut PreparedFp,
    stop: &FpStop,
    observe: &impl Fn(FpPhase),
) -> Result<(), UnknownOrigin> {
    stop.check()?;
    let namespace = &prepared.namespace;
    for clause in &prepared.tseitin.clauses {
        add_clause(solver, clause.literals().iter().copied(), stop, observe)?;
    }
    for clause in std::mem::take(&mut prepared.encoding.clauses) {
        add_clause(
            solver,
            clause
                .literals()
                .iter()
                .map(|&lit| namespace.offset_lit(lit)),
            stop,
            observe,
        )?;
    }
    for (tseitin_lit, fp_lit) in std::mem::take(&mut prepared.links) {
        let offset = namespace.offset_lit(fp_lit);
        add_clause(solver, [-tseitin_lit, offset], stop, observe)?;
        add_clause(solver, [tseitin_lit, -offset], stop, observe)?;
    }
    for clause in std::mem::take(&mut prepared.congruence) {
        let literals = clause.into_iter().map(|lit| match lit {
            PlanLit::Fp(fp_lit) => namespace.offset_lit(fp_lit),
            PlanLit::Tseitin(tseitin_lit) => tseitin_lit,
        });
        add_clause(solver, literals, stop, observe)?;
    }
    for (fp_var, tseitin_var) in std::mem::take(&mut prepared.encoding.pending_condition_links) {
        let offset = namespace.offset_lit(fp_var as i32);
        let tseitin_lit = tseitin_var as i32;
        add_clause(solver, [-tseitin_lit, offset], stop, observe)?;
        add_clause(solver, [tseitin_lit, -offset], stop, observe)?;
    }
    stop.check()
}
