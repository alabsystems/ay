// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Allocation-free work pricing for the existing ordinary bounded RUP replay.

use super::ResolutionValidationResource as Resource;
use super::{enforce, ResolutionValidationError, ResolutionValidationLimits};
use ay_core::time::Instant;

/// Caller-authenticated upper bounds for the live original ordinary CNF.
///
/// These dimensions are not a certificate, a source binding or a resource
/// allowance. Understating any dimension invalidates the returned price.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ConservativeRupSourceShape {
    /// Upper bound for the Boolean variable namespace.
    pub num_vars: usize,
    /// Upper bound for the original clause count.
    pub original_clauses: usize,
    /// Upper bound for the original literal count.
    pub original_literals: usize,
    /// Upper bound for the width of every original clause.
    pub max_original_width: usize,
}

/// Price the deterministic meter of ordinary, non-premised bounded RUP replay.
///
/// Derived rows are borrowed dimensions `(clause length, hint count)` in their
/// actual replay order. With N variables, C original clauses, D derived rows,
/// L0 original literals, Li/Hi the current row dimensions and Mi the maximum
/// original/PRIOR-derived width, this returns the checked bound
///
/// `initial + 4*(C+D) + 3*N + L0 + 2*sum(Li)`
/// `+ sum(min(N,Li+Hi) + (min(N,Hi)+1)*Hi*(1+Mi))`.
///
/// A productive hint sweep assigns a previously unassigned variable. Each
/// hinted clause can propagate only once before becoming satisfied; hence at
/// most min(N,Hi) productive sweeps and one final sweep. Trail clearing visits
/// at most min(N,Li+Hi) assignments. Mi increases only AFTER pricing the row.
///
/// No clause, literal, hint id or semantic proof is inspected, and this never
/// validates or authorizes a DAG. Fixed-unit-premise replay is NOT covered.
/// Storage, allocation, source/CNF construction, iterator/callback work and
/// physical wall-clock/RSS closure are NOT included in the returned work.
///
/// The caller must pre-admit planning work before entry and before each
/// iterator visit on its SAME original owner. Controls are polled before and
/// after every iterator advance (including EOF), and again before returning.
/// No allocation, relative timeout, credit, retry or refund is created here.
pub fn conservative_rup_validation_work_bound(
    source: ConservativeRupSourceShape,
    mut rows: impl Iterator<Item = (usize, usize)>,
    initial_work: u64,
    limits: &ResolutionValidationLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<u64, ResolutionValidationError> {
    poll(limits, keep_going)?;
    let mut bound = Bound::new(source, initial_work, limits)?;
    loop {
        poll(limits, keep_going)?;
        let row = rows.next();
        poll(limits, keep_going)?;
        let Some((literals, hints)) = row else {
            break;
        };
        bound.admit_row(source.num_vars, literals, hints, limits)?;
    }
    poll(limits, keep_going)?;
    Ok(bound.work)
}

struct Bound {
    work: u64,
    derived: usize,
    derived_literals: usize,
    hints: usize,
    max_known_width: usize,
}

impl Bound {
    fn new(
        source: ConservativeRupSourceShape,
        initial: u64,
        limits: &ResolutionValidationLimits,
    ) -> Result<Self, ResolutionValidationError> {
        enforce(
            Resource::OriginalClauses,
            source.original_clauses,
            limits.max_original_clauses,
        )?;
        enforce(
            Resource::OriginalLiterals,
            source.original_literals,
            limits.max_original_literals,
        )?;
        let work = add(
            add(initial, mul(4, number(source.original_clauses)?)?)?,
            add(
                mul(3, number(source.num_vars)?)?,
                number(source.original_literals)?,
            )?,
        )?;
        enforce_work(work, limits)?;
        Ok(Self {
            work,
            derived: 0,
            derived_literals: 0,
            hints: 0,
            max_known_width: source.max_original_width,
        })
    }

    fn admit_row(
        &mut self,
        variables: usize,
        literals: usize,
        hints: usize,
        limits: &ResolutionValidationLimits,
    ) -> Result<(), ResolutionValidationError> {
        self.derived = super::checked_add(self.derived, 1, Resource::DerivedSteps)?;
        self.derived_literals =
            super::checked_add(self.derived_literals, literals, Resource::DerivedLiterals)?;
        self.hints = super::checked_add(self.hints, hints, Resource::Hints)?;
        enforce(
            Resource::DerivedSteps,
            self.derived,
            limits.max_derived_steps,
        )?;
        enforce(
            Resource::DerivedLiterals,
            self.derived_literals,
            limits.max_derived_literals,
        )?;
        enforce(Resource::Hints, self.hints, limits.max_hints)?;
        let reset = number(variables)?.min(add(number(literals)?, number(hints)?)?);
        let sweeps = add(number(variables)?.min(number(hints)?), 1)?;
        let hint_visits = mul(
            sweeps,
            mul(number(hints)?, add(1, number(self.max_known_width)?)?)?,
        )?;
        let row = add(
            add(4, mul(2, number(literals)?)?)?,
            add(reset, hint_visits)?,
        )?;
        self.work = add(self.work, row)?;
        enforce_work(self.work, limits)?;
        self.max_known_width = self.max_known_width.max(literals);
        Ok(())
    }
}

fn poll(
    limits: &ResolutionValidationLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<(), ResolutionValidationError> {
    if limits.deadline.is_some_and(|end| Instant::now() >= end) {
        return Err(ResolutionValidationError::DeadlineExceeded);
    }
    if !keep_going() {
        return Err(ResolutionValidationError::Cancelled);
    }
    if limits.deadline.is_some_and(|end| Instant::now() >= end) {
        return Err(ResolutionValidationError::DeadlineExceeded);
    }
    Ok(())
}

fn number(value: usize) -> Result<u64, ResolutionValidationError> {
    u64::try_from(value).map_err(|_| overflow())
}

fn add(left: u64, right: u64) -> Result<u64, ResolutionValidationError> {
    left.checked_add(right).ok_or_else(overflow)
}

fn mul(left: u64, right: u64) -> Result<u64, ResolutionValidationError> {
    left.checked_mul(right).ok_or_else(overflow)
}

fn overflow() -> ResolutionValidationError {
    ResolutionValidationError::AccountingOverflow {
        resource: Resource::Work,
    }
}

fn enforce_work(
    work: u64,
    limits: &ResolutionValidationLimits,
) -> Result<(), ResolutionValidationError> {
    if work > limits.max_work {
        return Err(ResolutionValidationError::LimitExceeded {
            resource: Resource::Work,
            limit: u128::from(limits.max_work),
            actual: u128::from(work),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests;
