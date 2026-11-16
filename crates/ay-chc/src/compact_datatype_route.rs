// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Candidate-only, demand-driven witnesses for finite product datatypes.
//!
//! A selected linear Horn path is existentially instantiated. Equal predicate
//! columns identify original variables; only scalar selector observations are
//! sent to SMT. Unobserved fields are NOT removed from the evidence: canonical
//! complete product defaults and path-copy overrides reconstruct every field.
//! The independent compact checker then evaluates the ORIGINAL clauses.
//! No absence of a candidate proves safety. This is not a counted SMT API.

use crate::ground_derivation::compact::{self, CompactDerivation, Error, Owner};
use crate::{ChcProblem, SmtContext, SmtResult};

pub(crate) mod acceptance;
mod materialize;
mod paths;
mod project;
mod variables;

#[cfg(test)]
mod tests;

type Result<T> = std::result::Result<T, Error>;
const MAX_DEPTH: usize = 128;

/// The caller captures `Owner` before source inspection and retains it through
/// artifact transport and final publication. No deadline/allowance is minted.
pub(crate) fn derive(
    problem: &ChcProblem,
    owner: &mut Owner<'_>,
) -> Result<Option<CompactDerivation>> {
    let result = (|| {
        owner.admit(1, 0)?;
        if problem.has_stripped_body_forall() {
            return Err(Error::Unsupported);
        }
        compact::validate_source(problem, owner)?;
        paths::search(problem, owner)
    })();
    if let Err(error @ (Error::Stopped | Error::Resource)) = result {
        return owner.refuse(error);
    }
    owner.poll()?;
    result
}

fn candidate(
    problem: &ChcProblem,
    path: &[usize],
    owner: &mut Owner<'_>,
) -> Result<Option<CompactDerivation>> {
    let variables = variables::Variables::new(problem, path, owner)?;
    let projection = project::Projection::new(problem, path, &variables, owner)?;
    owner.poll()?;
    let entered = owner.enter();
    let mut smt = SmtContext::new();
    let result = match owner.remaining() {
        Some(remaining) if remaining.is_zero() => return owner.refuse(Error::Stopped),
        Some(remaining) => smt.check_sat_with_timeout(&projection.formula, remaining),
        None => smt.check_sat(&projection.formula),
    };
    drop(smt);
    drop(entered);
    owner.poll()?;
    let SmtResult::Sat(model) = result else {
        // Even UNSAT only rejects this selected path. Unknown never becomes a
        // proof, nor permits a new owner or replenished resource grant.
        return Ok(None);
    };
    let derivation = materialize::build(problem, path, &variables, &projection, &model, owner)?;
    compact::validate(problem, &derivation, owner)?;
    drop(model);
    drop(projection);
    drop(variables);
    owner.poll()?;
    Ok(Some(derivation))
}

fn reserve<T>(items: &mut Vec<T>, count: usize, owner: &mut Owner<'_>) -> Result<()> {
    let bytes = count
        .checked_mul(std::mem::size_of::<T>())
        .ok_or(Error::Resource)?;
    owner.admit(count, bytes)?;
    if items.try_reserve(count).is_err() {
        return owner.refuse(Error::Resource);
    }
    Ok(())
}

fn text(source: &str, owner: &mut Owner<'_>) -> Result<String> {
    owner.admit(source.len(), source.len())?;
    let mut result = String::new();
    if result.try_reserve(source.len()).is_err() {
        return owner.refuse(Error::Resource);
    }
    result.push_str(source);
    Ok(result)
}
