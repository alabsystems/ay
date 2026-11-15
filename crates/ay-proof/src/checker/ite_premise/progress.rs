// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Caller-metered counterpart of the authored-ITE structural matcher.
//!
//! This recognizes exactly the legacy branch forms; it does not authenticate
//! the caller's authored-ITE registry or add assumptions to a proof. Borrowed
//! literal/conjunct views avoid source clones. Only the bounded-depth unfolded
//! branch and its used-slot flags allocate, after checked callback charges.

use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

use crate::ProofCheckError;

mod branch;
mod meter;

use meter::Meter;

type AuthoredIte = (TermId, TermId, TermId);

/// Preserve the unmetered matcher's exact ordering and duplicate coverage.
/// A refused callback is never converted into either recognition or a miss.
pub(crate) fn assumed_is_authored_bool_ite_consequence_with_progress(
    terms: &TermStore,
    assumed: TermId,
    authored_bool_ites: &[(TermId, TermId, TermId)],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<bool, ProofCheckError> {
    let mut meter = Meter { terms, progress };
    meter.charge(0, 0)?;
    let recognized = matches_authored(assumed, authored_bool_ites, &mut meter)?;
    meter.charge(0, 0)?;
    Ok(recognized)
}

fn matches_authored(
    assumed: TermId,
    authored: &[AuthoredIte],
    meter: &mut Meter<'_, '_>,
) -> Result<bool, ProofCheckError> {
    if authored.is_empty() {
        return Ok(false);
    }
    if let TermData::App(Symbol::Named(name), args) = meter.term(assumed)? {
        if meter.named(name, "and")? && args.len() == 2 {
            for &ite in authored {
                meter.charge(1, 0)?;
                // Deliberately evaluate both sides, as the legacy matcher
                // does, even when the first is not a branch consequence.
                let first = matches_single(args[0], ite, meter)?;
                let second = matches_single(args[1], ite, meter)?;
                if let (Some(first), Some(second)) = (first, second) {
                    meter.charge(1, 0)?;
                    if first != second {
                        return Ok(true);
                    }
                }
            }
            // A two-argument conjunction can itself be a degenerate single
            // branch. Do not turn failure of the combined form into refusal.
        }
    }
    for &ite in authored {
        meter.charge(1, 0)?;
        if matches_single(assumed, ite, meter)?.is_some() {
            return Ok(true);
        }
    }
    Ok(false)
}

fn matches_single(
    assumed: TermId,
    (cond, then_term, else_term): AuthoredIte,
    meter: &mut Meter<'_, '_>,
) -> Result<Option<bool>, ProofCheckError> {
    let singleton = [assumed];
    let literals = match meter.term(assumed)? {
        TermData::App(Symbol::Named(name), args) if meter.named(name, "or")? => args.as_slice(),
        _ => &singleton,
    };
    meter.roots(literals)?;
    // Intentionally retain the old then-only Bool guard. This structural
    // helper does not broaden its role into a source-typing validator.
    if !meter.is_boolean(then_term)? {
        return Ok(None);
    }
    let single_condition = [cond];
    let conjuncts = match meter.term(cond)? {
        TermData::App(Symbol::Named(name), args)
            if meter.named(name, "and")? && !args.is_empty() =>
        {
            args.as_slice()
        }
        _ => &single_condition,
    };
    meter.roots(conjuncts)?;
    if branch::matches(literals, conjuncts, None, then_term, meter)? {
        return Ok(Some(true));
    }
    if branch::matches(literals, &[], Some(cond), else_term, meter)? {
        return Ok(Some(false));
    }
    Ok(None)
}

#[cfg(test)]
mod tests;
