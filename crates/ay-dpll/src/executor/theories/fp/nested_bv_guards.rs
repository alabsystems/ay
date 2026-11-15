// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Name hidden BV predicates before FP takes its immutable Tseitin map.
//!
//! The outer Boolean walk stops at theory atoms. A BV predicate below a
//! numeric ITE therefore needs a name even when it is not an asserted root.
//! Only existing, typed builtin BV predicates are seeded here: their actual
//! definitions come from the shared FP predicate dispatch and its usual links.
//! No predicate or ITE condition is asserted. Other guards keep the existing
//! FP connective/foreign-function handling and fail-closed encoding-gap rules.
//! Every seeding route builds its FP solver with
//! `FpSolver::new_with_seeded_tseitin`, so a hidden predicate this walk leaves
//! unnamed (one below a binder) keeps the gap instead of DR-47's circuit.

use ay_core::kani_compat::DetHashSet;
use ay_core::{Sort, Symbol, TermData, TermId, TermStore, Tseitin};

use crate::executor_types::UnknownOrigin;

use super::stop::FpStop;

pub(super) fn seed(
    terms: &TermStore,
    roots: impl IntoIterator<Item = TermId>,
    tseitin: &mut Tseitin<'_>,
    stop: &FpStop,
    observe: &impl Fn(),
) -> Result<(), UnknownOrigin> {
    stop.check()?;
    let result = walk(terms, roots, tseitin, stop, observe);
    // Walk scratch is gone before any definitions can be published.
    stop.check()?;
    result
}

fn walk(
    terms: &TermStore,
    roots: impl IntoIterator<Item = TermId>,
    tseitin: &mut Tseitin<'_>,
    stop: &FpStop,
    observe: &impl Fn(),
) -> Result<(), UnknownOrigin> {
    let mut stack = Vec::new();
    let mut seen = DetHashSet::default();
    for root in roots {
        push(&mut stack, root, stop)?;
    }
    while let Some(term) = stack.pop() {
        stop.check()?;
        observe();
        stop.check()?;
        if terms.entry_stamp(term).is_none() {
            return Err(stop.refuse(UnknownOrigin::DeterministicResourceBudget));
        }
        if seen.contains(&term) {
            continue;
        }
        seen.try_reserve(1)
            .map_err(|_| stop.refuse(UnknownOrigin::MemoryBudget))?;
        seen.insert(term);
        match terms.get(term) {
            TermData::App(symbol, args) => {
                for &child in args {
                    push(&mut stack, child, stop)?;
                }
                if supported(terms, term, symbol, args) {
                    stop.check()?;
                    let _definition = tseitin.encode_root(term);
                    stop.check()?;
                }
            }
            TermData::Ite(condition, then_term, else_term) => {
                for child in [*condition, *then_term, *else_term] {
                    push(&mut stack, child, stop)?;
                }
            }
            TermData::Not(inner) => push(&mut stack, *inner, stop)?,
            // Never turn a bound variable into a fresh global predicate.
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => {}
            TermData::Var(..) | TermData::Const(..) => {}
            _ => {}
        }
    }
    stop.check()
}

fn push(stack: &mut Vec<TermId>, term: TermId, stop: &FpStop) -> Result<(), UnknownOrigin> {
    stop.check()?;
    stack
        .try_reserve(1)
        .map_err(|_| stop.refuse(UnknownOrigin::MemoryBudget))?;
    stack.push(term);
    Ok(())
}

fn supported(terms: &TermStore, term: TermId, symbol: &Symbol, args: &[TermId]) -> bool {
    let Symbol::Named(name) = symbol else {
        return false;
    };
    if args.len() != 2
        || terms.sort(term) != &Sort::Bool
        || terms.is_declared_function(name)
        || !matches!(
            name.as_str(),
            "=" | "distinct"
                | "bvult"
                | "bvule"
                | "bvugt"
                | "bvuge"
                | "bvslt"
                | "bvsle"
                | "bvsgt"
                | "bvsge"
        )
        || args.iter().any(|&arg| terms.entry_stamp(arg).is_none())
    {
        return false;
    }
    matches!(terms.sort(args[0]), Sort::BitVec(sort) if sort.width > 0)
        && terms.sort(args[0]) == terms.sort(args[1])
}

#[cfg(test)]
mod tests;
