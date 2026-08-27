// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Metered authored-assumption closure validation.

use std::mem::size_of;

use ay_core::kani_compat::DetHashSet;
use ay_core::{Proof, ProofId, ProofStep, Symbol, TermData, TermId, TermStore};

use super::{charge_progress, checked_add_usize, checked_mul_usize};
use crate::checker::ProofCheckError;

pub(super) fn validate_problem_assumptions_metered(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mut allowed = DetHashSet::default();
    let mut stack = Vec::new();
    for &assertion in problem_assertions {
        charge_progress(
            progress,
            1,
            checked_add_usize(checked_mul_usize(size_of::<TermId>(), 2)?, 32)?,
        )?;
        if allowed.insert(assertion) {
            stack.push(assertion);
        }
    }

    // The executor may assert branch consequences of an authored Bool ITE.
    // Re-derive that closure from supplied problem roots; no producer record
    // participates in authority.
    let mut authored_bool_ites = Vec::new();
    while let Some(term) = stack.pop() {
        charge_progress(progress, 1, 0)?;
        match terms.get(term) {
            TermData::Ite(cond, then_term, else_term) => {
                charge_progress(progress, 1, checked_mul_usize(size_of::<TermId>(), 3)?)?;
                authored_bool_ites.push((*cond, *then_term, *else_term));
            }
            TermData::App(Symbol::Named(name), args) if name == "and" => {
                for &arg in args {
                    charge_progress(
                        progress,
                        1,
                        checked_add_usize(checked_mul_usize(size_of::<TermId>(), 2)?, 32)?,
                    )?;
                    if allowed.insert(arg) {
                        stack.push(arg);
                    }
                }
            }
            _ => {}
        }
    }

    for (index, step) in proof.steps.iter().enumerate() {
        charge_progress(progress, 1, 0)?;
        if let ProofStep::Assume(term) = step {
            if allowed.contains(term) {
                continue;
            }
            charge_progress(progress, authored_bool_ites.len().max(1), 0)?;
            if !crate::checker::assumed_is_authored_bool_ite_consequence(
                terms,
                *term,
                &authored_bool_ites,
            ) {
                return Err(ProofCheckError::UnauthorizedAssumption {
                    step: ProofId(index as u32),
                    term: *term,
                });
            }
        }
    }
    Ok(())
}
