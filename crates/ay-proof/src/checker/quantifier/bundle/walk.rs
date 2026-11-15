// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Budgeted source/assumption walks, including duplicate edges and trigger lists.

use super::meter::{insert_id, invalid_named};
use super::*;

fn record_name(
    name: &str,
    candidates: &HashMap<String, TermId>,
    found: &mut HashSet<TermId>,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<(), ProofCheckError> {
    meter.lookup(name, candidates.len())?;
    if let Some(&witness) = candidates.get(name) {
        insert_id(meter, found, witness)?;
    }
    Ok(())
}

fn push_children(
    data: &TermData,
    candidates: &HashMap<String, TermId>,
    found: &mut HashSet<TermId>,
    stack: &mut Vec<TermId>,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<(), ProofCheckError> {
    match data {
        TermData::Var(name, _) => record_name(name, candidates, found, meter)?,
        TermData::App(symbol, args) => {
            record_name(symbol.name(), candidates, found, meter)?;
            for &arg in args {
                meter.push(stack, arg)?;
            }
        }
        TermData::Let(bindings, body) => {
            for (name, value) in bindings {
                record_name(name, candidates, found, meter)?;
                meter.push(stack, *value)?;
            }
            meter.push(stack, *body)?;
        }
        TermData::Not(inner) => meter.push(stack, *inner)?,
        TermData::Ite(condition, then_branch, else_branch) => {
            for term in [*condition, *then_branch, *else_branch] {
                meter.push(stack, term)?;
            }
        }
        TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
            for (name, _) in vars {
                record_name(name, candidates, found, meter)?;
            }
            meter.push(stack, *body)?;
            for group in triggers {
                meter.charge(1, 0)?;
                for &term in group {
                    meter.push(stack, term)?;
                }
            }
        }
        TermData::Const(..) => {}
        _ => return Err(ProofCheckError::ResourceLimit),
    }
    Ok(())
}

pub(super) fn collect_candidate_witnesses(
    terms: &TermStore,
    mut stack: Vec<TermId>,
    candidates: &HashMap<String, TermId>,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<HashSet<TermId>, ProofCheckError> {
    let mut found = HashSet::default();
    let mut visited = HashSet::default();
    while let Some(term) = stack.pop() {
        if meter.seen(&mut visited, term)? {
            continue;
        }
        meter.visit()?;
        push_children(
            meter.term(terms, term)?,
            candidates,
            &mut found,
            &mut stack,
            meter,
        )?;
    }
    meter.charge(0, 0)?;
    Ok(found)
}

pub(super) fn validate_problem_freshness(
    proof: &Proof,
    terms: &TermStore,
    problem_assertions: &[TermId],
    registry: &BundleRegistry<'_>,
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<(), ProofCheckError> {
    let mut roots = Vec::new();
    for &root in problem_assertions {
        meter.push(&mut roots, root)?;
    }
    // Charge the complete proof census, not just the selected Assume roots.
    for proof_step in &proof.steps {
        meter.charge(1, 0)?;
        if let ProofStep::Assume(term) = proof_step {
            meter.push(&mut roots, *term)?;
        }
    }
    let mentioned = collect_candidate_witnesses(terms, roots, &registry.by_name, meter)?;
    meter.table_iteration(mentioned.len())?;
    let Some(witness) = mentioned.into_iter().next() else {
        return Ok(());
    };
    meter.lookup("", registry.binding_by_witness.len())?;
    let Some(binding) = registry.binding_by_witness.get(&witness).copied() else {
        return Err(meter.invalid("Skolem freshness scan references an unknown witness")?);
    };
    Err(invalid_named(meter, binding.step, "Skolem witness is not fresh: it occurs in the claimed problem obligation or an Assume step", &[&binding.name])?)
}
