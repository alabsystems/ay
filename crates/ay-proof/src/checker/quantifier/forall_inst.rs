// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact, capture-safe validation for premiseless `forall_inst`.

use super::progress::QuantifierMeter;
use super::scans::{argument_has_free_name_in, argument_is_ground_for, nested_binder_names};
use super::substitution::matches_substitution;
use super::*;

type ForallInstShape<'a> = (&'a [(String, Sort)], TermId, TermId);

fn decode_forall_inst_shape<'a>(
    terms: &'a TermStore,
    _step: ProofId,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<ForallInstShape<'a>, ProofCheckError> {
    if premise_count != 0 {
        return Err(meter.invalid("must not have premises")?);
    }
    let [implication] = clause else {
        return Err(meter.invalid("conclusion must be one or-wrapped implication")?);
    };
    let TermData::App(Symbol::Named(or_name), disjuncts) = meter.term(terms, *implication)? else {
        return Err(meter.invalid("conclusion must be an or term")?);
    };
    meter.name(or_name)?;
    let implication_sort = meter.sort(terms, *implication)?;
    if !meter.sort_equal(implication_sort, &Sort::Bool)? || or_name != "or" || disjuncts.len() != 2
    {
        return Err(
            meter.invalid("conclusion must be exactly a Boolean (or (not forall) instance)")?
        );
    }
    let TermData::Not(quantified) = meter.term(terms, disjuncts[0])? else {
        return Err(meter.invalid("first disjunct must be the negated source forall")?);
    };
    let TermData::Forall(bindings, body, _) = meter.term(terms, *quantified)? else {
        return Err(meter.invalid("negated source must be a forall")?);
    };
    if bindings.is_empty() || args.len() != bindings.len() {
        return Err(
            meter.invalid("positional argument count must equal the non-empty binder count")?
        );
    }
    Ok((bindings, *body, disjuncts[1]))
}

fn checked_substitutions<'a>(
    terms: &'a TermStore,
    _step: ProofId,
    bindings: &'a [(String, Sort)],
    body: TermId,
    args: &[TermId],
    meter: &mut QuantifierMeter<'_, '_>,
) -> Result<HashMap<&'a str, TermId>, ProofCheckError> {
    let mut binder_names = HashSet::default();
    for (name, _) in bindings {
        meter.name_set_entry(&binder_names, name)?;
        if !binder_names.insert(name.as_str()) {
            return Err(meter.invalid("source forall contains duplicate binder names")?);
        }
    }
    let Some(nested_names) = nested_binder_names(terms, body, meter)? else {
        return Err(meter.invalid("nested-binder scan encounters let or unsupported term")?);
    };
    // Source binders disappear under simultaneous instantiation. In a
    // binder-free body their names may therefore denote ambient free symbols.
    // Preserve the existing conservative source-name restriction whenever
    // the body carries a nested binder (including one inside a trigger).
    let mut capturing_binders = HashSet::default();
    if !nested_names.is_empty() {
        meter.table_iteration(binder_names.len())?;
        for &name in &binder_names {
            meter.name_set_entry(&capturing_binders, name)?;
            capturing_binders.insert(name);
        }
    }
    let mut substitutions = HashMap::default();
    for ((name, sort), &argument) in bindings.iter().zip(args) {
        let argument_sort = meter.sort(terms, argument)?;
        if !meter.sort_equal(argument_sort, sort)? {
            return Err(meter.invalid("argument sort does not match its positional binder")?);
        }
        if !argument_is_ground_for(terms, argument, &capturing_binders, meter)? {
            return Err(meter.invalid("argument carries a binder or let, or names a source binder the body keeps in scope")?);
        }
        if argument_has_free_name_in(terms, argument, &nested_names, meter)? {
            return Err(
                meter.invalid("argument is unbounded or may be captured by a nested binder")?
            );
        }
        meter.name_map_entry(&substitutions, name)?;
        substitutions.insert(name.as_str(), argument);
    }
    Ok(substitutions)
}

/// Compatibility wrapper for callers without a resource callback.
pub(crate) fn validate_forall_inst(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
) -> Result<(), ProofCheckError> {
    validate_forall_inst_with_progress(terms, step, clause, premise_count, args, &mut |_, _| true)
}

/// Validate exact simultaneous instantiation within the caller's envelope.
pub(crate) fn validate_forall_inst_with_progress(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mut work = 0usize;
    let mut meter = QuantifierMeter::new(step, "forall_inst", &mut work, progress);
    meter.charge(1, 0)?;
    let (bindings, body, instance) =
        decode_forall_inst_shape(terms, step, clause, premise_count, args, &mut meter)?;
    let substitutions = checked_substitutions(terms, step, bindings, body, args, &mut meter)?;
    let instance_sort = meter.sort(terms, instance)?;
    if !meter.sort_equal(instance_sort, &Sort::Bool)? {
        return Err(meter.invalid("instantiated body must be Boolean")?);
    }
    if !matches_substitution(terms, body, instance, &substitutions, &mut meter)? {
        return Err(meter.invalid("instance is not the exact simultaneous binder substitution")?);
    }
    meter.charge(0, 0)
}
