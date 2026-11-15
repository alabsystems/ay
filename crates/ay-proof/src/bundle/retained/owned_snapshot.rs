// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed snapshot records, not snapshot preflight or proof acceptance.
//!
//! Every nested owner uses the same control. Record shape and transport values
//! follow the existing serde grammar; source binding, ID validity, declaration
//! consistency and certificate correctness remain mandatory reader/checker
//! duties. The enclosing reader admits the input and settles returned owners.

use super::owned_values::{
    null, owned_string, structure, tagged, tuple, u32_value, vector, Form, RawSlice, UnknownFields,
};
use super::{
    owned_annotation, owned_rule, owned_sort, owned_sos, owned_term, Control, TransportError,
};
use crate::DatatypeMemberSignature;
use ay_core::{ProofId, ProofStep, Sort, TermData};

pub(super) fn step(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<ProofStep, TransportError> {
    control.charge(1, 0)?;
    let tag = tagged(
        raw,
        &[
            "Assume",
            "Resolution",
            "TheoryLemma",
            "Step",
            "Anchor",
            "NraSos",
            "FiniteFieldLinear",
        ],
        control,
    )?;
    let raw = required(tag.payload, control)?;
    let step = match tag.index {
        0 => ProofStep::Assume(owned_term::term_id(raw, control)?),
        1 => resolution(raw, control)?,
        2 => theory(raw, control)?,
        3 => inference(raw, control)?,
        4 => anchor(raw, control)?,
        5 => {
            let [clause, certificate] = structure(
                raw,
                &["clause", "certificate"],
                UnknownFields::Reject,
                control,
            )?
            .values;
            ProofStep::NraSos {
                clause: owned_sos::clause(required(clause, control)?, control)?,
                certificate: owned_sos::certificate(required(certificate, control)?, control)?,
            }
        }
        6 => {
            let [clause, multipliers] = structure(
                raw,
                &["clause", "multipliers"],
                UnknownFields::Reject,
                control,
            )?
            .values;
            let clause = vector(
                required(clause, control)?,
                u32::MAX as usize,
                control,
                owned_term::term_id,
            )?;
            let multipliers = vector(
                required(multipliers, control)?,
                u32::MAX as usize,
                control,
                u32_value,
            )?;
            if clause.is_empty() || clause.len() != multipliers.len() {
                return control.fail(TransportError::InvalidShape(
                    "finite-field row/multiplier lengths disagree",
                ));
            }
            ProofStep::FiniteFieldLinear {
                clause,
                multipliers,
            }
        }
        _ => return control.fail(TransportError::InvalidShape("unsupported proof step")),
    };
    control.charge(0, 0)?;
    Ok(step)
}

fn resolution(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<ProofStep, TransportError> {
    let [clause, pivot, clause1, clause2] = structure(
        raw,
        &["clause", "pivot", "clause1", "clause2"],
        UnknownFields::Reject,
        control,
    )?
    .values;
    Ok(ProofStep::Resolution {
        clause: owned_term::ids(required(clause, control)?, control)?,
        pivot: owned_term::term_id(required(pivot, control)?, control)?,
        clause1: proof_id(required(clause1, control)?, control)?,
        clause2: proof_id(required(clause2, control)?, control)?,
    })
}

fn theory(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<ProofStep, TransportError> {
    let fields = structure(
        raw,
        &["theory", "clause", "farkas", "kind", "lia"],
        UnknownFields::Reject,
        control,
    )?;
    let [name, clause, farkas, kind, lia] = fields.values;
    Ok(ProofStep::TheoryLemma {
        theory: owned_string(required(name, control)?, control)?,
        clause: owned_term::ids(required(clause, control)?, control)?,
        farkas: optional(farkas, fields.form, control, owned_annotation::farkas)?,
        kind: owned_rule::theory(required(kind, control)?, control)?,
        lia: optional(lia, fields.form, control, owned_annotation::lia)?,
    })
}

fn inference(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<ProofStep, TransportError> {
    let [rule, clause, premises, args] = structure(
        raw,
        &["rule", "clause", "premises", "args"],
        UnknownFields::Reject,
        control,
    )?
    .values;
    let rule = owned_rule::alethe(required(rule, control)?, control)?;
    let clause = owned_term::ids(required(clause, control)?, control)?;
    let premises = required(premises, control)?;
    let premises = vector(premises, premises.as_str().len(), control, proof_id)?;
    let args = owned_term::ids(required(args, control)?, control)?;
    Ok(ProofStep::Step {
        rule,
        clause,
        premises,
        args,
    })
}

fn anchor(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<ProofStep, TransportError> {
    let [end_step, variables] = structure(
        raw,
        &["end_step", "variables"],
        UnknownFields::Reject,
        control,
    )?
    .values;
    let end_step = proof_id(required(end_step, control)?, control)?;
    let variables = required(variables, control)?;
    let variables = vector(
        variables,
        variables.as_str().len(),
        control,
        owned_term::binder,
    )?;
    Ok(ProofStep::Anchor {
        end_step,
        variables,
    })
}

fn proof_id(raw: RawSlice<'_>, control: &mut Control<'_>) -> Result<ProofId, TransportError> {
    u32_value(raw, control).map(ProofId)
}

pub(super) fn term_entry(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<(TermData, Sort), TransportError> {
    let [term, sort] = tuple(raw, control)?;
    let term = owned_term::read(required(term, control)?, control)?;
    let sort = owned_sort::read(required(sort, control)?, control)?;
    control.charge(0, 0)?;
    Ok((term, sort))
}

pub(super) fn named_members(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<(String, Vec<String>), TransportError> {
    let [name, members] = tuple(raw, control)?;
    let name = owned_string(required(name, control)?, control)?;
    let members = required(members, control)?;
    let members = vector(members, members.as_str().len(), control, owned_string)?;
    control.charge(0, 0)?;
    Ok((name, members))
}

pub(super) fn signature(
    raw: RawSlice<'_>,
    control: &mut Control<'_>,
) -> Result<DatatypeMemberSignature, TransportError> {
    let fields = structure(
        raw,
        &["identity", "argument_sorts", "result_sort", "nullary_term"],
        UnknownFields::Reject,
        control,
    )?;
    let [identity, arguments, result, nullary] = fields.values;
    let identity = owned_string(required(identity, control)?, control)?;
    let arguments = required(arguments, control)?;
    let argument_sorts = vector(
        arguments,
        arguments.as_str().len(),
        control,
        owned_sort::read,
    )?;
    let result_sort = owned_sort::read(required(result, control)?, control)?;
    let nullary_term = optional(nullary, fields.form, control, owned_term::term_id)?;
    control.charge(0, 0)?;
    Ok(DatatypeMemberSignature {
        identity,
        argument_sorts,
        result_sort,
        nullary_term,
    })
}

fn required<'a>(
    field: Option<RawSlice<'a>>,
    control: &mut Control<'_>,
) -> Result<RawSlice<'a>, TransportError> {
    field
        .ok_or(TransportError::InvalidShape("missing snapshot field"))
        .or_else(|error| control.fail(error))
}

/// Derived Option fields may be omitted from maps, but not from positional
/// structs. A present null is distinguished from both a missing field and a
/// present malformed value before invoking the explicit nested-owner decoder.
fn optional<'a, T>(
    field: Option<RawSlice<'a>>,
    form: Form,
    control: &mut Control<'_>,
    decode: impl FnOnce(RawSlice<'a>, &mut Control<'_>) -> Result<T, TransportError>,
) -> Result<Option<T>, TransportError> {
    control.charge(1, 0)?;
    match field {
        Some(raw) if raw.as_str() == "null" => null(raw, control).map(|()| None),
        Some(raw) => decode(raw, control).map(Some),
        None if form == Form::Object => Ok(None),
        None => control.fail(TransportError::InvalidShape(
            "missing positional Option field",
        )),
    }
}

#[cfg(test)]
mod tests;
