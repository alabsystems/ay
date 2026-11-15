// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Bounded source-sort traversal; constructor and selector order is unchanged.
//!
//! The work model follows the normalized identity's spelling: a datatype
//! occurrence costs its reference, and each distinct constructor list is
//! priced once for its single definition, never once per tree occurrence.

use super::*;
use crate::{ChcDtConstructors, ChcDtId};
use ay_core::kani_compat::DetHashSet as FxHashSet;

pub(super) fn source_bitvector_width_work(
    width: u32,
) -> Result<usize, ChcGroundDerivationArtifactError> {
    if width == 0 || width > crate::MAX_BITVECTOR_WIDTH {
        return Err(source_identity_error(format!(
            "source bitvector width {width} is outside 1..={}",
            crate::MAX_BITVECTOR_WIDTH
        )));
    }
    // Whole-problem identity and namespace passes render only this bounded
    // decimal width; they never allocate a `width`-bit value or mask. Selected
    // ground replay charges ceil(width/8) separately before evaluation.
    Ok(16)
}

/// Constructor lists already priced. The normalized identity spells a
/// datatype by reference at every occurrence and defines each list once.
#[derive(Default)]
pub(super) struct PricedDatatypes(FxHashSet<ChcDtId>);

/// One reference, beyond the name's own bytes: `Datatype(` (9), the name's
/// JSON quotes (2), `;@` (2), the 64 hex digits of its id and `)` (1).
const DATATYPE_REFERENCE_WORK: usize = 78;

/// One definition line, beyond its constructor parts: `constructors @` (14),
/// the 64 hex digits of the id, `=` (1) and the newline (1).
const DATATYPE_DEFINITION_WORK: usize = 80;

fn preflight_source_identity_sort<'a>(
    control: &mut GroundValidationControl<'_>,
    root: &'a ChcSort,
    work: &mut usize,
    priced: &mut PricedDatatypes,
    definitions: &mut Vec<&'a ChcDtConstructors>,
) -> Result<(), ChcGroundDerivationArtifactError> {
    control.poll().map_err(interruption_error)?;
    let mut stack = vec![(root, 1usize)];
    while let Some((sort, depth)) = stack.pop() {
        control.poll().map_err(interruption_error)?;
        if depth > CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH {
            return Err(source_identity_error(
                "whole-problem source sort exceeds depth bound",
            ));
        }
        // `normalized_sort` constructs child strings bottom-up. Weight every
        // node and name by its sort-ancestor depth so a deep sort's repeated
        // copying is admitted only when the fixed envelope dominates it.
        charge_source_identity_work(
            control,
            work,
            32usize
                .checked_mul(depth)
                .ok_or_else(|| source_identity_error("source sort node work overflow"))?,
        )?;
        match sort {
            ChcSort::Array(index, value) => {
                charge_source_identity_work(
                    control,
                    work,
                    2usize
                        .checked_mul(depth)
                        .ok_or_else(|| source_identity_error("source array sort work overflow"))?,
                )?;
                let child_depth = depth.checked_add(1).ok_or_else(|| {
                    source_identity_error("whole-problem source sort depth overflow")
                })?;
                stack.push((index, child_depth));
                stack.push((value, child_depth));
            }
            ChcSort::Uninterpreted(name) => charge_source_identity_work(
                control,
                work,
                name.len().checked_mul(depth).ok_or_else(|| {
                    source_identity_error("source uninterpreted-sort name work overflow")
                })?,
            )?,
            ChcSort::Datatype { name, constructors } => {
                // A reference: the definition is priced once, at top level.
                charge_source_identity_work(
                    control,
                    work,
                    name.len()
                        .checked_add(DATATYPE_REFERENCE_WORK)
                        .and_then(|amount| amount.checked_mul(depth))
                        .ok_or_else(|| source_identity_error("source datatype work overflow"))?,
                )?;
                if priced.0.insert(constructors.id()) {
                    definitions.push(constructors);
                }
            }
            ChcSort::BitVec(width) => charge_source_identity_work(
                control,
                work,
                source_bitvector_width_work(*width)?
                    .checked_mul(depth)
                    .ok_or_else(|| source_identity_error("source bitvector sort work overflow"))?,
            )?,
            ChcSort::Bool | ChcSort::Int | ChcSort::Real => {}
        }
    }
    Ok(())
}

pub(super) fn preflight_source_identity_sort_multiplied(
    control: &mut GroundValidationControl<'_>,
    root: &ChcSort,
    work: &mut usize,
    multiplier: usize,
    priced: &mut PricedDatatypes,
) -> Result<(), ChcGroundDerivationArtifactError> {
    let starting_work = *work;
    let mut definitions = Vec::new();
    preflight_source_identity_sort(control, root, work, priced, &mut definitions)?;
    let sort_work = work
        .checked_sub(starting_work)
        .ok_or_else(|| source_identity_error("whole-problem sort work underflow"))?;
    let additional = multiplier
        .checked_sub(1)
        .and_then(|multiplier| sort_work.checked_mul(multiplier))
        .ok_or_else(|| source_identity_error("whole-problem sort identity work overflow"))?;
    charge_source_identity_work(control, work, additional)?;
    // Each newly referenced list is spelled once, however often it occurs.
    while let Some(constructors) = definitions.pop() {
        price_definition(control, constructors, work, priced, &mut definitions)?;
    }
    Ok(())
}

/// One `constructors @<id>=...` line: its names, and its selector sorts
/// spelled from the top level.
fn price_definition<'a>(
    control: &mut GroundValidationControl<'_>,
    constructors: &'a ChcDtConstructors,
    work: &mut usize,
    priced: &mut PricedDatatypes,
    definitions: &mut Vec<&'a ChcDtConstructors>,
) -> Result<(), ChcGroundDerivationArtifactError> {
    charge_source_identity_work(
        control,
        work,
        DATATYPE_DEFINITION_WORK
            .checked_add(constructors.len())
            .ok_or_else(|| source_identity_error("source datatype definition work overflow"))?,
    )?;
    for constructor in constructors.iter() {
        charge_source_identity_work(
            control,
            work,
            constructor
                .name
                .len()
                .checked_add(constructor.selectors.len())
                .ok_or_else(|| source_identity_error("source constructor work overflow"))?,
        )?;
        for selector in &constructor.selectors {
            charge_source_identity_work(control, work, selector.name.len())?;
            preflight_source_identity_sort(control, &selector.sort, work, priced, definitions)?;
        }
    }
    Ok(())
}
