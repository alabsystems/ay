// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Attach real read constraints, retaining their independent proof obligations.

use super::*;
use ay_arrays::counted_reads::Unresolved;

pub(super) fn encoder<'scope>(
    context: Context<'scope, '_>,
    cnf: &'scope CountedCnf<'scope>,
) -> Result<CountedBvEncoder<'scope>> {
    match context.array_reads() {
        Some(closure) => {
            closure.validate_source(cnf.terms())?;
            for obligation in closure.unresolved() {
                context.admission().admit(1, 0)?;
                if matches!(obligation, Unresolved::ArrayRelation { .. }) {
                    // Array equality/extensionality cannot be replaced by a
                    // scalar Boolean gate, even in an inactive source arm.
                    return Err(Error::Unsupported);
                }
            }
            CountedBvEncoder::with_array_reads(cnf.terms(), closure).map_err(bv_error)
        }
        None => CountedBvEncoder::new(cnf.terms(), context.admission()).map_err(bv_error),
    }
}

pub(super) fn roots(context: Context<'_, '_>, roots: &mut Vec<TermId>) -> Result<()> {
    let owner = context.admission();
    if let Some(closure) = context.array_reads() {
        for read in closure.reads() {
            owner.admit(1, 0)?;
            memory::push(roots, read.index, owner)?;
            memory::push(roots, read.select, owner)?;
        }
        for step in closure.steps() {
            owner.admit(1, 0)?;
            for &literal in step.literals() {
                memory::push(roots, literal, owner)?;
            }
        }
        // Original scalar variables in otherwise inactive array constructors
        // also belong to candidate replay. Never manufacture their values.
        for binding in context.bindings() {
            owner.admit(1, 0)?;
            if !matches!(&binding.original.sort, crate::ChcSort::Array(..)) {
                memory::push(roots, binding.term, owner)?;
            }
        }
    }
    Ok(())
}

pub(super) fn append(
    context: Context<'_, '_>,
    bv: &CountedBvEncoder<'_>,
    offset: u32,
    rows: &mut Vec<AttachedRow>,
) -> Result<()> {
    if let Some(closure) = context.array_reads() {
        for (index, step) in closure.steps().iter().enumerate() {
            context.admission().admit(1, 0)?;
            let mut literals = [0i32; 2];
            for (slot, &source) in literals.iter_mut().zip(step.literals()) {
                *slot = bv.literal(source).map_err(bv_error)?;
            }
            attachment::append(
                rows,
                &literals[..step.literals().len()],
                offset,
                RowOrigin::ArrayRead(index),
                context.admission(),
            )?;
        }
    }
    Ok(())
}
