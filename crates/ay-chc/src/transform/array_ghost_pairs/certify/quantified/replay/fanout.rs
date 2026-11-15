// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Debit model-substitution expansion before the legacy instantiators copy it.

use super::super::super::super::MAX_SLOTS_PER_PREDICATE;
use super::*;

#[cfg(test)]
mod tests;

// A generated index name contains a fixed prefix and at most usize's decimal
// digits. This also covers its scalar sort; Select adds one node and two edges.
const GENERATED_INDEX_BYTES: usize = 512;
const SELECT_BYTES: usize = 512;
const NODE_BYTES: usize = 256;

pub(super) fn precharge(
    model: &GhostPairModel,
    clause: &HornClause,
    control: &SourceControl<'_>,
) -> Option<()> {
    // A body trigger may come from any select/store in any clause expression,
    // not just a predicate argument. The whole root bounds every such subtree.
    let mut index_bytes = GENERATED_INDEX_BYTES;
    for expr in clause
        .body
        .constraint
        .iter()
        .chain(clause.body.predicates.iter().flat_map(|(_, args)| args))
        .chain(match &clause.head {
            ClauseHead::Predicate(_, args) => args.as_slice(),
            ClauseHead::False => &[],
        })
    {
        index_bytes = index_bytes.max(expression_bytes(expr, control)?);
    }
    if let ClauseHead::Predicate(predicate, args) = &clause.head {
        application(model, *predicate, args, index_bytes, 1, control)?;
    }
    for (predicate, args) in &clause.body.predicates {
        control.poll()?;
        // At most the retained finite cap, then one full quantified instance.
        application(
            model,
            *predicate,
            args,
            index_bytes,
            BODY_INSTANCE_CAP.checked_add(1)?,
            control,
        )?;
    }
    control.poll()
}

fn application(
    model: &GhostPairModel,
    predicate: PredicateId,
    args: &[ChcExpr],
    index_bytes: usize,
    copies: usize,
    control: &SourceControl<'_>,
) -> Option<()> {
    let interpretation = model.model.get(&predicate)?;
    let formula_bytes = expression_bytes(&interpretation.formula, control)?;
    // Each visited occurrence contributes at least NODE_BYTES. Name bytes can
    // only increase this bound; dividing avoids the spurious 256x multiplier.
    let occurrences = formula_bytes.checked_add(NODE_BYTES - 1)? / NODE_BYTES;
    let mut argument_bytes = 0usize;
    let mut largest_argument = 0usize;
    for arg in args {
        let bytes = expression_bytes(arg, control)?;
        argument_bytes = argument_bytes.checked_add(bytes)?;
        largest_argument = largest_argument.max(bytes);
    }
    let slots = model
        .spec
        .preds
        .get(&predicate)
        .map_or(0, |layout| layout.slots(model.spec.n));
    let replacement_bytes = largest_argument
        .checked_add(index_bytes)?
        .checked_add(SELECT_BYTES)?;
    let full_arguments = argument_bytes
        .checked_add(slots.checked_mul(index_bytes.checked_add(replacement_bytes)?)?)?;
    let expanded = formula_bytes
        .checked_add(occurrences.checked_mul(replacement_bytes)?)?
        .checked_add(full_arguments)?;
    control.bytes(expanded.checked_mul(copies)?)?;

    // The retained-instance cap does not itself cap temporary tuples: the
    // legacy generator constructs some candidates after the retained cap is
    // full. Charge its bounded fresh/seed/alternate/source-by-slot work too.
    if copies > 1 && slots != 0 {
        // Fresh terms belong to the head, whose slot count can exceed this
        // body's layout. Later diagonal and two-slot Cartesian candidates are
        // constructed even once the retained cap is full.
        let sources = INDEX_TERM_CAP.checked_add(MAX_SLOTS_PER_PREDICATE)?;
        let pairs = if slots == 2 {
            sources.checked_mul(sources.checked_sub(1)?)?
        } else {
            0
        };
        let tuples = 4usize
            .checked_add(slots)?
            .checked_add(sources.checked_mul(slots)?)?
            .checked_add(sources)?
            .checked_add(pairs)?;
        // Replacing one seed entry clones an additional index root.
        control.bytes(
            tuples
                .checked_mul(slots.checked_add(1)?)?
                .checked_mul(index_bytes)?,
        )?;
    }
    control.poll()
}

fn expression_bytes(expr: &ChcExpr, control: &SourceControl<'_>) -> Option<usize> {
    let mut bytes = 0;
    source_premises::preflight(expr, control, &mut bytes)?;
    Some(bytes)
}
