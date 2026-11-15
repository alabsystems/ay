// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Transport search probes only between uniquely identical source owners.
//! This does not establish an invariant or replace original-source replay.

use super::super::layout::{Predicate, Step};
use super::*;

#[derive(Clone, Copy)]
struct Owner<'a> {
    argument: usize,
    prefix: &'a [Step],
}

pub(super) fn correspondence(
    id: PredicateId,
    args: &[ChcExpr],
    head: &ClauseHead,
    layout: &Layout,
    control: &SourceControl<'_>,
) -> Option<Vec<Option<usize>>> {
    let body = layout.predicate(id)?;
    control.charge(body.axes.len())?;
    let mut result = Vec::new();
    result.try_reserve_exact(body.axes.len()).ok()?;
    result.resize(body.axes.len(), None);
    let ClauseHead::Predicate(head_id, head_args) = head else {
        return Some(result);
    };
    let head = layout.predicate(*head_id)?;
    if args.len() != body.original.len() || head_args.len() != head.original.len() {
        return None;
    }
    let body_owners = owners(body, control)?;
    let head_owners = owners(head, control)?;
    control.charge(head.axes.len())?;
    let mut uses = vec![0usize; head.axes.len()];
    for (axis, owner) in body_owners.iter().enumerate() {
        let mut found = None;
        let mut ambiguous = false;
        for (target, candidate) in head_owners.iter().enumerate() {
            control.charge(1)?;
            if body.axes[axis] != head.axes[target]
                || !same_path(owner.prefix, candidate.prefix, control)?
                || !same_argument(
                    owner.argument,
                    candidate.argument,
                    body,
                    head,
                    args,
                    head_args,
                    control,
                )?
            {
                continue;
            }
            if found.replace(target).is_some() {
                ambiguous = true;
            }
        }
        if !ambiguous {
            result[axis] = found;
            if let Some(target) = found {
                uses[target] = uses[target].checked_add(1)?;
            }
        }
    }
    // Two source argument occurrences keep independent probes even when their
    // actual expressions happen to be identical. Never merge their axes.
    for target in &mut result {
        if target.is_some_and(|index| uses[index] != 1) {
            *target = None;
        }
    }
    control.poll()?;
    Some(result)
}

fn owners<'a>(predicate: &'a Predicate, control: &SourceControl<'_>) -> Option<Vec<Owner<'a>>> {
    control.charge(predicate.axes.len())?;
    let mut result = Vec::new();
    result.try_reserve_exact(predicate.axes.len()).ok()?;
    for axis in 0..predicate.axes.len() {
        let mut owner: Option<Owner<'a>> = None;
        for observation in &predicate.observations {
            control.charge(observation.path.len().checked_add(1)?)?;
            for (position, step) in observation.path.iter().enumerate() {
                if *step != Step::Axis(axis) {
                    continue;
                }
                let prefix = &observation.path[..=position];
                if let Some(previous) = owner {
                    control.charge(prefix.len())?;
                    if previous.argument != observation.argument || previous.prefix != prefix {
                        return None;
                    }
                } else {
                    owner = Some(Owner {
                        argument: observation.argument,
                        prefix,
                    });
                }
            }
        }
        result.push(owner?);
    }
    control.poll()?;
    Some(result)
}

fn same_path(left: &[Step], right: &[Step], control: &SourceControl<'_>) -> Option<bool> {
    control.charge(left.len().checked_add(right.len())?)?;
    if left.len() != right.len() {
        return Some(false);
    }
    Some(left.iter().zip(right).all(|(a, b)| match (a, b) {
        // Absolute axis IDs change with predicate argument order. Their exact
        // ancestry positions, and every intervening field ordinal, must agree.
        (Step::Axis(_), Step::Axis(_)) => true,
        (Step::Field(a), Step::Field(b)) => a == b,
        _ => false,
    }))
}

fn same_argument(
    left: usize,
    right: usize,
    body: &Predicate,
    head: &Predicate,
    args: &[ChcExpr],
    head_args: &[ChcExpr],
    control: &SourceControl<'_>,
) -> Option<bool> {
    let left_sort = body.original.get(left)?;
    let right_sort = head.original.get(right)?;
    control.bytes(sort_bytes(left_sort)?.checked_add(sort_bytes(right_sort)?)?)?;
    let left = args.get(left)?;
    let right = head_args.get(right)?;
    // Charge complete repeated DAG occurrences and recursive sort metadata
    // before structural equality; no pointer-only or semantic alias matching.
    source_premises::preflight(left, control, &mut 0)?;
    source_premises::preflight(right, control, &mut 0)?;
    let same = left_sort == right_sort && left == right;
    control.poll()?;
    Some(same)
}
