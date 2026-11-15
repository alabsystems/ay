// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Recognize original scalar paths, without rewriting a composite value.

use super::layout::{Observation, Predicate, Step};
use super::*;
use crate::quantified::records::{sort_bytes, OperationKind};
use crate::{ChcExpr, ChcOp, ChcVar};
use ay_core::kani_compat::DetHashMap;

pub(super) enum AccessStep<'a> {
    Index(&'a ChcExpr),
    Field(usize),
}
pub(super) struct Access<'a> {
    pub(super) argument: usize,
    pub(super) path: Vec<AccessStep<'a>>,
}

pub(super) fn recognize<'a>(
    expr: &'a ChcExpr,
    positions: &DetHashMap<ChcVar, usize>,
    layout: &Layout,
    control: &SourceControl<'_>,
    depth: usize,
) -> Option<Access<'a>> {
    control.charge(1)?;
    if depth > crate::quantified::records::MAX_RECORD_DEPTH {
        return None;
    }
    match expr {
        ChcExpr::Var(var) => Some(Access {
            argument: *positions.get(var)?,
            path: Vec::new(),
        }),
        ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
            let mut access = recognize(&args[0], positions, layout, control, depth + 1)?;
            let ChcSort::Array(key, _) = args[0].sort() else {
                return None;
            };
            if args[1].sort() != *key {
                return None;
            }
            access.path.push(AccessStep::Index(&args[1]));
            Some(access)
        }
        ChcExpr::FuncApp(name, sort, args) if args.len() == 1 => {
            let actual = args[0].sort();
            control.bytes(sort_bytes(&actual)?)?;
            let resolved = layout.registry.resolve_application(name, &[actual]).ok()?;
            let OperationKind::Selector { field } = resolved.kind else {
                return None;
            };
            if resolved.sort != sort {
                return None;
            }
            let mut access = recognize(&args[0], positions, layout, control, depth + 1)?;
            access.path.push(AccessStep::Field(field));
            Some(access)
        }
        _ => None,
    }
}

pub(super) fn matching<'a>(
    predicate: &'a Predicate,
    access: &Access<'_>,
    argument: usize,
) -> Option<(usize, &'a Observation)> {
    predicate
        .observations
        .iter()
        .enumerate()
        .find(|(_, observation)| {
            observation.argument == argument
                && observation.path.len() == access.path.len()
                && observation
                    .path
                    .iter()
                    .zip(&access.path)
                    .all(|(step, actual)| {
                        matches!((step, actual), (Step::Axis(_), AccessStep::Index(_)))
                            || matches!((step, actual),
                (Step::Field(left), AccessStep::Field(right)) if left == right)
                    })
        })
}

/// Complete scalar-access census. Unsupported composite uses remain untouched
/// in the original clause but cannot be a source for this scalar candidate.
pub(super) fn collect<'a>(
    expr: &'a ChcExpr,
    positions: &DetHashMap<ChcVar, usize>,
    layout: &Layout,
    control: &SourceControl<'_>,
) -> Option<Vec<Access<'a>>> {
    source_premises::preflight(expr, control, &mut 0)?;
    let mut pending = vec![(expr, 0usize)];
    let mut accesses = Vec::new();
    while let Some((node, depth)) = pending.pop() {
        control.charge(1)?;
        if depth > crate::quantified::records::MAX_RECORD_DEPTH {
            return None;
        }
        if layout::scalar(&node.sort()) {
            if let Some(access) = recognize(node, positions, layout, control, 0) {
                if !access.path.is_empty() {
                    accesses.push(access);
                    continue;
                }
            }
        }
        match node {
            ChcExpr::Var(var) if layout::scalar(&var.sort) => {}
            ChcExpr::Bool(_) | ChcExpr::BitVec(_, _) => {}
            ChcExpr::Op(op, args) if !matches!(op, ChcOp::Select | ChcOp::Store) => {
                control.charge(args.len())?;
                pending.extend(args.iter().rev().map(|arg| (arg.as_ref(), depth + 1)));
            }
            _ => return None,
        }
    }
    control.poll()?;
    Some(accesses)
}
