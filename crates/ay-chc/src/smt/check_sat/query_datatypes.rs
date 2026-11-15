// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Query-local datatype scheduling, not datatype admission or validation.
//!
//! Scan only borrowed expression nodes and Array sort edges. Datatype metadata
//! establishes presence immediately; constructor definitions and names are not
//! traversed, hashed, compared or cloned. Executor admission remains authoritative.
//! Uninterpreted names are not resolved against a problem-level registry.

use crate::{ChcExpr, ChcSort};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use std::sync::Arc;
use std::time::Duration;

// A scheduling-work ceiling, not a new solver admission limit. Exhaustion
// selects the conservative DT schedule rather than accepting/rejecting a query.
const MAX_ROUTING_WORK: usize = 131_072;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DatatypeUse {
    Present,
    Absent,
    Indeterminate,
}

impl DatatypeUse {
    pub(super) fn needs_datatype_schedule(self) -> bool {
        !matches!(self, Self::Absent)
    }

    pub(super) fn internal_slice(self, timeout: Option<Duration>) -> Option<Duration> {
        let slice = timeout.map(|time| (time / 4).min(Duration::from_secs(2)));
        if self.needs_datatype_schedule() {
            const DT_CAP: Duration = Duration::from_millis(25);
            Some(slice.map_or(DT_CAP, |slice| slice.min(DT_CAP)))
        } else {
            slice
        }
    }
}

enum Item<'a> {
    Expr(&'a ChcExpr),
    Sort(&'a ChcSort),
}

pub(super) fn classify(expr: &ChcExpr) -> DatatypeUse {
    classify_with_limit(expr, MAX_ROUTING_WORK)
}

fn classify_with_limit(expr: &ChcExpr, limit: usize) -> DatatypeUse {
    let Some(mut remaining) = limit.min(MAX_ROUTING_WORK).checked_sub(1) else {
        return DatatypeUse::Indeterminate;
    };
    let mut pending = vec![Item::Expr(expr)];
    let mut expressions: FxHashSet<*const ChcExpr> = FxHashSet::default();
    let mut sorts: FxHashSet<*const ChcSort> = FxHashSet::default();
    // Every queued item is charged before insertion. Thus the total pending
    // items and BOTH pointer sets together cannot exceed MAX_ROUTING_WORK.
    // Pointers identify only live borrowed nodes, never structural equality.
    while let Some(item) = pending.pop() {
        let (sort, children): (Option<&ChcSort>, &[Arc<ChcExpr>]) = match item {
            Item::Expr(expr) => {
                if !expressions.insert(std::ptr::from_ref(expr)) {
                    continue;
                }
                match expr {
                    ChcExpr::ArrayLambda(_) => return DatatypeUse::Indeterminate,
                    ChcExpr::Var(variable) => (Some(&variable.sort), &[]),
                    ChcExpr::FuncApp(_, sort, children) => (Some(sort), children),
                    ChcExpr::Op(_, children) | ChcExpr::PredicateApp(_, _, children) => {
                        (None, children)
                    }
                    ChcExpr::ConstArray(key, value) => (Some(key), std::slice::from_ref(value)),
                    ChcExpr::ConstArrayMarker(key) => (Some(key), &[]),
                    ChcExpr::Bool(_)
                    | ChcExpr::Int(_)
                    | ChcExpr::Real(_, _)
                    | ChcExpr::BitVec(_, _)
                    | ChcExpr::IsTesterMarker(_) => (None, &[]),
                }
            }
            Item::Sort(sort) => {
                if !sorts.insert(std::ptr::from_ref(sort)) {
                    continue;
                }
                match sort {
                    ChcSort::Datatype { .. } => return DatatypeUse::Present,
                    ChcSort::Array(key, value) => {
                        let Some(next) = remaining.checked_sub(2) else {
                            return DatatypeUse::Indeterminate;
                        };
                        remaining = next;
                        pending.push(Item::Sort(key));
                        pending.push(Item::Sort(value));
                    }
                    ChcSort::Bool
                    | ChcSort::Int
                    | ChcSort::Real
                    | ChcSort::BitVec(_)
                    | ChcSort::Uninterpreted(_) => {}
                }
                continue;
            }
        };
        // Charge the complete fanout before growing the worklist. Even repeated
        // incoming DAG edges cost work, while each node's own fanout expands once.
        let Some(next) = remaining
            .checked_sub(children.len())
            .and_then(|left| left.checked_sub(usize::from(sort.is_some())))
        else {
            return DatatypeUse::Indeterminate;
        };
        remaining = next;
        pending.extend(children.iter().map(|child| Item::Expr(child.as_ref())));
        if let Some(sort) = sort {
            pending.push(Item::Sort(sort));
        }
    }
    DatatypeUse::Absent
}

#[cfg(test)]
mod tests;
