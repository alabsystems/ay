// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded borrowed identity census and independent translator accounting.

use std::collections::BTreeMap;

use ay_bindings::{Expr, ExprValue};
use ay_core::original_query::WorkBudget;

use super::{typed, FpAdapterError, FpExprInputBinding};

pub(super) const MAX_NODES: usize = 500;
pub(super) const MAX_DEPTH: usize = 64;
const MAX_OCCURRENCES: usize = 4096;
const MAX_NAME: usize = 256;
pub(super) const COMMON: usize = 7;

#[derive(Clone, Copy)]
struct Count {
    occurrences: usize,
    height: usize,
    kind: typed::Scalar,
}
enum Visit {
    Active,
    Done(Count, usize),
}

pub(super) struct Plan<'a> {
    pub nodes: Vec<&'a Expr>,
    seen: BTreeMap<usize, Visit>,
}

pub(super) fn identity(expr: &Expr) -> usize {
    // Identity only inside this borrowed immutable graph, never semantic Eq,
    // proof identity or a pointer dereference. Original Expr keeps the Arc live.
    expr.value() as *const ExprValue as usize
}

impl Plan<'_> {
    pub fn index(&self, expr: &Expr) -> Result<usize, FpAdapterError> {
        match self.seen.get(&identity(expr)) {
            Some(Visit::Done(_, index)) => Ok(*index),
            _ => Err(FpAdapterError::Invalid("missing typed source identity")),
        }
    }

    pub fn prepay(&self, budget: &mut WorkBudget<'_>) -> Result<(), FpAdapterError> {
        let n = self
            .nodes
            .len()
            .checked_add(COMMON)
            .ok_or_else(|| budget.refuse_exhaustion())?;
        // Separate translator fee, not reused native gate pricing. At <=507
        // entries and arity64/name256, N²*1024 dominates bounded tree lookups,
        // record construction, payload/ID copying and both arena disposals.
        // N*8192+65536 covers the intermediary vector, names/children, roots,
        // binding vectors and fixed frames. Snapshot's SECOND payload/storage
        // copy, fresh rollback Arc and record reserve are additionally debited
        // by from_entries_with_progress, on this same borrowed ledger.
        let work = n
            .checked_mul(n)
            .and_then(|v| v.checked_mul(1024))
            .and_then(|v| n.checked_mul(8192).and_then(|w| v.checked_add(w)))
            .and_then(|v| v.checked_add(65_536))
            .ok_or_else(|| budget.refuse_exhaustion())?;
        let bytes = n
            .checked_mul(8192)
            .and_then(|v| v.checked_add(65_536))
            .ok_or_else(|| budget.refuse_exhaustion())?;
        budget.admit(work, bytes)?;
        Ok(())
    }
}

pub(super) fn plan<'a>(
    roots: &'a [Expr],
    bindings: &[FpExprInputBinding<'a>],
    budget: &mut WorkBudget<'_>,
) -> Result<Plan<'a>, FpAdapterError> {
    budget.charge(0)?;
    if roots.is_empty() || roots.len() > MAX_NODES || bindings.len() > MAX_NODES {
        return Err(FpAdapterError::Unsupported("typed root/input population"));
    }
    // Three bounded borrowed-key trees, postorder refs, and recursive frames.
    // Charge BEFORE node/map/reserve/name comparisons; no Expr clone/hash.
    budget.admit(4096, MAX_NODES * 4096 + MAX_DEPTH * 2048)?;
    let links = validate_bindings(bindings, budget)?;
    let mut result = Plan {
        nodes: Vec::new(),
        seen: BTreeMap::new(),
    };
    result
        .nodes
        .try_reserve_exact(MAX_NODES)
        .map_err(|_| budget.refuse_exhaustion())?;
    let mut total = 0usize;
    for root in roots {
        if typed::scalar(root)? != typed::Scalar::Bool {
            return Err(FpAdapterError::Invalid("typed root is not Bool"));
        }
        let count = visit(root, &links, &mut result, 0, budget)?;
        total = total
            .checked_add(count.occurrences)
            .filter(|&n| n <= MAX_OCCURRENCES)
            .ok_or(FpAdapterError::Unsupported("typed repeated occurrences"))?;
    }
    // Retain every supplied input in the source descriptor and typed arena.
    // An unused input is unconstrained; do not invent a native bit assignment
    // for it. Native transfer links every actually reached input unchanged.
    for binding in bindings {
        visit(binding.source, &links, &mut result, 0, budget)?;
    }
    drop(links);
    budget.charge(0)?;
    Ok(result)
}

fn validate_bindings(
    bindings: &[FpExprInputBinding<'_>],
    budget: &mut WorkBudget<'_>,
) -> Result<BTreeMap<usize, ()>, FpAdapterError> {
    let mut links = BTreeMap::new();
    let mut names = BTreeMap::new();
    for binding in bindings {
        // At most ten levels/twelve keys per balanced B-tree node and
        // 256 bytes/name; 65,536 also covers splits and the integer-ID tree.
        budget.charge(65_536)?;
        let ExprValue::Var { name } = binding.source.value() else {
            return Err(FpAdapterError::Invalid("typed input is not free Var"));
        };
        if name.len() > MAX_NAME
            || name != &binding.target.name
            || !typed::scalar(binding.source)?.binding(&binding.target.sort)
        {
            return Err(FpAdapterError::Invalid("typed input name/sort mismatch"));
        }
        if links.insert(identity(binding.source), ()).is_some()
            || names
                .insert(name.as_str(), identity(binding.source))
                .is_some()
        {
            return Err(FpAdapterError::Invalid("duplicate or aliased typed input"));
        }
    }
    drop(names);
    budget.charge(0)?;
    Ok(links)
}

fn visit<'a>(
    expr: &'a Expr,
    links: &BTreeMap<usize, ()>,
    plan: &mut Plan<'a>,
    depth: usize,
    budget: &mut WorkBudget<'_>,
) -> Result<Count, FpAdapterError> {
    budget.charge(8192)?;
    if depth >= MAX_DEPTH {
        return Err(FpAdapterError::Unsupported("typed source depth"));
    }
    let key = identity(expr);
    let kind = typed::scalar(expr)?;
    match plan.seen.get(&key) {
        Some(Visit::Active) => return Err(FpAdapterError::Invalid("typed source cycle")),
        Some(Visit::Done(count, _)) => {
            if count.kind != kind || depth + count.height > MAX_DEPTH {
                return Err(FpAdapterError::Invalid("typed identity sort/depth"));
            }
            return Ok(*count);
        }
        None => {}
    }
    if plan.seen.len() >= MAX_NODES {
        return Err(FpAdapterError::Unsupported("typed unique population"));
    }
    plan.seen.insert(key, Visit::Active);
    let shape = typed::describe(expr)?;
    if matches!(shape.op, typed::Operator::Var) && !links.contains_key(&key) {
        return Err(FpAdapterError::Invalid("omitted typed free input"));
    }
    let mut count = Count {
        occurrences: 1,
        height: 1,
        kind,
    };
    for child in shape.children {
        let next = visit(child, links, plan, depth + 1, budget)?;
        count.occurrences = count
            .occurrences
            .checked_add(next.occurrences)
            .filter(|&n| n <= MAX_OCCURRENCES)
            .ok_or(FpAdapterError::Unsupported("typed raw occurrences"))?;
        count.height = count.height.max(next.height + 1);
    }
    if depth + count.height > MAX_DEPTH {
        return Err(FpAdapterError::Unsupported("typed source height"));
    }
    let index = plan.nodes.len();
    plan.nodes.push(expr);
    plan.seen.insert(key, Visit::Done(count, index));
    Ok(count)
}
