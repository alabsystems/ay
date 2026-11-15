// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded exact instantiation of retained source-premise matrices.

use std::cell::Cell;
use std::sync::Arc;
use std::time::Duration;

use crate::quantified::UniversalPremise;
use crate::{CancellationToken, ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::time::Instant;

#[cfg(test)]
#[path = "source_premises/tests/debit.rs"]
mod debit_tests;
mod grouped;
#[cfg(test)]
mod tests;

const MAX_INSTANCE_NODES: usize = 8_000_000;
const MAX_DEPTH: usize = 128;
pub(super) const MAX_REPLAY_BYTES: usize = 8 * 1024 * 1024;
const MAX_COPY_BYTES: usize = 64 * 1024 * 1024;

/// Wall share of one original clause in a quantified-source discharge.
///
/// The certificate is all-or-nothing over the original clauses, discharged in
/// order, so each clause takes a fair share of the caller's REMAINING envelope,
/// recomputed after every success so cheap clauses donate their surplus. There
/// is deliberately no fixed ceiling. The flat ghost lane's five-second
/// `per_rule_budget` cap was sized for obligations it settles in milliseconds;
/// here it expired nested datatype/array obligations that take seconds of
/// solver work as soon as CPU contention stretched that work past five wall
/// seconds, with most of the caller's envelope unspent, so one certificate
/// flipped between Safe and Unknown with the machine's load. The caller's
/// deadline stays the hard bound on the whole discharge.
pub(super) fn clause_budget(remaining: Duration, clauses_remaining: usize) -> Duration {
    let divisor = u32::try_from(clauses_remaining.max(1)).unwrap_or(u32::MAX);
    remaining / divisor
}

pub(crate) struct SourceControl<'a> {
    pub(super) deadline: Instant,
    pub(super) cancellation: &'a CancellationToken,
    pub(super) replay_cancellation: crate::smt::executor_adapter::ReplayCancellation,
    stopped: Cell<bool>,
    remaining: Cell<usize>,
    bytes_left: Cell<usize>,
}

impl<'a> SourceControl<'a> {
    pub(crate) fn new(deadline: Instant, cancellation: &'a CancellationToken) -> Self {
        Self {
            deadline,
            cancellation,
            replay_cancellation: crate::smt::executor_adapter::ReplayCancellation::new(
                cancellation,
            ),
            stopped: Cell::new(false),
            remaining: Cell::new(MAX_INSTANCE_NODES),
            bytes_left: Cell::new(MAX_COPY_BYTES),
        }
    }

    pub(crate) fn poll(&self) -> Option<()> {
        if self.stopped.get()
            || self.replay_cancellation.is_cancelled()
            || Instant::now() >= self.deadline
            || ay_core::TermStore::global_memory_exceeded()
        {
            self.stopped.set(true);
            return None;
        }
        Some(())
    }

    pub(crate) fn charge(&self, nodes: usize) -> Option<()> {
        self.poll()?;
        let Some(bytes) = nodes.checked_mul(64) else {
            self.stopped.set(true);
            return None;
        };
        self.debit(nodes, bytes)
    }

    pub(crate) fn bytes(&self, count: usize) -> Option<()> {
        self.debit(0, count)
    }

    /// Permanently refuse this attempt without mutating the caller's token.
    pub(crate) fn stop(&self) {
        self.stopped.set(true);
    }

    /// Charge independently metered work and copying to this same attempt.
    /// Query conservation counts compared bytes as work without allocating a
    /// node per comparison; it must not inherit `charge`'s 64-byte node cost.
    /// Both counters are checked before either changes. Refusal is terminal;
    /// this operation neither reserves a second allowance nor refunds work.
    pub(crate) fn debit(&self, work: usize, bytes: usize) -> Option<()> {
        self.poll()?;
        let (Some(work), Some(bytes)) = (
            self.remaining.get().checked_sub(work),
            self.bytes_left.get().checked_sub(bytes),
        ) else {
            self.stopped.set(true);
            return None;
        };
        self.remaining.set(work);
        self.bytes_left.set(bytes);
        Some(())
    }
}

/// Conservative serialization/copy preflight, counting occurrences rather than
/// unique DAG nodes. This runs before legacy recursive formatters or clones.
/// The per-node allowance covers operators, delimiters and numeric payloads;
/// names are charged separately, including quoting expansion and sort syntax.
pub(super) fn preflight(
    expr: &ChcExpr,
    control: &SourceControl<'_>,
    output_bytes: &mut usize,
) -> Option<()> {
    let mut stack = vec![(expr, 0usize)];
    while let Some((node, depth)) = stack.pop() {
        control.charge(1)?;
        if depth > MAX_DEPTH {
            return None;
        }
        let mut bytes = 256usize;
        match node {
            ChcExpr::Var(var) => {
                bytes = bytes
                    .checked_add(sort_bytes(&var.sort)?)?
                    .checked_add(var.name.len().checked_mul(4)?)?;
            }
            ChcExpr::FuncApp(name, sort, args) => {
                // Resource admission only. The immutable source registry and
                // projected model validator authenticate function signatures.
                bytes = bytes
                    .checked_add(sort_bytes(sort)?)?
                    .checked_add(name.len().checked_mul(4)?)?;
                control.charge(args.len())?;
                stack.try_reserve(args.len()).ok()?;
                stack.extend(args.iter().rev().map(|arg| (arg.as_ref(), depth + 1)));
            }
            ChcExpr::Op(_, args) => {
                control.charge(args.len())?;
                stack.try_reserve(args.len()).ok()?;
                stack.extend(args.iter().rev().map(|arg| (arg.as_ref(), depth + 1)));
            }
            ChcExpr::ConstArray(sort, value) => {
                if !copyable_const_key(sort) {
                    return None;
                }
                bytes = bytes.checked_add(sort_bytes(sort)?)?;
                stack.push((value, depth + 1));
            }
            ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::BitVec(_, _) => {}
            _ => return None,
        }
        *output_bytes = output_bytes.checked_add(bytes)?;
        if *output_bytes > MAX_REPLAY_BYTES {
            return None;
        }
        // The inherited formatter materializes intermediate subexpressions.
        control.bytes(bytes.checked_mul(depth.checked_add(1)?)?)?;
    }
    control.poll()
}

pub(super) fn preflight_clause(
    clause: &crate::HornClause,
    control: &SourceControl<'_>,
) -> Option<()> {
    let mut bytes = 0;
    for (_, args) in &clause.body.predicates {
        for arg in args {
            preflight(arg, control, &mut bytes)?;
        }
    }
    if let crate::ClauseHead::Predicate(_, args) = &clause.head {
        for arg in args {
            preflight(arg, control, &mut bytes)?;
        }
    }
    if let Some(expr) = &clause.body.constraint {
        preflight(expr, control, &mut bytes)?;
    }
    control.poll()
}

/// Include binder names too: generated ghost/skolem names cannot shadow them.
pub(super) fn reserve_names(
    premises: &[UniversalPremise],
    used: &mut FxHashSet<String>,
    control: &SourceControl<'_>,
) -> Option<()> {
    for premise in premises {
        for binder in premise.binders() {
            control.bytes(binder.name.len())?;
            used.insert(binder.name.clone());
        }
        preflight(premise.matrix(), control, &mut 0)?;
        let vars = super::certify::certificate_formula_vars(premise.matrix())?;
        for var in vars {
            control.poll()?;
            used.insert(var.name);
        }
    }
    control.poll()
}

/// Free source-matrix variables belong to the original clause scope, while
/// each premise binder remains lexical to that premise alone.
pub(super) fn clause_variables(
    clause: &crate::HornClause,
    premises: &[UniversalPremise],
    control: &SourceControl<'_>,
) -> Option<Vec<ChcVar>> {
    preflight_clause(clause, control)?;
    let mut vars = super::certify::exact_clause_vars(clause)?;
    let mut seen: FxHashSet<ChcVar> = vars.iter().cloned().collect();
    for premise in premises {
        control.poll()?;
        preflight(premise.matrix(), control, &mut 0)?;
        for var in super::certify::certificate_formula_vars(premise.matrix())? {
            control.poll()?;
            if !premise.binders().any(|binder| binder == &var) && seen.insert(var.clone()) {
                vars.push(var);
            }
        }
    }
    vars.sort_by(|a, b| a.name.cmp(&b.name));
    control.poll()?;
    Some(vars)
}

/// Every selected term is merely an instance; no support-range approximation
/// or invented array equality is substituted for the original matrix.
pub(super) fn instances(
    premises: &[UniversalPremise],
    terms: &[ChcExpr],
    control: &SourceControl<'_>,
) -> Option<Vec<ChcExpr>> {
    let mut out = Vec::new();
    for premise in premises {
        control.poll()?;
        if premise.binder_count() > 1 {
            grouped::instances(premise, terms, control, &mut out)?;
            continue;
        }
        for term in terms {
            control.poll()?;
            if term.sort() != premise.binder().sort {
                continue;
            }
            out.push(substitute(
                premise.matrix(),
                &[(premise.binder(), term)],
                0,
                control,
            )?);
        }
    }
    control.poll()?;
    Some(out)
}

fn substitute(
    expr: &ChcExpr,
    bindings: &[(&ChcVar, &ChcExpr)],
    depth: usize,
    control: &SourceControl<'_>,
) -> Option<ChcExpr> {
    control.charge(1)?;
    if depth > MAX_DEPTH {
        return None;
    }
    let result = match expr {
        ChcExpr::Var(var) if bindings.iter().any(|(binder, _)| *binder == var) => {
            let (_, term) = bindings.iter().find(|(binder, _)| *binder == var)?;
            copy_term(term, depth, control)?
        }
        ChcExpr::Op(op, args) => {
            control.charge(args.len())?;
            let mut out = Vec::new();
            out.try_reserve_exact(args.len()).ok()?;
            for arg in args {
                out.push(Arc::new(substitute(arg, bindings, depth + 1, control)?));
            }
            ChcExpr::Op(*op, out)
        }
        ChcExpr::ConstArray(sort, value) => {
            control.bytes(sort_bytes(sort)?)?;
            ChcExpr::ConstArray(
                sort.clone(),
                Arc::new(substitute(value, bindings, depth + 1, control)?),
            )
        }
        ChcExpr::FuncApp(name, sort, args) => {
            control.bytes(name.len().checked_add(sort_bytes(sort)?)?)?;
            control.charge(args.len())?;
            let mut out = Vec::new();
            out.try_reserve_exact(args.len()).ok()?;
            for arg in args {
                out.push(Arc::new(substitute(arg, bindings, depth + 1, control)?));
            }
            ChcExpr::FuncApp(name.clone(), sort.clone(), out)
        }
        ChcExpr::Var(var) => {
            control.bytes(var.name.len().checked_add(sort_bytes(&var.sort)?)?)?;
            expr.clone()
        }
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::BitVec(_, _) => expr.clone(),
        _ => return None,
    };
    control.poll()?;
    Some(result)
}

/// Atomic alpha-renaming/instantiation: replacements are copied verbatim and
/// never visited by the substitution map, including names of other binders.
pub(super) fn simultaneous(
    matrix: &ChcExpr,
    bindings: &[(&ChcVar, &ChcExpr)],
    control: &SourceControl<'_>,
) -> Option<ChcExpr> {
    if bindings.len() > crate::quantified::MAX_PREMISE_BINDERS {
        control.stopped.set(true);
        return None;
    }
    for (index, (binder, term)) in bindings.iter().enumerate() {
        control.charge(1)?;
        preflight(term, control, &mut 0)?;
        if !matches!(binder.sort, ChcSort::BitVec(1..=64))
            || term.sort() != binder.sort
            || bindings[..index]
                .iter()
                .any(|(other, _)| other.name == binder.name)
        {
            return None;
        }
    }
    substitute(matrix, bindings, 0, control)
}

/// Complete ordered binder group; the matrix is preflighted by the caller.
pub(super) fn binder_list(
    premise: &UniversalPremise,
    control: Option<&SourceControl<'_>>,
) -> Option<String> {
    let mut out = String::new();
    for (index, binder) in premise.binders().enumerate() {
        if let Some(control) = control {
            control.bytes(binder.name.len().checked_mul(4)?.checked_add(256)?)?;
        }
        if index != 0 {
            out.push(' ');
        }
        out.push_str(&format!(
            "({} {})",
            ay_core::quote_symbol(&binder.name),
            crate::smt::executor_adapter::sort_to_smtlib(&binder.sort)
        ));
    }
    Some(out)
}

fn copy_term(expr: &ChcExpr, depth: usize, control: &SourceControl<'_>) -> Option<ChcExpr> {
    control.charge(1)?;
    if depth > MAX_DEPTH {
        return None;
    }
    match expr {
        ChcExpr::Var(var) => {
            control.bytes(var.name.len().checked_add(sort_bytes(&var.sort)?)?)?;
            Some(expr.clone())
        }
        ChcExpr::Int(_) | ChcExpr::BitVec(_, _) | ChcExpr::Bool(_) => Some(expr.clone()),
        ChcExpr::Op(op, args) => {
            control.charge(args.len())?;
            let mut out = Vec::new();
            out.try_reserve_exact(args.len()).ok()?;
            for arg in args {
                out.push(Arc::new(copy_term(arg, depth + 1, control)?));
            }
            Some(ChcExpr::Op(*op, out))
        }
        ChcExpr::FuncApp(name, sort, args) => {
            control.bytes(name.len().checked_add(sort_bytes(sort)?)?)?;
            control.charge(args.len())?;
            let mut out = Vec::new();
            out.try_reserve_exact(args.len()).ok()?;
            for arg in args {
                out.push(Arc::new(copy_term(arg, depth + 1, control)?));
            }
            Some(ChcExpr::FuncApp(name.clone(), sort.clone(), out))
        }
        ChcExpr::ConstArray(sort, value) => {
            if !copyable_const_key(sort) {
                return None;
            }
            control.bytes(sort_bytes(sort)?)?;
            Some(ChcExpr::ConstArray(
                sort.clone(),
                Arc::new(copy_term(value, depth + 1, control)?),
            ))
        }
        _ => None,
    }
}

/// Wide source-only copies do not widen `supported_sort`, the legacy ghost
/// certificate's separate admission boundary. Source typing is checked elsewhere.
fn copyable_const_key(sort: &ChcSort) -> bool {
    supported_sort(sort) || matches!(sort, ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH))
}

/// Structural resource cost, never declaration or function-signature authority.
fn sort_bytes(sort: &ChcSort) -> Option<usize> {
    if supported_sort(sort) {
        // Existing per-node allowances already cover scalar/array metadata.
        Some(0)
    } else {
        // Complete record metadata remains charged when nested under arrays.
        // This does not widen the legacy ghost-model admission gate below.
        crate::quantified::records::sort_bytes(sort)
    }
}

pub(super) fn supported_sort(sort: &ChcSort) -> bool {
    match sort {
        ChcSort::Bool | ChcSort::Int | ChcSort::BitVec(1..=128) => true,
        ChcSort::Array(key, value) => {
            matches!(key.as_ref(), ChcSort::Int | ChcSort::BitVec(1..=64))
                && matches!(
                    value.as_ref(),
                    ChcSort::Bool | ChcSort::Int | ChcSort::BitVec(1..=128)
                )
        }
        _ => false,
    }
}
