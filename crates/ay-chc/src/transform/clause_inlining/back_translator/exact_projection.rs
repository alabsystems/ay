// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded exact existential projection of Boolean/bitvector formulas and
//! flat arrays over those scalar sorts. Array constraints remain exact syntax:
//! only occurs-checked defining equalities eliminate an array local.
//!
//! A top-level conjunct closed over the retained formals is kept whole
//! (`closed_atoms`: a closed array guard is retained verbatim, never
//! scalarized); the arena projects the remaining conjuncts.
//!
//! Uses existential distributivity, occurs-checked equality substitution and
//! the images of constant unsigned division and checked unsigned arithmetic. It
//! never enumerates models or drops an alternative. The result remains an
//! untrusted invariant candidate: original-clause validation and strict proof
//! replay still apply.

use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use std::sync::Arc;

mod arena;
mod closed_atoms;
mod control;
mod eliminate;
mod formals;

use arena::{Arena, Id, Kind};
use control::{Failure, Limits, Scope};

pub(super) enum Projection {
    Closed(ChcExpr),
    Declined,
    Stopped,
}

pub(super) fn project(formula: &ChcExpr, keep: &[ChcVar]) -> Projection {
    let memory = crate::bmc::memory::Budget::capture(None, None);
    let interrupt = crate::smt::deadline::lane_interrupt_flag();
    let original_deadline = crate::smt::deadline::effective_thread_deadline();
    let start = ay_core::time::Instant::now();
    let open = || {
        !crate::smt::smt_deadline_expired()
            && original_deadline.is_none_or(|deadline| ay_core::time::Instant::now() < deadline)
            && interrupt
                .as_ref()
                .is_none_or(|flag| !flag.load(std::sync::atomic::Ordering::Relaxed))
            && memory.open()
            && start.elapsed() < super::EXISTENTIAL_QE_LOOP_DEADLINE
    };
    run(formula, keep, &mut Scope::new(Limits::default(), &open))
}

fn run(formula: &ChcExpr, keep: &[ChcVar], scope: &mut Scope<'_>) -> Projection {
    let result = project_with_scope(formula, keep, scope);
    if scope.poll().is_err() {
        return Projection::Stopped;
    }
    match result {
        Ok(formula) => Projection::Closed(formula),
        Err(Failure::Declined) => Projection::Declined,
        Err(Failure::Stopped) => Projection::Stopped,
    }
}

fn project_with_scope(
    formula: &ChcExpr,
    keep: &[ChcVar],
    scope: &mut Scope<'_>,
) -> Result<ChcExpr, Failure> {
    let mut arena = Arena::new(keep, scope)?;
    let parts = closed_atoms::Parts::read(formula, &arena.formals, scope)?;
    scope.grow::<Id>(parts.scalar.len())?;
    let mut scalar = Vec::with_capacity(parts.scalar.len());
    for atom in &parts.scalar {
        let id = arena.read(atom, 0, scope)?;
        // Literal true is the conjunction's neutral element. Distribution
        // drops it, but the closed shortcut and the retained factors below
        // export atoms verbatim: kept, every inlined clause body would stack
        // one more `true` onto each back-translated interpretation.
        if !matches!(arena.nodes[id].kind, Kind::Bool(true)) {
            scalar.push(id);
        }
    }
    let root = arena.join(ChcOp::And, scalar, scope)?;
    // Admission above validates EVERY source atom before this shortcut. When
    // all scalar variables are retained, there is no existential to eliminate:
    // distributing independent closed disjunctions would only duplicate the
    // formula (and can exhaust the branch bound on an already closed fact).
    // Closure, export and reassembly retain the same original resource scope.
    if arena.closed(root, scope)? {
        return parts.assemble(arena.export(root, scope)?, scope);
    }
    // Existential quantification distributes over a conjunction's closed
    // factors, not over arbitrary subterms: preserve each closed OR whole.
    // Keep literal false in the residual so an unsupported local still has
    // the exact empty image, after the complete source was validated above.
    let mut retained = Vec::new();
    let mut residual = Vec::new();
    let singleton = [root];
    let atoms = match &arena.nodes[root].kind {
        Kind::Op(ChcOp::And, args) => args.as_slice(),
        _ => &singleton,
    };
    for &atom in atoms {
        scope.grow::<Id>(1)?;
        if !matches!(arena.nodes[atom].kind, Kind::Bool(false)) && arena.closed(atom, scope)? {
            retained.push(atom);
        } else {
            residual.push(atom);
        }
    }
    let root = arena.join(ChcOp::And, residual, scope)?;
    let branches = distribute(root, &arena, scope)?;
    scope.grow::<Id>(branches.len())?;
    let mut closed = Vec::with_capacity(branches.len());
    for branch in branches {
        scope.poll()?;
        closed.push(eliminate::close(branch, &mut arena, scope)?);
    }
    let root = arena.join(ChcOp::Or, closed, scope)?;
    // A residual whose locals all eliminated has image true: neutral too.
    if !matches!(arena.nodes[root].kind, Kind::Bool(true)) {
        scope.grow::<Id>(1)?;
        retained.push(root);
    }
    let root = arena.join(ChcOp::And, retained, scope)?;
    let scalar = arena.export(root, scope)?;
    parts.assemble(scalar, scope)
}

struct Branch {
    atoms: Vec<Id>,
    pending: Vec<Id>,
}

/// Distribute only positive AND/OR positions. Negations and all other atoms
/// stay intact. Every branch inherits its entire pending common context.
fn distribute(root: Id, arena: &Arena<'_>, scope: &mut Scope<'_>) -> Result<Vec<Vec<Id>>, Failure> {
    scope.branch(1)?;
    scope.grow::<Branch>(1)?;
    scope.grow::<Id>(1)?;
    let mut pending = vec![Branch {
        atoms: Vec::new(),
        pending: vec![root],
    }];
    let mut complete = Vec::new();
    while let Some(mut branch) = pending.pop() {
        let mut impossible = false;
        while let Some(id) = branch.pending.pop() {
            scope.work(1)?;
            match &arena.nodes[id].kind {
                Kind::Op(ChcOp::And, args) => {
                    scope.grow::<Id>(args.len())?;
                    branch.pending.extend(args.iter().rev().copied());
                }
                Kind::Op(ChcOp::Or, args) => {
                    if args.is_empty() {
                        impossible = true;
                        break;
                    }
                    scope.branch(args.len() - 1)?;
                    for other in args.iter().skip(1).rev() {
                        scope.work(branch.atoms.len() + branch.pending.len() + 1)?;
                        scope.grow::<Branch>(1)?;
                        scope.grow::<Id>(branch.atoms.len() + branch.pending.len() + 1)?;
                        let mut next = Branch {
                            atoms: branch.atoms.clone(),
                            pending: branch.pending.clone(),
                        };
                        next.pending.push(*other);
                        pending.push(next);
                    }
                    scope.grow::<Id>(1)?;
                    branch.pending.push(args[0]);
                }
                Kind::Bool(false) => {
                    impossible = true;
                    break;
                }
                Kind::Bool(true) => {}
                _ => {
                    scope.grow::<Id>(1)?;
                    branch.atoms.push(id);
                }
            }
        }
        if !impossible {
            scope.grow::<Vec<Id>>(1)?;
            complete.push(branch.atoms);
        }
    }
    Ok(complete)
}

#[cfg(test)]
mod tests;
