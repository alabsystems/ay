// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed conjunction elimination and bounded ground congruence, without SMT.
//!
//! Both complete inputs are typed before any proof decision. Canonical node
//! IDs denote full, structurally equal terms (including sorts), never hashes.
//! Unsupported syntax is a decline, not a proof; resource refusal is terminal
//! in the caller's original owner. This is not an invariant-synthesis rule.

mod arena;
mod congruence;
mod types;

use crate::ground_derivation::compact::{Error, Owner, Result};
use crate::{ChcExpr, ChcOp};
use arena::{Arena, Key};
use std::collections::HashSet;

/// `Ok(true)` proves the implication. `Ok(false)` means only "not established".
/// The caller must not replace a stopped owner and retry with fresh credit.
pub(crate) fn entails(body: &ChcExpr, head: &ChcExpr, owner: &mut Owner) -> Result<bool> {
    let scope = owner.enter();
    let result = check(body, head, owner);
    drop(scope);
    // Local arenas and traversal storage are gone before final admission.
    match result {
        Err(error @ (Error::Stopped | Error::Resource)) => owner.refuse(error),
        Err(Error::Unsupported | Error::InvalidSource) => {
            owner.poll()?;
            Ok(false)
        }
        other => {
            owner.poll()?;
            other
        }
    }
}

fn check(body: &ChcExpr, head: &ChcExpr, owner: &mut Owner) -> Result<bool> {
    owner.poll()?;
    let mut arena = Arena::new();
    let body = arena.read(body, 0, owner)?;
    let head = arena.read(head, 0, owner)?;
    if !arena.is_bool(body) || !arena.is_bool(head) {
        return Err(Error::InvalidSource);
    }
    let mut assumptions = HashSet::new();
    let mut pending = Vec::new();
    push(&mut pending, body, owner)?;
    while let Some(id) = pending.pop() {
        owner.admit(1, 0)?;
        if !assumptions.contains(&id) {
            owner.admit(1, 64)?;
            assumptions.try_reserve(1).map_err(|_| Error::Resource)?;
            assumptions.insert(id);
            if let Key::Op(ChcOp::And, args) = &arena.node(id).key {
                for &arg in args {
                    push(&mut pending, arg, owner)?;
                }
            }
        }
    }
    if exact(&arena, head, &assumptions, owner)? {
        return Ok(true);
    }
    congruence::entails(&mut arena, head, &assumptions, owner)
}

fn exact(
    arena: &Arena,
    head: usize,
    assumptions: &HashSet<usize>,
    owner: &mut Owner,
) -> Result<bool> {
    let mut pending = Vec::new();
    let mut visited = HashSet::new();
    push(&mut pending, head, owner)?;
    while let Some(id) = pending.pop() {
        owner.admit(1, 0)?;
        if visited.contains(&id) {
            continue;
        }
        owner.admit(1, 64)?;
        visited.try_reserve(1).map_err(|_| Error::Resource)?;
        visited.insert(id);
        if assumptions.contains(&id) {
            continue;
        }
        match &arena.node(id).key {
            Key::Bool(true) => {}
            Key::Op(ChcOp::Eq, args) if args.len() == 2 && args[0] == args[1] => {}
            Key::Op(ChcOp::And, args) => {
                for &arg in args {
                    push(&mut pending, arg, owner)?;
                }
            }
            _ => return Ok(false),
        }
    }
    Ok(true)
}

fn push(pending: &mut Vec<usize>, id: usize, owner: &mut Owner) -> Result<()> {
    owner.admit(1, 4 * std::mem::size_of::<usize>())?;
    pending.try_reserve(1).map_err(|_| Error::Resource)?;
    pending.push(id);
    Ok(())
}

#[cfg(test)]
mod tests;
