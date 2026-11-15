// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ground congruence closure by union/find and signature rebuilding.
//!
//! This is the standard congruence-closure rule of Nelson and Oppen,
//! "Fast Decision Procedures Based on Congruence Closure", JACM 27(2), 1980.
//! We use a bounded fixed-point rebuild rather than its optimized worklists.
//! Every signature compares complete typed children; hashes are only indexes.
//! The only interpreted rules are in `rules`, after both inputs are typed.

mod classes;
mod rules;
mod signatures;

use super::arena::{Arena, Key};
use super::{push, Error, Owner, Result};
use crate::ChcOp;
use classes::Classes;
use std::collections::HashSet;

pub(super) fn entails(
    arena: &mut Arena,
    head: usize,
    assumptions: &HashSet<usize>,
    owner: &mut Owner,
) -> Result<bool> {
    let yes = arena.boolean(true, owner)?;
    let no = arena.boolean(false, owner)?;
    let mut classes = Classes::new(arena, owner)?;
    // Iterate in arena order: the randomized assumption set never determines
    // work, union representatives, or how much original credit is consumed.
    for id in 0..arena.len() {
        owner.admit(1, 0)?;
        if !assumptions.contains(&id) {
            continue;
        }
        classes.union(id, yes, arena, owner)?;
        match &arena.node(id).key {
            Key::Op(ChcOp::Eq, args) => {
                classes.union(args[0], args[1], arena, owner)?;
            }
            Key::Op(ChcOp::Not, args) => {
                classes.union(args[0], no, arena, owner)?;
            }
            _ => {}
        }
    }
    loop {
        // Equalities only accumulate. Once the complete, already-typed head
        // follows from them, another saturation pass cannot invalidate that
        // proof. Check both the initial facts and each completed pass under
        // the same owner; an unproved head must still reach a fixed point.
        if classes.same(yes, no, owner)? {
            return Ok(true);
        }
        if conclusion(arena, &mut classes, head, yes, owner)? {
            return Ok(true);
        }
        let mut changed = false;
        // New constants have no applications, so visit the current nodes once.
        for id in 0..arena.len() {
            owner.admit(1, 0)?;
            changed |= rules::apply(id, yes, no, arena, &mut classes, owner)?;
        }
        changed |= signatures::rebuild(arena, &mut classes, owner)?;
        if !changed {
            return Ok(false);
        }
    }
}

fn conclusion(
    arena: &Arena,
    classes: &mut Classes,
    head: usize,
    yes: usize,
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
        if classes.same(id, yes, owner)? {
            continue;
        }
        match &arena.node(id).key {
            Key::Op(ChcOp::Eq, args) if classes.same(args[0], args[1], owner)? => {}
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
