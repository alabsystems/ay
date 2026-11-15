// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Single-variable cancellation in the additive group of integers modulo 2^w.
//!
//! For any same-width terms R,T that do not contain x, the equalities
//! R=x+T, R=T+x, R=x-T, R=T-x uniquely determine x as R-T, R-T, R+T, T-R.
//! Thus exists x. (E(x) and F(x)) equals F(inverse(R,T)); no range premise or
//! division is involved. Other locals in R/T remain existentially quantified.

use super::{Arena, ChcOp, ChcSort, Failure, Id, Kind, Scope};

#[derive(Clone, Copy)]
pub(super) struct Binding {
    pub(super) definition: Id,
    pub(super) local: usize,
    pub(super) value: Id,
}

pub(super) fn find(
    atoms: &[Id],
    arena: &mut Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<Option<Binding>, Failure> {
    for definition in atoms {
        scope.work(1)?;
        let Kind::Op(ChcOp::Eq, equality) = &arena.nodes[*definition].kind else {
            continue;
        };
        let sides = [equality[0], equality[1]];
        for (target, expression) in [(sides[0], sides[1]), (sides[1], sides[0])] {
            scope.work(1)?;
            let Some((local, operation, arguments)) = candidate(target, expression, arena, scope)?
            else {
                continue;
            };
            // Insert the typed RHS BEFORE close() sizes its rewrite memo. It
            // contains only existing variable identities, never the removed x.
            scope.grow::<Id>(2)?;
            let value = arena.operation(operation, arguments.to_vec(), scope)?;
            return Ok(Some(Binding {
                definition: *definition,
                local,
                value,
            }));
        }
    }
    Ok(None)
}

fn candidate(
    target: Id,
    expression: Id,
    arena: &Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<Option<(usize, ChcOp, [Id; 2])>, Failure> {
    let ChcSort::BitVec(width @ 1..=128) = arena.nodes[expression].sort else {
        return Ok(None);
    };
    let Kind::Op(operation @ (ChcOp::BvAdd | ChcOp::BvSub), args) = &arena.nodes[expression].kind
    else {
        return Ok(None);
    };
    // Full-source admission already checks binary arity and matching sorts;
    // keep the rule's same-width preconditions explicit as well.
    if args.len() != 2 || arena.nodes[target].sort != ChcSort::BitVec(width) {
        return Ok(None);
    }
    for position in 0..2 {
        scope.work(1)?;
        let Kind::Var(local) = arena.nodes[args[position]].kind else {
            continue;
        };
        let other = args[1 - position];
        if local < arena.kept
            || arena.vars[local].sort != ChcSort::BitVec(width)
            || arena.nodes[other].sort != ChcSort::BitVec(width)
            || arena.contains(target, local, scope)?
            || arena.contains(other, local, scope)?
        {
            continue;
        }
        let (operation, arguments) = match (*operation, position) {
            (ChcOp::BvAdd, _) => (ChcOp::BvSub, [target, other]),
            (ChcOp::BvSub, 0) => (ChcOp::BvAdd, [target, other]),
            (ChcOp::BvSub, _) => (ChcOp::BvSub, [other, target]),
            _ => return Ok(None),
        };
        return Ok(Some((local, operation, arguments)));
    }
    Ok(None)
}
