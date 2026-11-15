// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact joint image of modular addition and its unsigned carry bit.
//!
//! For independent x,y:BVw, S=x+y and C=ult(S,x), the image is
//! `!C || S != MAX`. No-carry witness: x=S,y=0. Carry witness when S<MAX:
//! x=MAX,y=S+1. The sum cannot be MAX with carry because x+y <= 2*MAX.
//! Replacing both observations together preserves every surrounding relation.

use super::{Arena, ChcOp, ChcSort, Failure, Id, Kind, Scope};

#[derive(Clone, Copy)]
pub(super) struct Binding {
    left: usize,
    right: usize,
    sum: Id,
    carry: Id,
    width: u32,
}

pub(super) fn find(
    atoms: &[Id],
    arena: &Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<Option<Binding>, Failure> {
    for atom in atoms {
        scope.work(1)?;
        let Kind::Op(ChcOp::Eq, args) = &arena.nodes[*atom].kind else {
            continue;
        };
        for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
            scope.work(1)?;
            let Some(binding) = sum_binding(lhs, rhs, arena) else {
                continue;
            };
            if let Some(binding) = find_carry(atoms, binding, arena, scope)? {
                return Ok(Some(binding));
            }
        }
    }
    Ok(None)
}

fn sum_binding(lhs: Id, rhs: Id, arena: &Arena<'_>) -> Option<Binding> {
    let Kind::Var(kept) = arena.nodes[lhs].kind else {
        return None;
    };
    let Kind::Op(ChcOp::BvAdd, args) = &arena.nodes[rhs].kind else {
        return None;
    };
    let (Kind::Var(left), Kind::Var(right)) =
        (&arena.nodes[args[0]].kind, &arena.nodes[args[1]].kind)
    else {
        return None;
    };
    let ChcSort::BitVec(width) = arena.nodes[lhs].sort else {
        return None;
    };
    // Complete source admission already checked binary arity and equal widths.
    // Distinctness and unkept status are necessary for the two witnesses above.
    if kept >= arena.kept || left == right || *left < arena.kept || *right < arena.kept {
        return None;
    }
    Some(Binding {
        left: *left,
        right: *right,
        sum: lhs,
        // Filled only after locating a retained Boolean carry binding.
        carry: lhs,
        width,
    })
}

fn find_carry(
    atoms: &[Id],
    binding: Binding,
    arena: &Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<Option<Binding>, Failure> {
    for atom in atoms {
        scope.work(1)?;
        let Kind::Op(ChcOp::Eq, args) = &arena.nodes[*atom].kind else {
            continue;
        };
        for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
            scope.work(1)?;
            let Kind::Var(kept) = arena.nodes[lhs].kind else {
                continue;
            };
            if kept < arena.kept
                && arena.nodes[lhs].sort == ChcSort::Bool
                && matches_carry(rhs, binding, arena)
            {
                let binding = Binding {
                    carry: lhs,
                    ..binding
                };
                if exclusive_uses(atoms, binding, arena, scope)? {
                    return Ok(Some(binding));
                }
            }
        }
    }
    Ok(None)
}

fn matches_sum(id: Id, binding: Binding, arena: &Arena<'_>) -> bool {
    let Kind::Op(ChcOp::BvAdd, args) = &arena.nodes[id].kind else {
        return false;
    };
    matches!(arena.nodes[args[0]].kind, Kind::Var(var) if var == binding.left)
        && matches!(arena.nodes[args[1]].kind, Kind::Var(var) if var == binding.right)
}

fn matches_carry(id: Id, binding: Binding, arena: &Arena<'_>) -> bool {
    let Kind::Op(ChcOp::BvULt, args) = &arena.nodes[id].kind else {
        return false;
    };
    matches_sum(args[0], binding, arena)
        && matches!(arena.nodes[args[1]].kind,
            Kind::Var(var) if var == binding.left || var == binding.right)
}

pub(super) fn replacement(id: Id, binding: Binding, arena: &Arena<'_>) -> Option<Id> {
    // Match the whole carry before descending into its sum or raw operand.
    if matches_carry(id, binding, arena) {
        Some(binding.carry)
    } else if matches_sum(id, binding, arena) {
        Some(binding.sum)
    } else {
        None
    }
}

fn exclusive_uses(
    atoms: &[Id],
    binding: Binding,
    arena: &Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<bool, Failure> {
    scope.work(atoms.len())?;
    scope.grow::<Id>(atoms.len())?;
    let mut pending = atoms.to_vec();
    while let Some(id) = pending.pop() {
        scope.work(1)?;
        if replacement(id, binding, arena).is_some() {
            continue;
        }
        match &arena.nodes[id].kind {
            Kind::Var(var) if *var == binding.left || *var == binding.right => return Ok(false),
            _ => {
                let children = arena.children(id);
                if !children.is_empty() {
                    scope.grow::<Id>(children.len())?;
                    pending.extend(children.iter().copied());
                }
            }
        }
    }
    Ok(true)
}

pub(super) fn image(
    binding: Binding,
    arena: &mut Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<Id, Failure> {
    scope.grow::<Id>(1)?;
    let no_carry = arena.operation(ChcOp::Not, vec![binding.carry], scope)?;
    let maximum = if binding.width == 128 {
        u128::MAX
    } else {
        (1u128 << binding.width) - 1
    };
    let maximum = arena.push(
        Kind::BitVec(maximum, binding.width),
        ChcSort::BitVec(binding.width),
        scope,
    )?;
    scope.grow::<Id>(2)?;
    let below_maximum = arena.operation(ChcOp::Ne, vec![binding.sum, maximum], scope)?;
    scope.grow::<Id>(2)?;
    arena.operation(ChcOp::Or, vec![no_carry, below_maximum], scope)
}
