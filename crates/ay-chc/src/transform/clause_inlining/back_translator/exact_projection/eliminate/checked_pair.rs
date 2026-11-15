// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact joint images of two free unsigned operands, with M=2^w.
//!
//! Difference D=x-y, borrow B=x<y: `!B || D!=0`. Witnesses are (D,0)
//! without borrow, or (0,M-D) with borrow, necessarily D>0.
//!
//! Product L=x*y mod M, no-overflow E=(x*y<M): image E for w=1,
//! `E || L!=3` for w=2, and true for w>=3. No-overflow witness: (L,1).
//! Overflow witnesses: L=0 uses (M/2,2), 1<=L<=M-2 uses (M-1,M-L),
//! and L=M-1 uses (M/2-1,M/2+1). The last witness needs w>=3; at w=2
//! the overflow products are exactly 4,6,9, and at w=1 none overflow.
//! Distinct operand identities are required, not distinct operand values.

use super::{Arena, ChcOp, ChcSort, Failure, Id, Kind, Scope};

mod syntax;
use syntax::{Arithmetic, Candidate, Polarity};

#[derive(Clone, Copy)]
pub(super) struct Binding {
    candidate: Candidate,
    // Always the canonical observation: borrow, or product NO-overflow.
    observation: Id,
}

pub(super) fn find(
    atoms: &[Id],
    arena: &mut Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<Option<Binding>, Failure> {
    for atom in atoms {
        scope.work(1)?;
        let Kind::Op(ChcOp::Eq, args) = &arena.nodes[*atom].kind else {
            continue;
        };
        for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
            scope.work(1)?;
            let Some(candidate) = syntax::candidate(lhs, rhs, arena) else {
                continue;
            };
            if let Some(binding) = find_observation(atoms, candidate, arena, scope)? {
                return Ok(Some(binding));
            }
        }
    }
    Ok(None)
}

fn find_observation(
    atoms: &[Id],
    candidate: Candidate,
    arena: &mut Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<Option<Binding>, Failure> {
    for atom in atoms {
        scope.work(1)?;
        let Kind::Op(ChcOp::Eq, args) = &arena.nodes[*atom].kind else {
            continue;
        };
        for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
            scope.work(1)?;
            let Some(polarity) = syntax::flag_binding(lhs, rhs, candidate, arena) else {
                continue;
            };
            if !exclusive_uses(atoms, candidate, arena, scope)? {
                continue;
            }
            let observation = match polarity {
                Polarity::Positive => lhs,
                Polarity::Negative => {
                    scope.grow::<Id>(1)?;
                    arena.operation(ChcOp::Not, vec![lhs], scope)?
                }
            };
            return Ok(Some(Binding {
                candidate,
                observation,
            }));
        }
    }
    Ok(None)
}

fn exclusive_uses(
    atoms: &[Id],
    candidate: Candidate,
    arena: &Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<bool, Failure> {
    scope.work(atoms.len())?;
    scope.grow::<Id>(atoms.len())?;
    let mut pending = atoms.to_vec();
    while let Some(id) = pending.pop() {
        scope.work(1)?;
        if syntax::low(id, candidate, arena) || syntax::observation(id, candidate, arena) {
            continue;
        }
        match &arena.nodes[id].kind {
            Kind::Var(var) if *var == candidate.left || *var == candidate.right => {
                return Ok(false);
            }
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

pub(super) fn replacement(id: Id, binding: Binding, arena: &Arena<'_>) -> Option<Id> {
    // Recognize the whole comparison before descending into its raw operands
    // or widened product. Surrounding negations and ITEs retain their meaning.
    if syntax::observation(id, binding.candidate, arena) {
        Some(binding.observation)
    } else if syntax::low(id, binding.candidate, arena) {
        Some(binding.candidate.result)
    } else {
        None
    }
}

pub(super) fn image(
    binding: Binding,
    arena: &mut Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<Id, Failure> {
    scope.work(1)?;
    let candidate = binding.candidate;
    let (allowed, excluded) = match candidate.arithmetic {
        Arithmetic::Difference => {
            scope.grow::<Id>(1)?;
            let no_borrow = arena.operation(ChcOp::Not, vec![binding.observation], scope)?;
            (no_borrow, 0)
        }
        Arithmetic::Product if candidate.width == 1 => return Ok(binding.observation),
        Arithmetic::Product if candidate.width == 2 => (binding.observation, 3),
        Arithmetic::Product => return arena.push(Kind::Bool(true), ChcSort::Bool, scope),
    };
    let excluded = arena.push(
        Kind::BitVec(excluded, candidate.width),
        ChcSort::BitVec(candidate.width),
        scope,
    )?;
    scope.grow::<Id>(2)?;
    let other_result = arena.operation(ChcOp::Ne, vec![candidate.result, excluded], scope)?;
    scope.grow::<Id>(2)?;
    arena.operation(ChcOp::Or, vec![allowed, other_result], scope)
}
