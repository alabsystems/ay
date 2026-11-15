// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact branch-local elimination; no substitution escapes its disjunct.

use super::arena::{Arena, Id, Kind};
use super::control::{Failure, Scope};
use super::{ChcOp, ChcSort};

mod checked_pair;
mod inverse;
mod rewrite;
mod sum_carry;

#[derive(Clone, Copy)]
enum Rule {
    Variable {
        local: usize,
        value: Id,
    },
    UnsignedImage {
        local: usize,
        value: Id,
        operation: ChcOp,
        constant: u128,
        width: u32,
        maximum: u128,
    },
    SumCarry(sum_carry::Binding),
    CheckedPair(checked_pair::Binding),
    Inverse(inverse::Binding),
}

pub(super) fn close(
    mut atoms: Vec<Id>,
    arena: &mut Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<Id, Failure> {
    // Each successful rule removes at least one distinct local everywhere.
    // Its RHS contains only existing variables, never an eliminated local.
    let local_bound = arena.vars.len() - arena.kept;
    for _ in 0..=local_bound {
        atoms = normalize(atoms, arena, scope)?;
        scope.work(atoms.len())?;
        scope.grow::<Id>(atoms.len())?;
        let root = arena.join(ChcOp::And, atoms.clone(), scope)?;
        if arena.closed(root, scope)? {
            return Ok(root);
        }
        let rule = match direct_rule(&atoms, arena, scope)? {
            Some(rule) => rule,
            None => match image_rule(&atoms, arena, scope)? {
                Some(rule) => rule,
                None => match sum_carry::find(&atoms, arena, scope)? {
                    Some(binding) => Rule::SumCarry(binding),
                    None => match checked_pair::find(&atoms, arena, scope)? {
                        Some(binding) => Rule::CheckedPair(binding),
                        // Preserve joint-image priority: substituting one
                        // operand first could obscure an exact paired image.
                        None => Rule::Inverse(
                            inverse::find(&atoms, arena, scope)?.ok_or(Failure::Declined)?,
                        ),
                    },
                },
            },
        };
        // The memo is per substitution, not per resource scope. Arena IDs
        // remain immutable, and one memo preserves all repeated occurrences.
        scope.grow::<Option<Id>>(arena.nodes.len())?;
        let mut memo = vec![None; arena.nodes.len()];
        for atom in &mut atoms {
            let discharge = matches!(rule, Rule::Inverse(binding) if *atom == binding.definition);
            *atom = rewrite::apply(*atom, rule, arena, &mut memo, 0, scope)?;
            if discharge {
                // Modular inversion proves THIS positive defining equality a
                // tautology after substitution, even when another local occurs
                // in its terms. Do not discharge structurally duplicated/reversed equalities
                // or a shared occurrence under Not/ITE: their ordinary rewrite
                // remains in the memo and preserves every other observation.
                *atom = arena.push(Kind::Bool(true), ChcSort::Bool, scope)?;
            }
        }
        if let Rule::UnsignedImage {
            value,
            maximum,
            width,
            ..
        } = rule
        {
            let bound = arena.push(Kind::BitVec(maximum, width), ChcSort::BitVec(width), scope)?;
            scope.grow::<Id>(2)?;
            let range = arena.operation(ChcOp::BvULe, vec![value, bound], scope)?;
            scope.grow::<Id>(1)?;
            atoms.push(range);
        } else if let Rule::SumCarry(binding) = rule {
            let range = sum_carry::image(binding, arena, scope)?;
            scope.grow::<Id>(1)?;
            atoms.push(range);
        } else if let Rule::CheckedPair(binding) = rule {
            let range = checked_pair::image(binding, arena, scope)?;
            scope.grow::<Id>(1)?;
            atoms.push(range);
        }
    }
    Err(Failure::Declined)
}

fn normalize(
    mut pending: Vec<Id>,
    arena: &mut Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<Vec<Id>, Failure> {
    let mut atoms = Vec::new();
    while let Some(id) = pending.pop() {
        scope.work(1)?;
        match &arena.nodes[id].kind {
            Kind::Bool(true) => continue,
            Kind::Bool(false) => {
                scope.grow::<Id>(1)?;
                return Ok(vec![id]);
            }
            Kind::Op(ChcOp::And, args) => {
                scope.grow::<Id>(args.len())?;
                pending.extend(args.iter().copied());
                continue;
            }
            Kind::Op(ChcOp::Eq, args) if arena.same(args[0], args[1], scope)? => continue,
            _ => {}
        }
        scope.grow::<Id>(1)?;
        atoms.push(id);
    }
    Ok(atoms)
}

fn direct_rule(
    atoms: &[Id],
    arena: &mut Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<Option<Rule>, Failure> {
    for atom in atoms {
        scope.work(1)?;
        // A Boolean local asserted by this conjunction has one possible
        // witness. Substitute it everywhere, just like an explicit defining
        // equality. Never use a literal hidden under another connective, or
        // eliminate a retained formal. Full source typing precedes this walk.
        let pin = match &arena.nodes[*atom].kind {
            Kind::Var(local) if arena.nodes[*atom].sort == ChcSort::Bool => Some((*local, true)),
            Kind::Op(ChcOp::Not, args) if args.len() == 1 => match arena.nodes[args[0]].kind {
                Kind::Var(local) if arena.nodes[args[0]].sort == ChcSort::Bool => {
                    Some((local, false))
                }
                _ => None,
            },
            _ => None,
        };
        if let Some((local, value)) = pin.filter(|(local, _)| *local >= arena.kept) {
            let value = arena.push(Kind::Bool(value), ChcSort::Bool, scope)?;
            return Ok(Some(Rule::Variable { local, value }));
        }
        let Kind::Op(ChcOp::Eq, args) = &arena.nodes[*atom].kind else {
            continue;
        };
        for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
            scope.work(1)?;
            let Kind::Var(local) = arena.nodes[lhs].kind else {
                continue;
            };
            if local >= arena.kept && !arena.contains(rhs, local, scope)? {
                return Ok(Some(Rule::Variable { local, value: rhs }));
            }
        }
    }
    Ok(None)
}

fn image_rule(
    atoms: &[Id],
    arena: &Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<Option<Rule>, Failure> {
    for atom in atoms {
        scope.work(1)?;
        let Kind::Op(ChcOp::Eq, args) = &arena.nodes[*atom].kind else {
            continue;
        };
        for (lhs, rhs) in [(args[0], args[1]), (args[1], args[0])] {
            scope.work(1)?;
            let Some(rule) = unsigned_image_binding(lhs, rhs, arena, scope)? else {
                continue;
            };
            if exclusive_image_uses(atoms, rule, arena, scope)? {
                return Ok(Some(rule));
            }
        }
    }
    Ok(None)
}

fn unsigned_image_binding(
    lhs: Id,
    rhs: Id,
    arena: &Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<Option<Rule>, Failure> {
    let Kind::Op(operation @ (ChcOp::BvUDiv | ChcOp::BvLShr), args) = &arena.nodes[rhs].kind else {
        return Ok(None);
    };
    let Kind::Var(local) = arena.nodes[args[0]].kind else {
        return Ok(None);
    };
    let Kind::BitVec(constant, width) = arena.nodes[args[1]].kind else {
        return Ok(None);
    };
    // Strict source admission establishes same-width operands and canonical
    // constants, including the equality's two sides. A kept operand is not a
    // free existential witness. Its observed value may be ANY closed term,
    // including a literal: fixing a source operand before inlining can leave
    // 0 = (local >> k), with no retained variable naming the observation.
    // Closure is metered and forbids all locals, not just this operand.
    if local < arena.kept || !arena.closed(lhs, scope)? {
        return Ok(None);
    }
    let full_range = if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    let maximum = match operation {
        // Division by zero has different SMT-LIB semantics; keep declining it.
        ChcOp::BvUDiv => match full_range.checked_div(constant) {
            Some(maximum) => maximum,
            None => return Ok(None),
        },
        // Logical shift has image [0, MAX >> k] with witness x = result << k.
        // SMT-LIB overshifts have singleton image {0}. Check the full-width
        // unsigned amount BEFORE any host shift: it can be u128::MAX.
        ChcOp::BvLShr if constant >= u128::from(width) => 0,
        ChcOp::BvLShr => full_range >> constant,
        _ => return Ok(None),
    };
    Ok(Some(Rule::UnsignedImage {
        local,
        value: lhs,
        operation: *operation,
        constant,
        width,
        maximum,
    }))
}

/// The local may occur arbitrarily often, but ONLY as the direct first operand
/// of this identical typed division/shift. Raw uses or any other operator or
/// constant keep the rule inapplicable, even for equivalent mixed spellings.
/// No relationship to another occurrence is erased.
fn exclusive_image_uses(
    atoms: &[Id],
    rule: Rule,
    arena: &Arena<'_>,
    scope: &mut Scope<'_>,
) -> Result<bool, Failure> {
    let Rule::UnsignedImage { local, .. } = rule else {
        return Ok(false);
    };
    scope.work(atoms.len())?;
    scope.grow::<Id>(atoms.len())?;
    let mut pending = atoms.to_vec();
    while let Some(id) = pending.pop() {
        scope.work(1)?;
        if matches_image(id, rule, arena) {
            continue;
        }
        match &arena.nodes[id].kind {
            Kind::Var(var) if *var == local => return Ok(false),
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

fn matches_image(id: Id, rule: Rule, arena: &Arena<'_>) -> bool {
    let Rule::UnsignedImage {
        local,
        operation,
        constant,
        width,
        ..
    } = rule
    else {
        return false;
    };
    let Kind::Op(op, args) = &arena.nodes[id].kind else {
        return false;
    };
    *op == operation
        && matches!(arena.nodes[args[0]].kind, Kind::Var(var) if var == local)
        && matches!(arena.nodes[args[1]].kind, Kind::BitVec(value, bits) if value == constant && bits == width)
}
