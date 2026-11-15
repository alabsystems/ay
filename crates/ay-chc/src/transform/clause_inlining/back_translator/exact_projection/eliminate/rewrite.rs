// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{
    checked_pair, matches_image, sum_carry, Arena, ChcOp, ChcSort, Failure, Id, Kind, Rule, Scope,
};

pub(super) fn apply(
    id: Id,
    rule: Rule,
    arena: &mut Arena<'_>,
    memo: &mut [Option<Id>],
    depth: usize,
    scope: &mut Scope<'_>,
) -> Result<Id, Failure> {
    scope.depth(depth)?;
    if let Some(cached) = memo[id] {
        return Ok(cached);
    }
    let replacement = match rule {
        Rule::Variable { local, value } => {
            matches!(arena.nodes[id].kind, Kind::Var(var) if var == local).then_some(value)
        }
        Rule::Inverse(binding) => {
            matches!(arena.nodes[id].kind, Kind::Var(var) if var == binding.local)
                .then_some(binding.value)
        }
        Rule::UnsignedImage { value, .. } => matches_image(id, rule, arena).then_some(value),
        Rule::SumCarry(binding) => sum_carry::replacement(id, binding, arena),
        Rule::CheckedPair(binding) => checked_pair::replacement(id, binding, arena),
    };
    let result = if let Some(value) = replacement {
        value
    } else if let Kind::Op(op, args) = &arena.nodes[id].kind {
        scope.work(args.len())?;
        scope.grow::<Id>(args.len())?;
        let (op, mut children) = (*op, args.clone());
        for child in &mut children {
            *child = apply(*child, rule, arena, memo, depth + 1, scope)?;
        }
        if op == ChcOp::Eq && arena.same(children[0], children[1], scope)? {
            arena.push(Kind::Bool(true), ChcSort::Bool, scope)?
        } else {
            arena.operation(op, children, scope)?
        }
    } else if let Kind::ConstArray(value) = &arena.nodes[id].kind {
        let value = *value;
        let key = match &arena.nodes[id].sort {
            ChcSort::Array(key, _)
                if matches!(key.as_ref(), ChcSort::Bool | ChcSort::BitVec(1..=128)) =>
            {
                // Admitted scalar key sorts clone without allocation.
                key.as_ref().clone()
            }
            _ => return Err(Failure::Declined),
        };
        let value = apply(value, rule, arena, memo, depth + 1, scope)?;
        arena.constant_array(&key, value, scope)?
    } else {
        id
    };
    memo[id] = Some(result);
    Ok(result)
}
