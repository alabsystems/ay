// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::eval::Evaluation;
use super::source::Source;
use super::{Arena, CompactDerivation, CompactStep, Error, Owner, Result, ValueId, ValueNode};
use crate::{ChcProblem, ClauseHead, PredicateId};
use ay_core::kani_compat::DetHashMap;

type Head = Option<(PredicateId, Vec<ValueId>)>;

pub(crate) fn validate(
    problem: &ChcProblem,
    derivation: &CompactDerivation,
    owner: &mut Owner,
) -> Result<()> {
    let _scope = owner.enter();
    let result = validate_inner(problem, derivation, owner);
    if result == Err(Error::Resource) {
        return owner.refuse(Error::Resource);
    }
    result
}

fn validate_inner(
    problem: &ChcProblem,
    derivation: &CompactDerivation,
    owner: &mut Owner,
) -> Result<()> {
    let mut source = Source::new(problem, owner)?;
    source.validate(owner)?;
    let mut arena = Arena::new();
    let roots = replay_arena(&mut source, &derivation.arena, &mut arena, owner)?;
    reachable(derivation, owner)?;
    let mut heads = Vec::new();
    owner.admit(
        derivation.steps.len(),
        derivation
            .steps
            .len()
            .checked_mul(64)
            .ok_or(Error::Resource)?,
    )?;
    if heads.try_reserve(derivation.steps.len()).is_err() {
        return owner.refuse(Error::Resource);
    }
    for (index, step) in derivation.steps.iter().enumerate() {
        let head = replay_step(&mut source, step, &roots, &mut arena, &heads, owner)?;
        if head.is_none() && index != derivation.query_step {
            return Err(Error::InvalidDerivation);
        }
        heads.push(head);
    }
    if heads.get(derivation.query_step) != Some(&None) {
        return Err(Error::InvalidDerivation);
    }
    owner.poll()
}

fn replay_arena(
    source: &mut Source<'_>,
    original: &Arena,
    arena: &mut Arena,
    owner: &mut Owner,
) -> Result<Vec<ValueId>> {
    owner.admit(
        original.nodes().len(),
        original
            .nodes()
            .len()
            .checked_mul(16)
            .ok_or(Error::Resource)?,
    )?;
    let mut roots = Vec::new();
    if roots.try_reserve(original.nodes().len()).is_err() {
        return owner.refuse(Error::Resource);
    }
    for node in original.nodes() {
        let id = if let ValueNode::Datatype {
            sort,
            constructor,
            fields,
        } = node
        {
            owner.admit(
                sort.len()
                    .saturating_add(constructor.len())
                    .saturating_add(fields.len()),
                sort.len()
                    .saturating_add(constructor.len())
                    .saturating_add(fields.len().saturating_mul(16)),
            )?;
            let definition = source
                .problem
                .datatype_defs()
                .get(sort)
                .ok_or(Error::InvalidValue)?;
            let [(expected, selectors)] = definition.as_slice() else {
                return Err(Error::Unsupported);
            };
            if constructor != expected || fields.len() != selectors.len() {
                return Err(Error::InvalidValue);
            }
            let mut mapped = Vec::new();
            if mapped.try_reserve(fields.len()).is_err() {
                return owner.refuse(Error::Resource);
            }
            for (field, (_, expected)) in fields.iter().zip(selectors) {
                let root = *roots.get(field.0 as usize).ok_or(Error::InvalidValue)?;
                if source.value_type(arena.get(root).ok_or(Error::InvalidValue)?, owner)?
                    != source.sort(expected, owner, 0)?
                {
                    return Err(Error::InvalidValue);
                }
                mapped.push(root);
            }
            arena.intern(
                &ValueNode::Datatype {
                    sort: sort.clone(),
                    constructor: constructor.clone(),
                    fields: mapped,
                },
                owner,
            )?
        } else {
            arena.intern(node, owner)?
        };
        roots.push(id);
    }
    Ok(roots)
}

fn replay_step<'a>(
    source: &mut Source<'a>,
    step: &CompactStep,
    roots: &[ValueId],
    arena: &mut Arena,
    heads: &[Head],
    owner: &mut Owner,
) -> Result<Head> {
    let clause = source
        .problem
        .clauses()
        .get(step.clause_index)
        .ok_or(Error::InvalidDerivation)?;
    let vars = source.clause(clause, owner)?.vars;
    if vars.len() != step.env.len() || clause.body.predicates.len() != step.premises.len() {
        return Err(Error::InvalidDerivation);
    }
    owner.admit(
        vars.len(),
        vars.len().checked_mul(128).ok_or(Error::Resource)?,
    )?;
    let mut env = DetHashMap::default();
    if env.try_reserve(vars.len()).is_err() {
        return owner.refuse(Error::Resource);
    }
    for (name, expected) in vars {
        owner.admit(name.len().saturating_add(1), 0)?;
        let original = step.env.get(name).ok_or(Error::InvalidDerivation)?;
        let root = *roots.get(original.0 as usize).ok_or(Error::InvalidValue)?;
        if source.value_type(arena.get(root).ok_or(Error::InvalidValue)?, owner)? != expected {
            return Err(Error::InvalidValue);
        }
        env.insert(name, root);
    }
    let mut eval = Evaluation {
        source,
        arena,
        env: &env,
        owner,
        cache: DetHashMap::default(),
    };
    if let Some(guard) = &clause.body.constraint {
        let value = eval.expression(guard, 0)?;
        if eval.arena.get(value) != Some(&ValueNode::Bool(true)) {
            return Err(Error::InvalidDerivation);
        }
    }
    for ((predicate, args), premise) in clause.body.predicates.iter().zip(&step.premises) {
        let Some(Some((actual_predicate, actual_args))) = heads.get(*premise) else {
            return Err(Error::InvalidDerivation);
        };
        if predicate != actual_predicate || args.len() != actual_args.len() {
            return Err(Error::InvalidDerivation);
        }
        for (arg, expected) in args.iter().zip(actual_args) {
            if eval.expression(arg, 0)? != *expected {
                return Err(Error::InvalidDerivation);
            }
        }
    }
    match &clause.head {
        ClauseHead::False => Ok(None),
        ClauseHead::Predicate(predicate, args) => {
            eval.owner.admit(
                args.len(),
                args.len().checked_mul(16).ok_or(Error::Resource)?,
            )?;
            let mut values = Vec::new();
            if values.try_reserve(args.len()).is_err() {
                return eval.owner.refuse(Error::Resource);
            }
            for arg in args {
                values.push(eval.expression(arg, 0)?);
            }
            Ok(Some((*predicate, values)))
        }
    }
}

fn reachable(derivation: &CompactDerivation, owner: &mut Owner) -> Result<()> {
    let count = derivation.steps.len();
    if count == 0 || derivation.query_step != count - 1 {
        return Err(Error::InvalidDerivation);
    }
    owner.admit(count, count.checked_mul(2).ok_or(Error::Resource)?)?;
    let mut seen = Vec::new();
    if seen.try_reserve(count).is_err() {
        return owner.refuse(Error::Resource);
    }
    seen.resize(count, false);
    seen[derivation.query_step] = true;
    for index in (0..count).rev() {
        if !seen[index] {
            return Err(Error::InvalidDerivation);
        }
        owner.admit(derivation.steps[index].premises.len(), 0)?;
        for premise in &derivation.steps[index].premises {
            if *premise >= index {
                return Err(Error::InvalidDerivation);
            }
            seen[*premise] = true;
        }
    }
    Ok(())
}
