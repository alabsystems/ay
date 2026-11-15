// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::project::Projection;
use super::variables::{Sort, Variables};
use super::{reserve, text, Error, Owner, Result, MAX_DEPTH};
use crate::ground_derivation::compact::{
    Arena, CompactDerivation, CompactStep, ValueId, ValueNode,
};
use crate::{ChcProblem, SmtValue};
use ay_core::kani_compat::DetHashMap;
use num_bigint::BigUint;

struct Builder<'a> {
    problem: &'a ChcProblem,
    arena: Arena,
    defaults: DetHashMap<Sort<'a>, ValueId>,
}

pub(super) fn build<'a>(
    problem: &'a ChcProblem,
    path: &[usize],
    variables: &Variables<'a>,
    projection: &Projection<'a>,
    model: &DetHashMap<String, SmtValue>,
    owner: &mut Owner,
) -> Result<CompactDerivation> {
    let mut builder = Builder {
        problem,
        arena: Arena::new(),
        defaults: DetHashMap::default(),
    };
    let mut values = Vec::new();
    reserve(&mut values, variables.declarations.len(), owner)?;
    values.resize(variables.declarations.len(), None);
    for (index, var) in variables.declarations.iter().enumerate() {
        if variables.root(index, owner)? == index {
            values[index] = Some(builder.default(Sort::read(&var.sort)?, 0, owner)?);
        }
    }
    for demand in &projection.demands {
        owner.admit(demand.name.len().saturating_add(1), 0)?;
        let leaf = match model.get(&demand.name) {
            Some(value) => builder.scalar(value, demand.sort, owner)?,
            // Solvers may omit unconstrained variables. Concrete defaults are
            // candidates only; the full original checker must still accept.
            None => builder.default(demand.sort, 0, owner)?,
        };
        let root = values
            .get(demand.root)
            .copied()
            .flatten()
            .ok_or(Error::InvalidValue)?;
        let value = builder.overlay(root, &demand.path, leaf, 0, owner)?;
        values[demand.root] = Some(value);
    }
    let mut steps = Vec::new();
    reserve(&mut steps, path.len(), owner)?;
    for (step, &clause_index) in path.iter().enumerate() {
        let mut env = DetHashMap::default();
        for (&name, &index) in &variables.frames[step] {
            owner.admit(name.len().saturating_add(1), 80)?;
            if env.try_reserve(1).is_err() {
                return owner.refuse(Error::Resource);
            }
            let root = variables.root(index, owner)?;
            let value = values
                .get(root)
                .copied()
                .flatten()
                .ok_or(Error::InvalidValue)?;
            env.insert(text(name, owner)?, value);
        }
        let mut premises = Vec::new();
        if step != 0 {
            reserve(&mut premises, 1, owner)?;
            premises.push(step - 1);
        }
        steps.push(CompactStep {
            clause_index,
            env,
            premises,
        });
    }
    let query_step = steps.len().checked_sub(1).ok_or(Error::InvalidDerivation)?;
    owner.poll()?;
    Ok(CompactDerivation {
        arena: builder.arena,
        steps,
        query_step,
    })
}

impl<'a> Builder<'a> {
    fn default(&mut self, sort: Sort<'a>, depth: usize, owner: &mut Owner) -> Result<ValueId> {
        owner.admit(1, 0)?;
        if depth >= MAX_DEPTH {
            return owner.refuse(Error::Resource);
        }
        if let Sort::Product(name) = sort {
            owner.admit(name.len(), 0)?;
        }
        if let Some(&value) = self.defaults.get(&sort) {
            return Ok(value);
        }
        let node = match sort {
            Sort::Bool => ValueNode::Bool(false),
            Sort::BitVec(width) => ValueNode::BitVec {
                value: BigUint::from(0u8),
                width,
            },
            Sort::Product(name) => {
                let definitions = self
                    .problem
                    .datatype_defs()
                    .get(name)
                    .ok_or(Error::InvalidSource)?;
                let [(constructor, selectors)] = definitions.as_slice() else {
                    return Err(Error::Unsupported);
                };
                let mut fields = Vec::new();
                reserve(&mut fields, selectors.len(), owner)?;
                for (_, field_sort) in selectors {
                    fields.push(self.default(Sort::read(field_sort)?, depth + 1, owner)?);
                }
                ValueNode::Datatype {
                    sort: text(name, owner)?,
                    constructor: text(constructor, owner)?,
                    fields,
                }
            }
        };
        let value = self.arena.intern(&node, owner)?;
        owner.admit(1, 80)?;
        if self.defaults.try_reserve(1).is_err() {
            return owner.refuse(Error::Resource);
        }
        self.defaults.insert(sort, value);
        Ok(value)
    }

    fn scalar(&mut self, value: &SmtValue, sort: Sort<'_>, owner: &mut Owner) -> Result<ValueId> {
        let node = match (sort, value) {
            (Sort::Bool, SmtValue::Bool(value)) => ValueNode::Bool(*value),
            (Sort::BitVec(width), SmtValue::BitVec(value, actual)) if width == *actual => {
                if width < 128 && (*value >> width) != 0 {
                    return Err(Error::InvalidValue);
                }
                owner.admit(1, 16)?;
                ValueNode::BitVec {
                    value: BigUint::from(*value),
                    width,
                }
            }
            (Sort::BitVec(width), SmtValue::BigBitVec(value, actual)) if width == *actual => {
                if value.bits() > u64::from(width) {
                    return Err(Error::InvalidValue);
                }
                let bytes =
                    usize::try_from((u64::from(width) + 7) / 8).map_err(|_| Error::Resource)?;
                owner.admit(bytes, bytes)?;
                ValueNode::BitVec {
                    value: value.as_ref().clone(),
                    width,
                }
            }
            _ => return Err(Error::InvalidValue),
        };
        self.arena.intern(&node, owner)
    }

    fn overlay(
        &mut self,
        root: ValueId,
        path: &[usize],
        leaf: ValueId,
        depth: usize,
        owner: &mut Owner,
    ) -> Result<ValueId> {
        owner.admit(1, 0)?;
        if depth >= MAX_DEPTH {
            return owner.refuse(Error::Resource);
        }
        let Some((&index, rest)) = path.split_first() else {
            return Ok(leaf);
        };
        let Some(ValueNode::Datatype {
            sort,
            constructor,
            fields,
        }) = self.arena.get(root)
        else {
            return Err(Error::InvalidValue);
        };
        let child = *fields.get(index).ok_or(Error::InvalidValue)?;
        let sort = text(sort, owner)?;
        let constructor = text(constructor, owner)?;
        let mut replacement = Vec::new();
        reserve(&mut replacement, fields.len(), owner)?;
        replacement.extend_from_slice(fields);
        replacement[index] = self.overlay(child, rest, leaf, depth + 1, owner)?;
        self.arena.intern(
            &ValueNode::Datatype {
                sort,
                constructor,
                fields: replacement,
            },
            owner,
        )
    }
}
