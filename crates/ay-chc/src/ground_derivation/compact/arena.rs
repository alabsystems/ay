// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Error, Owner, Result, ValueId, ValueNode};
use ay_core::kani_compat::DetHashMap;

#[derive(Debug, Default)]
pub(crate) struct Arena {
    nodes: Vec<ValueNode>,
    interned: DetHashMap<ValueNode, ValueId>,
}

impl Arena {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn nodes(&self) -> &[ValueNode] {
        &self.nodes
    }

    pub(crate) fn get(&self, id: ValueId) -> Option<&ValueNode> {
        self.nodes.get(id.0 as usize)
    }

    pub(crate) fn intern(&mut self, node: &ValueNode, owner: &mut Owner) -> Result<ValueId> {
        let result = self.intern_inner(node, owner);
        match result {
            Err(Error::Resource) => owner.refuse(Error::Resource),
            other => other,
        }
    }

    fn intern_inner(&mut self, node: &ValueNode, owner: &mut Owner) -> Result<ValueId> {
        owner.poll()?;
        let payload = match node {
            ValueNode::Bool(_) => 1,
            ValueNode::BitVec { value, width } => {
                if *width == 0
                    || *width > crate::MAX_BITVECTOR_WIDTH
                    || value.bits() > u64::from(*width)
                {
                    return Err(Error::InvalidValue);
                }
                usize::try_from(value.bits().div_ceil(8)).map_err(|_| Error::Resource)?
            }
            ValueNode::Datatype {
                sort,
                constructor,
                fields,
            } => sort
                .len()
                .checked_add(constructor.len())
                .and_then(|n| fields.len().checked_mul(8).and_then(|m| n.checked_add(m)))
                .ok_or(Error::Resource)?,
        };
        // Hashing and both owned copies (vector and interning key) are charged
        // before lookup/allocation. No recursive field expansion is involved.
        let bytes = payload
            .checked_mul(4)
            .and_then(|n| n.checked_add(256))
            .ok_or(Error::Resource)?;
        owner.admit(payload.saturating_add(1), bytes)?;
        if let ValueNode::Datatype { fields, .. } = node {
            if fields.iter().any(|id| self.get(*id).is_none()) {
                return Err(Error::InvalidValue);
            }
        }
        if let Some(id) = self.interned.get(node) {
            return Ok(*id);
        }
        let id = ValueId(u32::try_from(self.nodes.len()).map_err(|_| Error::Resource)?);
        if self.nodes.try_reserve(1).is_err() || self.interned.try_reserve(1).is_err() {
            return owner.refuse(Error::Resource);
        }
        self.nodes.push(node.clone());
        self.interned.insert(node.clone(), id);
        owner.poll()?;
        Ok(id)
    }
}
