// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{Arena, Error, Key, Owner, Result};

struct Class {
    parent: usize,
    rank: usize,
    literal: Option<usize>,
    array: Option<usize>,
}

pub(super) struct Classes(Vec<Class>);

impl Classes {
    pub(super) fn new(arena: &Arena<'_>, owner: &mut Owner<'_>) -> Result<Self> {
        let mut result = Self(Vec::new());
        result.extend(arena, owner)?;
        Ok(result)
    }

    pub(super) fn extend(&mut self, arena: &Arena<'_>, owner: &mut Owner<'_>) -> Result<()> {
        let extra = arena
            .len()
            .checked_sub(self.0.len())
            .ok_or(Error::Resource)?;
        let bytes = extra
            .checked_mul(2 * std::mem::size_of::<Class>())
            .ok_or(Error::Resource)?;
        owner.admit(extra, bytes)?;
        self.0.try_reserve(extra).map_err(|_| Error::Resource)?;
        for id in self.0.len()..arena.len() {
            let literal =
                matches!(arena.node(id).key, Key::Bool(_) | Key::BitVec(..)).then_some(id);
            let array = matches!(arena.node(id).key, Key::ConstArray(..)).then_some(id);
            self.0.push(Class {
                parent: id,
                rank: 0,
                literal,
                array,
            });
        }
        Ok(())
    }

    pub(super) fn root(&mut self, mut id: usize, owner: &mut Owner<'_>) -> Result<usize> {
        loop {
            // Path halving is charged before reads and parent mutation, not
            // only at successful unions. Even adversarial chains are bounded.
            owner.admit(1, 0)?;
            let parent = self.0[id].parent;
            if parent == id {
                return Ok(id);
            }
            self.0[id].parent = self.0[parent].parent;
            id = parent;
        }
    }

    pub(super) fn same(&mut self, a: usize, b: usize, owner: &mut Owner<'_>) -> Result<bool> {
        Ok(self.root(a, owner)? == self.root(b, owner)?)
    }

    pub(super) fn literal(&mut self, id: usize, owner: &mut Owner<'_>) -> Result<Option<usize>> {
        let root = self.root(id, owner)?;
        Ok(self.0[root].literal)
    }

    pub(super) fn array(&mut self, id: usize, owner: &mut Owner<'_>) -> Result<Option<usize>> {
        let root = self.root(id, owner)?;
        Ok(self.0[root].array)
    }

    pub(super) fn union(
        &mut self,
        a: usize,
        b: usize,
        arena: &Arena<'_>,
        owner: &mut Owner<'_>,
    ) -> Result<bool> {
        owner.admit(1, 0)?;
        if arena.node(a).sort != arena.node(b).sort {
            return Err(Error::InvalidSource);
        }
        let mut a = self.root(a, owner)?;
        let mut b = self.root(b, owner)?;
        if a == b {
            return Ok(false);
        }
        if self.0[a].rank < self.0[b].rank {
            std::mem::swap(&mut a, &mut b);
        }
        owner.admit(1, 0)?;
        if self.0[a].rank == self.0[b].rank {
            self.0[a].rank = self.0[a].rank.checked_add(1).ok_or(Error::Resource)?;
        }
        self.0[b].parent = a;
        // Either representative is a proved member of the class. Choosing the
        // earliest makes rule selection deterministic, even for contradictions.
        self.0[a].literal = earliest(self.0[a].literal, self.0[b].literal);
        self.0[a].array = earliest(self.0[a].array, self.0[b].array);
        Ok(true)
    }
}

fn earliest(a: Option<usize>, b: Option<usize>) -> Option<usize> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (a, b) => a.or(b),
    }
}
