// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Array-backed AVL index (Adelson-Velsky/Landis 1962). Each actual tree
//! comparison/rotation is admitted. Hashes only select candidate buckets.

use super::*;
use std::hash::BuildHasher;

struct Node {
    hash: u64,
    ids: Vec<TermId>,
    left: Option<usize>,
    right: Option<usize>,
    height: usize,
}

#[derive(Default)]
pub(super) struct Index {
    nodes: Vec<Node>,
    root: Option<usize>,
}

impl Index {
    pub(super) fn get(
        &self,
        hash: u64,
        owner: &dyn TermConstructionAdmission,
    ) -> Result<Option<&[TermId]>> {
        let mut current = self.root;
        while let Some(index) = current {
            owner.admit(1, 0)?;
            let node = &self.nodes[index];
            match hash.cmp(&node.hash) {
                std::cmp::Ordering::Equal => return Ok(Some(&node.ids)),
                std::cmp::Ordering::Less => current = node.left,
                std::cmp::Ordering::Greater => current = node.right,
            }
        }
        Ok(None)
    }

    pub(super) fn insert(
        &mut self,
        hash: u64,
        id: TermId,
        owner: &dyn TermConstructionAdmission,
    ) -> Result<()> {
        self.root = Some(self.insert_at(self.root, hash, id, owner, 0)?);
        Ok(())
    }

    fn insert_at(
        &mut self,
        root: Option<usize>,
        hash: u64,
        id: TermId,
        owner: &dyn TermConstructionAdmission,
        depth: usize,
    ) -> Result<usize> {
        owner.admit(1, 0)?;
        // An AVL tree on at most usize::MAX entries has height < 2*BITS.
        // Refuse corrupt scratch before recursion; this is not a node grant.
        if depth >= 2 * usize::BITS as usize {
            return Err(storage::work(owner));
        }
        let Some(root) = root else {
            storage::reserve(&mut self.nodes, 1, owner)?;
            let mut ids = Vec::new();
            storage::reserve(&mut ids, 1, owner)?;
            owner.admit(1, 0)?;
            ids.push(id);
            let index = self.nodes.len();
            self.nodes.push(Node {
                hash,
                ids,
                left: None,
                right: None,
                height: 1,
            });
            return Ok(index);
        };
        match hash.cmp(&self.nodes[root].hash) {
            std::cmp::Ordering::Equal => {
                storage::reserve(&mut self.nodes[root].ids, 1, owner)?;
                self.nodes[root].ids.push(id);
                return Ok(root);
            }
            std::cmp::Ordering::Less => {
                let child = self.insert_at(self.nodes[root].left, hash, id, owner, depth + 1)?;
                self.nodes[root].left = Some(child);
            }
            std::cmp::Ordering::Greater => {
                let child = self.insert_at(self.nodes[root].right, hash, id, owner, depth + 1)?;
                self.nodes[root].right = Some(child);
            }
        }
        self.balance(root, owner)
    }

    fn height(&self, node: Option<usize>) -> usize {
        node.map_or(0, |index| self.nodes[index].height)
    }

    fn update(&mut self, node: usize) {
        self.nodes[node].height = 1 + self
            .height(self.nodes[node].left)
            .max(self.height(self.nodes[node].right));
    }

    fn balance(&mut self, root: usize, owner: &dyn TermConstructionAdmission) -> Result<usize> {
        owner.admit(1, 0)?;
        self.update(root);
        let left = self.height(self.nodes[root].left);
        let right = self.height(self.nodes[root].right);
        if left > right + 1 {
            let child = self.nodes[root]
                .left
                .ok_or(CountedTermError::InvalidInput)?;
            if self.height(self.nodes[child].right) > self.height(self.nodes[child].left) {
                self.nodes[root].left = Some(self.rotate_left(child, owner)?);
            }
            return self.rotate_right(root, owner);
        }
        if right > left + 1 {
            let child = self.nodes[root]
                .right
                .ok_or(CountedTermError::InvalidInput)?;
            if self.height(self.nodes[child].left) > self.height(self.nodes[child].right) {
                self.nodes[root].right = Some(self.rotate_right(child, owner)?);
            }
            return self.rotate_left(root, owner);
        }
        Ok(root)
    }

    fn rotate_left(&mut self, root: usize, owner: &dyn TermConstructionAdmission) -> Result<usize> {
        owner.admit(1, 0)?;
        let child = self.nodes[root]
            .right
            .ok_or(CountedTermError::InvalidInput)?;
        self.nodes[root].right = self.nodes[child].left;
        self.nodes[child].left = Some(root);
        self.update(root);
        self.update(child);
        Ok(child)
    }

    fn rotate_right(
        &mut self,
        root: usize,
        owner: &dyn TermConstructionAdmission,
    ) -> Result<usize> {
        owner.admit(1, 0)?;
        let child = self.nodes[root]
            .left
            .ok_or(CountedTermError::InvalidInput)?;
        self.nodes[root].left = self.nodes[child].right;
        self.nodes[child].right = Some(root);
        self.update(root);
        self.update(child);
        Ok(child)
    }
}

pub(super) fn name_hash(name: &str) -> u64 {
    foldhash::fast::FixedState::default().hash_one(name)
}
