// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! AVL insertion, index-only links and complete borrowed-key comparisons.
//! AVL balance is the standard height-difference invariant (Adelson-Velsky
//! and Landis, 1962); no randomized hash, string surrogate or key allocation.

use super::*;
use std::cmp::Ordering;

pub(super) const NONE: usize = usize::MAX;

pub(super) struct Node<'a> {
    key: ModelCellKey<'a>,
    left: usize,
    right: usize,
    height: usize,
    pub(super) head: usize,
    pub(super) tail: usize,
    pub(super) soft: bool,
    pub(super) derived: bool,
    pub(super) poisoned: bool,
}

impl<'a> Node<'a> {
    pub(super) fn new(key: ModelCellKey<'a>, position: usize) -> Self {
        Self {
            key,
            left: NONE,
            right: NONE,
            height: 1,
            head: position,
            tail: position,
            soft: false,
            derived: false,
            poisoned: false,
        }
    }
}

impl<'a> IndexedModelCells<'a, '_, '_> {
    pub(super) fn find(&mut self, key: ModelCellKey<'a>) -> Result<Option<usize>, QueryError> {
        self.work.charge(0)?;
        let mut current = self.root;
        while current != NONE {
            self.work.charge(1)?;
            current = match compare(key, self.nodes[current].key, self.work)? {
                Ordering::Less => self.nodes[current].left,
                Ordering::Greater => self.nodes[current].right,
                Ordering::Equal => {
                    self.work.charge(0)?;
                    return Ok(Some(current));
                }
            };
        }
        self.work.charge(0)?;
        Ok(None)
    }

    pub(super) fn insert(
        &mut self,
        root: usize,
        node: usize,
        depth: usize,
    ) -> Result<usize, QueryError> {
        self.work.charge(1)?;
        if depth > 2 * usize::BITS as usize {
            return Err(self.work.refuse_exhaustion());
        }
        if root == NONE {
            return Ok(node);
        }
        match compare(self.nodes[node].key, self.nodes[root].key, self.work)? {
            Ordering::Less => {
                self.nodes[root].left = self.insert(self.nodes[root].left, node, depth + 1)?
            }
            Ordering::Greater => {
                self.nodes[root].right = self.insert(self.nodes[root].right, node, depth + 1)?
            }
            Ordering::Equal => return Err(self.work.refuse_exhaustion()),
        }
        self.update(root);
        let left = self.nodes[root].left;
        let right = self.nodes[root].right;
        if self.height(left) > self.height(right) + 1 {
            if self.height(self.nodes[left].right) > self.height(self.nodes[left].left) {
                self.nodes[root].left = self.rotate_left(left)?;
            }
            return self.rotate_right(root);
        }
        if self.height(right) > self.height(left) + 1 {
            if self.height(self.nodes[right].left) > self.height(self.nodes[right].right) {
                self.nodes[root].right = self.rotate_right(right)?;
            }
            return self.rotate_left(root);
        }
        Ok(root)
    }

    fn height(&self, node: usize) -> usize {
        if node == NONE {
            0
        } else {
            self.nodes[node].height
        }
    }

    fn update(&mut self, node: usize) {
        self.nodes[node].height = 1 + self
            .height(self.nodes[node].left)
            .max(self.height(self.nodes[node].right));
    }

    fn rotate_left(&mut self, root: usize) -> Result<usize, QueryError> {
        self.work.charge(1)?;
        let child = self.nodes[root].right;
        self.nodes[root].right = self.nodes[child].left;
        self.nodes[child].left = root;
        self.update(root);
        self.update(child);
        Ok(child)
    }

    fn rotate_right(&mut self, root: usize) -> Result<usize, QueryError> {
        self.work.charge(1)?;
        let child = self.nodes[root].left;
        self.nodes[root].left = self.nodes[child].right;
        self.nodes[child].right = root;
        self.update(root);
        self.update(child);
        Ok(child)
    }
}

fn compare(
    left: ModelCellKey<'_>,
    right: ModelCellKey<'_>,
    work: &mut WorkBudget<'_>,
) -> Result<Ordering, QueryError> {
    work.charge(1)?;
    match (left, right) {
        (ModelCellKey::Text(a), ModelCellKey::Text(b)) => text_compare(a, b, work),
        (ModelCellKey::Bool(a), ModelCellKey::Bool(b)) => Ok(a.cmp(&b)),
        (
            ModelCellKey::BitVec {
                width: a,
                value: av,
            },
            ModelCellKey::BitVec {
                width: b,
                value: bv,
            },
        ) => {
            let bytes = av
                .bits()
                .checked_add(bv.bits())
                .and_then(|bits| bits.checked_add(14))
                .and_then(|bits| usize::try_from(bits / 8).ok())
                .ok_or_else(|| work.refuse_exhaustion())?;
            // BigInt's comparison is a bounded opaque scan, not a new clone.
            for _ in 0..bytes / 128 {
                work.charge(128)?;
            }
            work.charge(bytes % 128 + 1)?;
            Ok(a.cmp(&b).then_with(|| av.cmp(bv)))
        }
        (ModelCellKey::Text(_), _) | (ModelCellKey::Bool(_), ModelCellKey::BitVec { .. }) => {
            Ok(Ordering::Less)
        }
        _ => Ok(Ordering::Greater),
    }
}

fn text_compare(
    left: &str,
    right: &str,
    work: &mut WorkBudget<'_>,
) -> Result<Ordering, QueryError> {
    for (a, b) in left
        .as_bytes()
        .chunks(128)
        .zip(right.as_bytes().chunks(128))
    {
        work.charge(a.len() + b.len() + 1)?;
        let order = a.cmp(b);
        if order != Ordering::Equal {
            return Ok(order);
        }
    }
    work.charge(1)?;
    Ok(left.len().cmp(&right.len()))
}

pub(super) fn text_equal(
    left: &str,
    right: &str,
    work: &mut WorkBudget<'_>,
) -> Result<bool, QueryError> {
    Ok(text_compare(left, right, work)? == Ordering::Equal)
}

#[cfg(test)]
pub(super) fn assert_balanced(cells: &IndexedModelCells<'_, '_, '_>) {
    fn height(cells: &IndexedModelCells<'_, '_, '_>, node: usize) -> usize {
        if node == NONE {
            return 0;
        }
        let left = height(cells, cells.nodes[node].left);
        let right = height(cells, cells.nodes[node].right);
        assert!(left.abs_diff(right) <= 1);
        assert_eq!(cells.nodes[node].height, 1 + left.max(right));
        cells.nodes[node].height
    }
    assert!(height(cells, cells.root) <= 2 * usize::BITS as usize);
}
