// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed bounded MODEL DATA topology. Indices have no native provenance.

use super::{charge, ArraySnapshot, ArrayValue, FunctionalArrayError, ModelValue, Node, Sort};
use num_bigint::BigInt;
use std::mem::size_of;

mod import;
mod terms;
pub use terms::SnapshotTermError;
#[cfg(test)]
mod tests;

const MAX_NODES: usize = 4096;
const MAX_STORES: usize = 32_768;
const MAX_BYTES: usize = 16 * 1024 * 1024;

/// Untrusted borrowed description; only checked import constructs snapshots.
/// References are strict backwards indices into the SAME description slice.
#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub enum SnapshotKind<'a> {
    Finite(&'a ArrayValue),
    Store {
        base: usize,
        index: &'a ModelValue,
        value: &'a ModelValue,
    },
    Range {
        destination: usize,
        source: usize,
        lo: &'a BigInt,
        hi: &'a BigInt,
        source_lo: &'a BigInt,
    },
}

/// Explicit sort and complete data for one node, including unused operands.
#[derive(Clone, Copy, Debug)]
pub struct SnapshotNode<'a> {
    pub sort: &'a Sort,
    pub kind: SnapshotKind<'a>,
}

/// A borrowed postorder DAG retaining shared edges and ordered finite stores.
/// This contains no declaration names, query roots, term IDs or proof seals.
#[derive(Debug)]
pub struct SnapshotTopology<'a> {
    nodes: Vec<SnapshotNode<'a>>,
    root: usize,
}

impl SnapshotTopology<'_> {
    pub fn nodes(&self) -> &[SnapshotNode<'_>] {
        &self.nodes
    }
    pub fn root(&self) -> usize {
        self.root
    }
}

enum Ledger<'w, 's> {
    Remaining {
        work: &'w mut usize,
        stop: &'s mut dyn FnMut() -> bool,
    },
    Progress(&'s mut dyn FnMut(usize, usize) -> bool),
}

struct Budget<'w, 's> {
    ledger: Ledger<'w, 's>,
    refused: bool,
    bytes: usize,
    stores: usize,
}

impl<'w, 's> Budget<'w, 's> {
    fn new(work: &'w mut usize, stop: &'s mut dyn FnMut() -> bool) -> Self {
        Self {
            ledger: Ledger::Remaining { work, stop },
            refused: false,
            bytes: 0,
            stores: 0,
        }
    }

    fn with_progress(progress: &'s mut dyn FnMut(usize, usize) -> bool) -> Self {
        Self {
            ledger: Ledger::Progress(progress),
            refused: false,
            bytes: 0,
            stores: 0,
        }
    }

    fn debit(&mut self, work: usize, bytes: usize) -> Result<(), FunctionalArrayError> {
        if self.refused {
            return Err(FunctionalArrayError::Resource);
        }
        self.refused = true;
        match &mut self.ledger {
            Ledger::Remaining { work: left, stop } => {
                if stop() {
                    **left = 0;
                    return Err(FunctionalArrayError::Resource);
                }
                charge(left, work)?;
            }
            Ledger::Progress(progress) => {
                if !progress(work, bytes) {
                    return Err(FunctionalArrayError::Resource);
                }
            }
        }
        self.refused = false;
        Ok(())
    }

    fn poll(&mut self) -> Result<(), FunctionalArrayError> {
        self.debit(0, 0)
    }

    fn pay(&mut self, amount: usize) -> Result<(), FunctionalArrayError> {
        self.debit(amount, 0)
    }

    fn storage(&mut self, bytes: usize) -> Result<(), FunctionalArrayError> {
        let total = self
            .bytes
            .checked_add(bytes)
            .filter(|n| *n <= MAX_BYTES)
            .ok_or(FunctionalArrayError::Resource)?;
        self.debit(bytes, bytes)?;
        self.bytes = total;
        Ok(())
    }

    fn reserve<T>(
        &mut self,
        values: &mut Vec<T>,
        extra: usize,
    ) -> Result<(), FunctionalArrayError> {
        let count = values
            .len()
            .checked_add(extra)
            .ok_or(FunctionalArrayError::Resource)?;
        // Conservatively prepay a whole new backing allocation AND old moves,
        // even if the allocator can grow in place or existing capacity suffices.
        let bytes = count
            .checked_add(values.len())
            .and_then(|n| n.checked_mul(size_of::<T>()))
            .ok_or(FunctionalArrayError::Resource)?;
        self.storage(bytes)?;
        values
            .try_reserve_exact(extra)
            .map_err(|_| FunctionalArrayError::Allocation)
    }

    fn stores(&mut self, count: usize) -> Result<(), FunctionalArrayError> {
        self.stores = self
            .stores
            .checked_add(count)
            .filter(|n| *n <= MAX_STORES)
            .ok_or(FunctionalArrayError::Resource)?;
        self.pay(count)
    }

    fn finish<T>(
        &mut self,
        result: Result<T, FunctionalArrayError>,
    ) -> Result<T, FunctionalArrayError> {
        match result {
            Ok(value) => {
                self.poll()?;
                Ok(value)
            }
            Err(error) => {
                self.refused = true;
                if let Ledger::Remaining { work, .. } = &mut self.ledger {
                    **work = 0;
                }
                Err(error)
            }
        }
    }
}

impl ArraySnapshot {
    /// Export complete borrowed data under the existing owner's ledger.
    /// All refusal (including cancellation) consumes that ledger to zero.
    /// Linear identity scans are prepaid; large DAGs can refuse below MAX_NODES.
    pub fn topology<'a>(
        &'a self,
        work: &mut usize,
        stop: &mut dyn FnMut() -> bool,
    ) -> Result<SnapshotTopology<'a>, FunctionalArrayError> {
        let mut budget = Budget::new(work, stop);
        let result = export(self, &mut budget);
        budget.finish(result)
    }

    /// Export complete borrowed DATA with direct original-owner prepayment.
    ///
    /// The callback owns the SAME finite work/storage/end/stop ledger across
    /// export, construction and disposal; no balance or allowance is created.
    /// Every scan/reservation is paid before work, and scratch drops before the
    /// final zero poll. The returned vector's eventual disposal is also priced.
    /// Allocation/overflow refusal must be latched by that original caller
    /// before retry. Callback panic and whole caller-owned snapshot disposal
    /// remain caller responsibilities, not RSS or hard-preemption promises.
    pub fn topology_with_progress<'a>(
        &'a self,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<SnapshotTopology<'a>, FunctionalArrayError> {
        let mut budget = Budget::with_progress(progress);
        let result = export(self, &mut budget);
        budget.finish(result)
    }
}

fn export<'a>(
    root: &'a ArraySnapshot,
    budget: &mut Budget<'_, '_>,
) -> Result<SnapshotTopology<'a>, FunctionalArrayError> {
    let mut nodes = Vec::new();
    let mut originals = Vec::new();
    let root = visit(root, 1, &mut originals, &mut nodes, budget)?;
    Ok(SnapshotTopology { nodes, root })
}

fn visit<'a>(
    current: &'a ArraySnapshot,
    depth: usize,
    originals: &mut Vec<&'a ArraySnapshot>,
    nodes: &mut Vec<SnapshotNode<'a>>,
    budget: &mut Budget<'_, '_>,
) -> Result<usize, FunctionalArrayError> {
    budget.pay(
        originals
            .len()
            .checked_add(1)
            .ok_or(FunctionalArrayError::Resource)?,
    )?;
    if depth > 64 {
        return Err(FunctionalArrayError::Resource);
    }
    if let Some(index) = originals
        .iter()
        .position(|prior| std::ptr::eq(*prior, current))
    {
        return Ok(index);
    }
    let kind = match &current.node {
        Node::Finite(value) => SnapshotKind::Finite(value),
        Node::Store { base, index, value } => SnapshotKind::Store {
            base: visit(base, depth + 1, originals, nodes, budget)?,
            index,
            value,
        },
        Node::Range {
            destination,
            source,
            lo,
            hi,
            source_lo,
        } => SnapshotKind::Range {
            destination: visit(destination, depth + 1, originals, nodes, budget)?,
            source: visit(source, depth + 1, originals, nodes, budget)?,
            lo,
            hi,
            source_lo,
        },
    };
    if nodes.len() >= MAX_NODES {
        return Err(FunctionalArrayError::Resource);
    }
    let description = SnapshotNode {
        sort: &current.sort,
        kind,
    };
    import::validate_export(description, budget)?;
    budget.reserve(originals, 1)?;
    budget.reserve(nodes, 1)?;
    let index = nodes.len();
    originals.push(current);
    nodes.push(description);
    Ok(index)
}
