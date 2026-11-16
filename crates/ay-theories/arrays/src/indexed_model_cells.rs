// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Controlled ordered cell DATA; neither a model credential nor a new grant.
//!
//! Borrowed complete keys avoid string/bignum clones in the index. Stable row
//! slots preserve duplicate FIFO authority. This additive API does not retrofit
//! an owner into the legacy infallible array-theory extraction/printing paths.

use ay_core::original_query::{QueryError, WorkBudget};
use num_bigint::BigInt;

mod index;
use index::{Node, NONE};

/// An exact borrowed key, with no normalization or low-word surrogate.
#[derive(Clone, Copy, Debug)]
pub enum ModelCellKey<'a> {
    /// The existing array interpretation's exact internal spelling.
    Text(&'a str),
    /// A decoded Boolean key.
    Bool(bool),
    /// A decoded width-tagged bitvector; the COMPLETE integer is retained.
    /// Structural equality is over both fields, not implicit modular coercion.
    BitVec {
        /// Declared bit width, retained without truncation.
        width: u32,
        /// Complete decoded integer, borrowed without conversion.
        value: &'a BigInt,
    },
}

/// One ordered borrowed row; values are exact existing internal spellings.
#[derive(Clone, Copy, Debug)]
pub struct ModelCellRow<'a> {
    /// Full cell identity.
    pub key: ModelCellKey<'a>,
    /// Existing value text, borrowed without invented defaults.
    pub value: &'a str,
}

/// Existing store authority; only soft cells yield to committed reads.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CellAuthority {
    /// A concrete original store remains authoritative.
    Concrete,
    /// A speculative existing store may be replaced by a committed read.
    Soft,
}

#[derive(Clone, Copy)]
struct Row<'a> {
    cell: ModelCellRow<'a>,
    next: usize,
    live: bool,
}

/// Immutable completed rows and whether a select conflict removed a cell.
pub struct IndexedModelCellRows<'a> {
    rows: Vec<ModelCellRow<'a>>,
    read_conflicted: bool,
}

impl<'a> IndexedModelCellRows<'a> {
    /// Ordered live rows, retaining original duplicates that were not removed.
    pub fn rows(&self) -> &[ModelCellRow<'a>] {
        &self.rows
    }
    /// No poisoned cell may be repaired by a subsequent observation.
    pub fn read_conflicted(&self) -> bool {
        self.read_conflicted
    }
}

/// A bounded cell transaction borrowing the SAME original ledger until finish.
///
/// `maximum_rows` is a caller-derived upper bound, not an allowance. All three
/// Vec capacities, visits, full-key comparisons and disposal visits are charged
/// BEFORE work/allocation. No BTreeMap, queue allocation, owned key or value
/// clone exists here. A storage guarantee requires `WorkBudget::with_admission`;
/// its compatibility constructor only checks its documented work/stop envelope.
/// Allocator bookkeeping, opaque deallocation and physical RSS are not bounded.
pub struct IndexedModelCells<'a, 'budget, 'owner> {
    work: &'budget mut WorkBudget<'owner>,
    rows: Vec<Row<'a>>,
    nodes: Vec<Node<'a>>,
    root: usize,
    maximum_rows: usize,
    read_conflicted: bool,
}

impl<'a, 'budget, 'owner> IndexedModelCells<'a, 'budget, 'owner> {
    /// Prepay and fallibly reserve a single fixed-capacity transaction.
    pub fn new(
        maximum_rows: usize,
        work: &'budget mut WorkBudget<'owner>,
    ) -> Result<Self, QueryError> {
        let bytes = maximum_rows
            .checked_mul(
                size_of::<Row<'a>>() + size_of::<Node<'a>>() + size_of::<ModelCellRow<'a>>(),
            )
            .ok_or_else(|| work.refuse_exhaustion())?;
        work.admit(maximum_rows, bytes)?;
        let mut rows = Vec::new();
        let mut nodes = Vec::new();
        rows.try_reserve_exact(maximum_rows)
            .map_err(|_| work.refuse_exhaustion())?;
        nodes
            .try_reserve_exact(maximum_rows)
            .map_err(|_| work.refuse_exhaustion())?;
        work.charge(0)?;
        Ok(Self {
            work,
            rows,
            nodes,
            root: NONE,
            maximum_rows,
            read_conflicted: false,
        })
    }

    /// Preserve a pre-existing newest-first row and its original soft-key flag.
    /// A soft flag is key-wide, matching the legacy `soft_store_indices` set.
    pub fn push_original(
        &mut self,
        cell: ModelCellRow<'a>,
        authority: CellAuthority,
    ) -> Result<(), QueryError> {
        let node = self.append(cell)?;
        self.nodes[node].soft |= authority == CellAuthority::Soft;
        self.work.charge(0)
    }

    /// Read the first live duplicate without silently swallowing refusal.
    pub fn first(&mut self, key: ModelCellKey<'a>) -> Result<Option<ModelCellRow<'a>>, QueryError> {
        let Some(node) = self.find(key)? else {
            return Ok(None);
        };
        let head = self.nodes[node].head;
        self.work.charge(1)?;
        let result = (head != NONE).then(|| self.rows[head].cell);
        self.work.charge(0)?;
        Ok(result)
    }

    /// Apply the exact legacy concrete/soft/select/poison precedence.
    pub fn observe(&mut self, cell: ModelCellRow<'a>) -> Result<(), QueryError> {
        let Some(node) = self.find(cell.key)? else {
            let node = self.append(cell)?;
            self.nodes[node].derived = true;
            return self.work.charge(0);
        };
        self.work.charge(1)?;
        if self.nodes[node].poisoned {
            return Ok(());
        }
        let head = self.nodes[node].head;
        if head == NONE {
            self.append(cell)?;
            self.nodes[node].derived = true;
        } else if !index::text_equal(self.rows[head].cell.value, cell.value, self.work)? {
            if self.nodes[node].derived {
                self.remove_node_first(node)?;
                self.nodes[node].poisoned = true;
                self.read_conflicted = true;
            } else if self.nodes[node].soft {
                self.rows[head].cell.value = cell.value;
                self.nodes[node].derived = true;
            }
        }
        self.work.charge(0)
    }

    /// Legacy chronological witness upsert: remove only the first, append last.
    pub fn upsert_newest(&mut self, cell: ModelCellRow<'a>) -> Result<(), QueryError> {
        if let Some(node) = self.find(cell.key)? {
            if self.nodes[node].poisoned {
                return self.work.charge(0);
            }
            self.remove_node_first(node)?;
        }
        self.append(cell)?;
        self.work.charge(0)
    }

    /// Reconstructed cells are weaker than any direct existing row.
    pub fn insert_missing(&mut self, cell: ModelCellRow<'a>) -> Result<(), QueryError> {
        if let Some(node) = self.find(cell.key)? {
            if self.nodes[node].poisoned {
                return self.work.charge(0);
            }
        }
        if self.first(cell.key)?.is_none() {
            self.append(cell)?;
        }
        self.work.charge(0)
    }

    fn append(&mut self, cell: ModelCellRow<'a>) -> Result<usize, QueryError> {
        self.work.charge(1)?;
        if self.rows.len() == self.maximum_rows {
            return Err(self.work.refuse_exhaustion());
        }
        let old = self.find(cell.key)?;
        if let Some(node) = old {
            if self.nodes[node].poisoned {
                return Ok(node);
            }
        }
        let position = self.rows.len();
        self.rows.push(Row {
            cell,
            next: NONE,
            live: true,
        });
        if let Some(node) = old {
            let tail = self.nodes[node].tail;
            if tail == NONE {
                self.nodes[node].head = position;
            } else {
                self.rows[tail].next = position;
            }
            self.nodes[node].tail = position;
            return Ok(node);
        }
        let node = self.nodes.len();
        self.nodes.push(Node::new(cell.key, position));
        self.root = self.insert(self.root, node, 0)?;
        Ok(node)
    }

    fn remove_node_first(&mut self, node: usize) -> Result<(), QueryError> {
        self.work.charge(1)?;
        let head = self.nodes[node].head;
        if head != NONE {
            self.rows[head].live = false;
            self.nodes[node].head = self.rows[head].next;
            if self.nodes[node].head == NONE {
                self.nodes[node].tail = NONE;
            }
        }
        Ok(())
    }

    /// Finalize only after every scratch container was freed and the SAME
    /// owner was re-polled. An error never publishes partial/missing cells.
    pub fn finish(self) -> Result<IndexedModelCellRows<'a>, QueryError> {
        let Self {
            work,
            rows,
            nodes,
            read_conflicted,
            ..
        } = self;
        work.charge(0)?;
        let mut result = Vec::new();
        result
            .try_reserve_exact(rows.len())
            .map_err(|_| work.refuse_exhaustion())?;
        for row in &rows {
            work.charge(1)?;
            if row.live {
                result.push(row.cell);
            }
        }
        // Copy-only records have no recursive payload destructors; prepay all
        // disposal visits, then poll AFTER the allocator-owned frees.
        let visits = rows
            .len()
            .checked_add(nodes.len())
            .ok_or_else(|| work.refuse_exhaustion())?;
        work.charge(visits)?;
        drop(rows);
        drop(nodes);
        work.charge(0)?;
        Ok(IndexedModelCellRows {
            rows: result,
            read_conflicted,
        })
    }
}

#[cfg(test)]
mod tests;
