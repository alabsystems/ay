// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The per-context node and sort tables behind every `Z3_ast` and `Z3_sort`.

use std::cell::RefCell;
use std::ffi::c_uint;

use ay_dpll::api::{Sort, Term};
use rustc_hash::FxHashMap;

/// One public AST node. An untagged `Z3_ast` carries `PubId + 1` as its
/// payload (see `term_to_ast` in the parent module).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct PubId(u32);

impl PubId {
    /// The id behind a handle payload's 0-based index.
    pub(crate) fn from_raw(raw: u32) -> Self {
        Self(raw)
    }

    /// The 0-based index this id occupies in its store.
    pub(crate) fn raw(self) -> u32 {
        self.0
    }

    fn index(self) -> usize {
        self.0 as usize
    }
}

/// One public sort: the context's stable semantic sort id, the same number
/// `Z3_get_sort_id` reports and every `Z3_sort` of that sort carries.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct SortId(c_uint);

impl SortId {
    /// The number `SortHandle::sort_id` stores (ids start at 1).
    pub(crate) fn raw(self) -> c_uint {
        self.0
    }
}

/// What a public node is.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) enum NodeData {
    /// An engine term exposed at a public sort. Migration only (P1 to P8):
    /// P9 deletes this variant.
    ///
    /// `sort` is the public sort the handle was minted at. `None` means no
    /// public sort was ever stated for the term: the node reads as the engine
    /// term's own sort, and the first sort stated for the term is written into
    /// this node rather than minting a second one, so a handle minted before
    /// its sort was known keeps its identity (the old per-term sort table did
    /// the same).
    Engine { term: Term, sort: Option<SortId> },
}

impl NodeData {
    fn sort(self) -> Option<SortId> {
        match self {
            Self::Engine { sort, .. } => sort,
        }
    }
}

/// Nodes are keyed by engine term: almost every term has exactly one public
/// node, so the term's entry in `latest` finds it with one hash, and only a
/// term that stands for several public objects (the finite-domain value 3 and
/// the integer 3) has `others`. The content key (term, sort) is unique.
#[derive(Default)]
struct Nodes {
    data: Vec<NodeData>,
    /// The node a bare engine term reads as: the one minted or re-sorted for
    /// it last. An engine-produced term (a child, a model value, a simplified
    /// form) carries no public sort of its own, so it reads as the public
    /// object the caller last built over it, as every handle did when the
    /// arena held one handle per term.
    latest: FxHashMap<Term, PubId>,
    /// The term's other nodes, each at a different public sort.
    others: FxHashMap<Term, Vec<PubId>>,
}

impl Nodes {
    fn push(&mut self, node: NodeData) -> Option<PubId> {
        let id = PubId(u32::try_from(self.data.len()).ok()?);
        self.data.try_reserve(1).ok()?;
        self.data.push(node);
        Some(id)
    }

    fn sort_of(&self, id: PubId) -> Option<SortId> {
        self.data.get(id.index()).and_then(|node| node.sort())
    }

    /// Make `term` read as its node at `sort` when the node it reads as now
    /// (`current`) has another sort: an existing node of `others`, or a new
    /// one. `current` moves to `others`.
    fn switch_sort(&mut self, term: Term, current: PubId, sort: SortId) -> Option<PubId> {
        let found = self.others.get(&term).and_then(|others| {
            others
                .iter()
                .position(|&other| self.sort_of(other) == Some(sort))
        });
        let id = match found {
            Some(position) => self.others.get_mut(&term)?.swap_remove(position),
            None => self.push(NodeData::Engine {
                term,
                sort: Some(sort),
            })?,
        };
        let others = self.others.entry(term).or_default();
        others.try_reserve(1).ok()?;
        others.push(current);
        self.latest.insert(term, id);
        Some(id)
    }
}

/// Ids of the three sorts nearly every construction states, so stating them
/// costs no hash of a `Sort`.
#[derive(Default)]
struct CommonSorts {
    bool_sort: Option<SortId>,
    int_sort: Option<SortId>,
    real_sort: Option<SortId>,
}

impl CommonSorts {
    fn slot(&mut self, sort: &Sort) -> Option<&mut Option<SortId>> {
        match sort {
            Sort::Bool => Some(&mut self.bool_sort),
            Sort::Int => Some(&mut self.int_sort),
            Sort::Real => Some(&mut self.real_sort),
            _ => None,
        }
    }
}

/// The public AST of one context: nodes interned by (engine term, public
/// sort), and sorts interned by value. Invariant: an unsorted node
/// `Engine { term, None }` exists only while no other node holds `term`.
#[derive(Default)]
pub(crate) struct PubStore {
    /// Interior mutability keeps minting a node possible from read-only
    /// introspection paths, as the arena it replaces did. Z3 contexts already
    /// require externally synchronized, non-aliased access.
    nodes: RefCell<Nodes>,
    sorts: Vec<Sort>,
    sort_ids: FxHashMap<Sort, SortId>,
    common: CommonSorts,
}

impl PubStore {
    /// The node `term` reads as when no public sort is given: the latest node
    /// over `term`, or a new unsorted one. `None` only when the store is full
    /// or an allocation fails.
    pub(crate) fn engine_node(&self, term: Term) -> Option<PubId> {
        self.engine_node_owned(term, None)
    }

    /// SAME node publication with native original-owner preflight. No borrow
    /// of the RefCell survives an arbitrary admission/cancellation callback.
    pub(crate) fn engine_node_owned(
        &self,
        term: Term,
        owner: Option<&dyn ay_core::term::TermConstructionAdmission>,
    ) -> Option<PubId> {
        let Some(owner) = owner else {
            let mut nodes = self.nodes.borrow_mut();
            if let Some(&id) = nodes.latest.get(&term) {
                return Some(id);
            }
            nodes.latest.try_reserve(1).ok()?;
            let id = nodes.push(NodeData::Engine { term, sort: None })?;
            nodes.latest.insert(term, id);
            return Some(id);
        };
        loop {
            owner.check().ok()?;
            let snapshot = {
                let nodes = self.nodes.try_borrow().ok()?;
                if let Some(&id) = nodes.latest.get(&term) {
                    drop(nodes);
                    owner.check().ok()?;
                    return Some(id);
                }
                (
                    nodes.data.len(),
                    nodes.data.capacity(),
                    nodes.latest.len(),
                    nodes.latest.capacity(),
                )
            };
            let (len, capacity, map_len, map_capacity) = snapshot;
            let vec_bytes = if len == capacity {
                capacity
                    .checked_mul(2)?
                    .max(4)
                    .checked_mul(size_of::<NodeData>())?
            } else {
                0
            };
            // Same conservative native table growth envelope as counted
            // registry maps: whole replacement buckets/control bytes plus
            // copies, not an allowance or a physical live-memory assertion.
            let map_bytes = if map_len == map_capacity {
                map_capacity
                    .checked_mul(size_of::<(Term, PubId)>())?
                    .checked_mul(4)?
                    .checked_add(4096)?
            } else {
                0
            };
            let copies = if vec_bytes != 0 { len } else { 0 };
            let rehash = if map_bytes != 0 { map_capacity } else { 0 };
            owner
                .admit(
                    copies.checked_add(rehash)?.checked_add(1)?,
                    vec_bytes.checked_add(map_bytes)?,
                )
                .ok()?;
            let mut nodes = self.nodes.try_borrow_mut().ok()?;
            if (
                nodes.data.len(),
                nodes.data.capacity(),
                nodes.latest.len(),
                nodes.latest.capacity(),
            ) != snapshot
            {
                drop(nodes);
                continue;
            }
            nodes.latest.try_reserve(1).ok()?;
            let id = nodes.push(NodeData::Engine { term, sort: None })?;
            nodes.latest.insert(term, id);
            drop(nodes);
            owner.check().ok()?;
            return Some(id);
        }
    }

    /// The node for `term` at public sort `sort`, interned, and from now on
    /// the node `term` reads as; with the sort of the node `term` read as
    /// before, if any. An unsorted node over `term` takes the sort in place
    /// (see [`NodeData::Engine`]).
    pub(crate) fn sorted_node(
        &mut self,
        term: Term,
        sort: SortId,
    ) -> Option<(PubId, Option<SortId>)> {
        let nodes = self.nodes.get_mut();
        let Some(current) = nodes.latest.get(&term).copied() else {
            nodes.latest.try_reserve(1).ok()?;
            let id = nodes.push(NodeData::Engine {
                term,
                sort: Some(sort),
            })?;
            nodes.latest.insert(term, id);
            return Some((id, None));
        };
        let previous = nodes.sort_of(current);
        match previous {
            Some(stated) if stated == sort => Some((current, previous)),
            None => {
                let slot = nodes.data.get_mut(current.index())?;
                *slot = NodeData::Engine {
                    term,
                    sort: Some(sort),
                };
                Some((current, None))
            }
            Some(_) => Some((nodes.switch_sort(term, current, sort)?, previous)),
        }
    }

    /// The node `term` reads as, without minting one.
    pub(crate) fn latest(&self, term: Term) -> Option<PubId> {
        self.nodes.borrow().latest.get(&term).copied()
    }

    /// Whether `term` stands for several public objects: it has a node at
    /// more than one public sort (the finite-domain value 3 and the integer
    /// 3, a `Char` and its code point). A walk over engine terms cannot tell
    /// those objects apart.
    pub(crate) fn is_shared(&self, term: Term) -> bool {
        self.nodes
            .borrow()
            .others
            .get(&term)
            .is_some_and(|others| !others.is_empty())
    }

    /// The content of `id`, if this store minted it.
    pub(crate) fn node(&self, id: PubId) -> Option<NodeData> {
        self.nodes.borrow().data.get(id.index()).copied()
    }

    /// How many nodes this store holds.
    pub(crate) fn len(&self) -> usize {
        self.nodes.borrow().data.len()
    }

    /// The id of `sort`, assigning the next one (from 1) on first sight.
    pub(crate) fn intern_sort(&mut self, sort: &Sort) -> Option<SortId> {
        if let Some(Some(id)) = self.common.slot(sort).map(|slot| *slot) {
            return Some(id);
        }
        let id = match self.sort_ids.get(sort) {
            Some(&id) => id,
            None => {
                let next = SortId(u32::try_from(self.sorts.len()).ok()?.checked_add(1)?);
                self.sorts.try_reserve(1).ok()?;
                self.sort_ids.try_reserve(1).ok()?;
                self.sorts.push(sort.clone());
                self.sort_ids.insert(sort.clone(), next);
                next
            }
        };
        if let Some(slot) = self.common.slot(sort) {
            *slot = Some(id);
        }
        Some(id)
    }

    /// The sort `id` names, if this store assigned it.
    pub(crate) fn sort(&self, id: SortId) -> Option<&Sort> {
        let index = usize::try_from(id.0).ok()?.checked_sub(1)?;
        self.sorts.get(index)
    }

    /// How many sort ids have been assigned (the largest id).
    pub(crate) fn sort_count(&self) -> usize {
        self.sorts.len()
    }
}

#[cfg(test)]
mod admitted_tactic_tests {
    use super::*;
    use ay_core::original_query::{CountedAdmission, CountedAdmissionError, FiniteAdmissionGrant};
    use ay_core::term::TermConstructionAdmission;
    use std::cell::Cell;
    use std::sync::Arc;

    #[test]
    fn ff2bv_public_node_admission_releases_borrows_and_rechecks_reentry() {
        let mut solver = ay_dpll::api::Solver::new(ay_dpll::api::Logic::All);
        let first = solver.bool_const(true);
        let second = solver.bool_const(false);
        let store = PubStore::default();
        struct Reentrant<'a> {
            store: &'a PubStore,
            other: Term,
            once: Cell<bool>,
            original: CountedAdmission,
        }
        impl TermConstructionAdmission for Reentrant<'_> {
            fn admit(&self, work: usize, bytes: usize) -> Result<(), CountedAdmissionError> {
                self.original.admit(work, bytes)?;
                if work > 0 && !self.once.replace(true) {
                    assert!(self.store.engine_node(self.other).is_some());
                }
                self.original.check()
            }
            fn refuse(&self, error: CountedAdmissionError) -> CountedAdmissionError {
                self.original.refuse(error)
            }
        }
        let owner = Reentrant {
            store: &store,
            other: second,
            once: Cell::new(false),
            original: CountedAdmission::new(
                FiniteAdmissionGrant::new(100_000, 1 << 20),
                None,
                Arc::new(|| false),
            )
            .expect("reentrant test admission must initialize"),
        };
        let id = store
            .engine_node_owned(first, Some(&owner))
            .expect("admitted engine node must be stored");
        assert!(matches!(store.node(id),Some(NodeData::Engine{term,..}) if term==first));
        assert!(owner.once.get());
        let stopped =
            CountedAdmission::new(FiniteAdmissionGrant::new(0, 0), None, Arc::new(|| false))
                .expect("zero-budget test admission must initialize");
        let fresh = PubStore::default();
        assert!(fresh.engine_node_owned(first, Some(&stopped)).is_none());
        assert!(fresh.latest(first).is_none());
        assert!(fresh.engine_node_owned(first, Some(&stopped)).is_none());
    }
}
