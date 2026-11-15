// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Read-only eligibility and attempt-local search hints. No term or proof
//! constructor is available through the shared Context borrow. The ordinary
//! kernel derivation is still built and checked later over the actual terms.

use super::*;
use ay_core::term::{TermEntryStamp, TermStoreSnapshotStamp};
use ay_frontend::{Context, SourceContextStamp};

pub(super) struct ReadHints {
    source: SourceContextStamp,
    store: TermStoreSnapshotStamp,
    metadata: u64,
    original_end: usize,
    entries: HashMap<TermId, (TermEntryStamp, Option<ReadHint>)>,
    store_chains: HashMap<TermId, Rc<Vec<(TermId, TermId)>>>,
}

#[derive(Clone)]
pub(super) struct ReadHint {
    pub(super) array: TermId,
    pub(super) key: TermId,
    pub(super) at: TermId,
    pub(super) value: TermId,
    pub(super) position: usize,
    pub(super) element_sort: Sort,
    pub(super) skipped_keys: Vec<TermId>,
}

impl ReadHints {
    /// An untrusted, attempt-local memo bound to the current source universe.
    /// Construction alone establishes no read eligibility or proof authority.
    pub(super) fn empty(context: &Context) -> Self {
        Self {
            source: context.source_context_stamp(),
            store: context.terms.snapshot_stamp(),
            metadata: context.terms.checker_visible_metadata_generation(),
            original_end: context.terms.len(),
            entries: HashMap::default(),
            store_chains: HashMap::default(),
        }
    }

    pub(super) fn preflight(
        context: &Context,
        root: TermId,
        visits: &mut usize,
        stop: &dyn Fn() -> bool,
    ) -> Option<Self> {
        let mut result = Self::empty(context);
        let mut seen = HashSet::default();
        let mut pending = vec![(root, 0usize)];
        while let Some((term, depth)) = pending.pop() {
            Self::poll(visits, stop)?;
            if depth > MAX_SOURCE_DEPTH {
                return None;
            }
            context.terms.entry_stamp(term)?;
            if seen.contains(&term) {
                continue;
            }
            if seen.len() >= MAX_TERMS {
                return None;
            }
            seen.insert(term);
            let children = Self::children(&context.terms, term)?;
            if let TermData::App(Symbol::Named(head), args) = context.terms.get(term) {
                if head == "select" {
                    let [array, _] = args.as_slice() else {
                        return None;
                    };
                    // Opaque reads of an input array remain source leaves.
                    // Every computed-memory read must have a structural hit
                    // with readable skips before any new Eq/offset term exists.
                    if !matches!(context.terms.get(*array), TermData::Var(..)) {
                        result.read(context, term, visits, stop)?;
                    }
                }
            }
            pending.extend(children.into_iter().rev().map(|child| (child, depth + 1)));
        }
        Some(result)
    }

    pub(super) fn children(terms: &ay_core::TermStore, term: TermId) -> Option<Vec<TermId>> {
        terms.entry_stamp(term)?;
        match terms.get(term) {
            TermData::App(_, children) if children.len() <= 128 => Some(children.clone()),
            TermData::Not(child) => Some(vec![*child]),
            TermData::Ite(c, t, e) => Some(vec![*c, *t, *e]),
            TermData::Var(..) | TermData::Const(..) => Some(vec![]),
            _ => None,
        }
    }

    pub(super) fn poll(visits: &mut usize, stop: &dyn Fn() -> bool) -> Option<()> {
        *visits = visits.checked_add(1)?;
        (*visits <= MAX_VISITS && !stop()).then_some(())
    }

    pub(super) fn read(
        &mut self,
        context: &Context,
        term: TermId,
        visits: &mut usize,
        stop: &dyn Fn() -> bool,
    ) -> Option<ReadHint> {
        Self::poll(visits, stop)?;
        if self.source != context.source_context_stamp()
            || !self.store.is_append_only_prefix_of(&context.terms)
            || self.metadata != context.terms.checker_visible_metadata_generation()
        {
            return None;
        }
        let stamp = context.terms.entry_stamp(term)?;
        if !matches!(context.terms.get(term), TermData::App(Symbol::Named(head), args)
            if head == "select" && args.len() == 2)
        {
            return None;
        }
        if let Some((birth, hint)) = self.entries.get(&term) {
            return (*birth == stamp).then(|| hint.clone()).flatten();
        }
        let hint = self.read_uncached(&context.terms, term, visits, stop);
        // Cache only entries in the preflight arena prefix, not a claim of
        // authored-cone membership. A rebuilt read can hash-cons to an older
        // ID. New IDs are reconsidered; no hint grants proof authority.
        if term.index() < self.original_end {
            if self.entries.len() >= MAX_TERMS {
                return None;
            }
            self.entries.insert(term, (stamp, hint.clone()));
        }
        hint
    }

    fn read_uncached(
        &mut self,
        terms: &ay_core::TermStore,
        term: TermId,
        visits: &mut usize,
        stop: &dyn Fn() -> bool,
    ) -> Option<ReadHint> {
        let TermData::App(Symbol::Named(head), args) = terms.get(term) else {
            return None;
        };
        let [array, key] = args.as_slice() else {
            return None;
        };
        if head != "select" {
            return None;
        }
        let (array, key) = (*array, *key);
        let array_sort = terms.sort(array).clone();
        let Sort::Array(shape) = &array_sort else {
            return None;
        };
        if !matches!(&shape.index_sort, Sort::BitVec(width) if (1..=128).contains(&width.width))
            || !matches!(&shape.element_sort, Sort::Bool | Sort::BitVec(_))
            || terms.sort(key) != &shape.index_sort
            || terms.sort(term) != &shape.element_sort
        {
            return None;
        }
        // Validate every store, including the tail below a matching write.
        // Memoize only that exact fully checked immutable source chain.
        let stores = if let Some(chain) = self.store_chains.get(&array) {
            chain.clone()
        } else {
            if self.store_chains.len() >= MAX_TERMS {
                return None;
            }
            let mut stores = Vec::new();
            let mut cursor = array;
            loop {
                Self::poll(visits, stop)?;
                terms.entry_stamp(cursor)?;
                if terms.sort(cursor) != &array_sort {
                    return None;
                }
                let TermData::App(Symbol::Named(op), args) = terms.get(cursor) else {
                    break;
                };
                if op != "store" {
                    break;
                }
                let [base, at, value] = args.as_slice() else {
                    return None;
                };
                if stores.len() >= MAX_SOURCE_DEPTH
                    || terms.entry_stamp(*base).is_none()
                    || terms.entry_stamp(*at).is_none()
                    || terms.entry_stamp(*value).is_none()
                    || terms.sort(*base) != &array_sort
                    || terms.sort(*at) != &shape.index_sort
                    || terms.sort(*value) != &shape.element_sort
                {
                    return None;
                }
                stores.push((*at, *value));
                cursor = *base;
            }
            let stores = Rc::new(stores);
            self.store_chains.insert(array, stores.clone());
            stores
        };
        let mut found = None;
        for (position, &(at, value)) in stores.iter().enumerate() {
            Self::poll(visits, stop)?;
            if Self::offset_relation(terms, key, at) == Some(true) {
                found = Some((position, at, value));
                break;
            }
        }
        let (position, at, value) = found?;
        let mut skipped_keys = Vec::with_capacity(position);
        for &(newer, _) in &stores[..position] {
            if Self::offset_relation(terms, at, newer) != Some(false) {
                return None;
            }
            skipped_keys.push(newer);
        }
        Some(ReadHint {
            array,
            key,
            at,
            value,
            position,
            element_sort: shape.element_sort.clone(),
            skipped_keys,
        })
    }

    fn offset_relation(terms: &ay_core::TermStore, left: TermId, right: TermId) -> Option<bool> {
        if left == right {
            return Some(true);
        }
        let reading = terms.bv_offset_equality(left, right)?;
        (reading.minuend == reading.subtrahend).then(|| reading.constant == 0u32.into())
    }
}
