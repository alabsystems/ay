// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The clause-id side table, keyed by arena word offset, stored one slot per
//! [`STRIDE`] arena words (AY-SAT-1).
//!
//! # Why
//!
//! `ColdState::clause_ids` maps a clause's arena WORD offset to its proof id.
//! It used to be a `Vec<u64>` with one entry per arena word, so it cost 8
//! bytes per word: twice the arena itself. With a proof on, it is written on
//! every load, and it was the largest single structure behind the SAT-COMP
//! memouts of AY-SAT-1. Measured with `--sat-mem-probe` on 5220b0e0 (33.6 M
//! clauses, VeriPB proof, ceiling 16000 MiB): `clause_ids=3187.3` MB against
//! `arena=2047.7` MB, of a live total of 12.8 GB after 2,728 conflicts. On
//! e85fb114 (82.2 M clauses) the table would have grown past 5.8 GB.
//!
//! # How
//!
//! Every clause occupies at least [`STRIDE`] (`HEADER_WORDS`) arena words,
//! because the header alone is that long; so two clause starts `a < b` satisfy
//! `b >= a + STRIDE`, hence `a / STRIDE < b / STRIDE`. One slot per `STRIDE`
//! words therefore gives every clause start a slot of its own. Each slot also
//! records which offset of its `STRIDE` words owns it (`tags`), so a read at an
//! offset that does not own the slot answers 0 ("no id"), exactly what the old
//! vector held at an offset that was never written, and never another
//! clause's id. Cost: 9 bytes per `STRIDE` words instead of 8 per word, 3 bytes
//! per word, 62.5% less.
//!
//! The table keeps the vector's logical length (one past the largest offset
//! it covers), so every `idx < len()` guard and every out-of-range panic of
//! the old `Vec<u64>` reads the same.
//!
//! # The one rule: only clause starts are written
//!
//! With one entry per word, a write at an offset that is not a clause start
//! was harmless. Here it would take over the slot of the clause start that
//! shares it and erase that clause's id, so the proof would lose a hint or
//! skip a deletion. [`ClauseIdTable::set`] therefore refuses (a `BUG` panic)
//! to take a slot from another offset that still holds a non-zero id. Offsets
//! are only reused after the arena is rebuilt (`compact_arena_locality`
//! builds a fresh table, `preprocess_reset` clears it) or rolled back
//! (`rollback_appends`, whose rungs' ids are taken to 0 first), so a correct
//! caller never meets the panic. Under that rule every read, `contains` and
//! `iter_recorded` answer exactly what the per-word vector answered: a slot
//! changes owner only while its old owner's id is 0, which the vector also
//! read as "no id" (AY-SAT-1).

use crate::clause_arena::HEADER_WORDS;
use crate::counted_storage;
use ay_core::original_query::CountedAdmission;
use std::mem::size_of;

/// Arena words per slot: the shortest possible clause (its header).
pub(crate) const STRIDE: usize = HEADER_WORDS;

/// Tag of a slot no offset owns.
const UNOWNED: u8 = 0;

static ZERO_ID: u64 = 0;

/// Clause ids keyed by arena word offset; see the module note.
#[derive(Clone, Debug, Default, Eq)]
pub(crate) struct ClauseIdTable {
    /// Logical length: one past the largest offset covered, as the old
    /// vector's `len()`.
    len: usize,
    /// The id of the clause owning each slot (0 when none).
    ids: Vec<u64>,
    /// `UNOWNED`, or 1 + the owning offset's position within its slot.
    tags: Vec<u8>,
}

#[inline]
fn slot_of(offset: usize) -> usize {
    offset / STRIDE
}

#[inline]
fn tag_of(offset: usize) -> u8 {
    // STRIDE is 3, so the residue fits in a u8 with room for UNOWNED.
    (offset % STRIDE) as u8 + 1
}

#[inline]
fn slots_for(len: usize) -> usize {
    len.div_ceil(STRIDE)
}

impl ClauseIdTable {
    /// An empty, unallocated table.
    pub(crate) const fn new() -> Self {
        Self {
            len: 0,
            ids: Vec::new(),
            tags: Vec::new(),
        }
    }

    /// A table covering offsets `0..len`, every one without an id (the old
    /// `vec![0u64; len]`).
    pub(crate) fn with_len(len: usize) -> Self {
        let slots = slots_for(len);
        Self {
            len,
            ids: vec![0; slots],
            tags: vec![UNOWNED; slots],
        }
    }

    /// One past the largest offset covered.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.len
    }

    /// Whether no offset is covered.
    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// Whether the table holds an allocation (the old `capacity() != 0`).
    #[inline]
    pub(crate) fn is_allocated(&self) -> bool {
        self.ids.capacity() != 0
    }

    /// Heap bytes the table holds.
    #[inline]
    pub(crate) fn heap_bytes(&self) -> usize {
        self.ids.capacity() * size_of::<u64>() + self.tags.capacity()
    }

    /// Heap bytes held beyond what the covered offsets need.
    #[inline]
    pub(crate) fn slack_bytes(&self) -> usize {
        (self.ids.capacity() - self.ids.len()) * size_of::<u64>()
            + (self.tags.capacity() - self.tags.len())
    }

    /// Heap bytes a reservation for `len` offsets takes.
    #[inline]
    pub(crate) fn bytes_for_len(len: usize) -> usize {
        slots_for(len) * (size_of::<u64>() + size_of::<u8>())
    }

    /// The id recorded at `offset`, 0 when none; `None` past `len()`.
    #[inline]
    pub(crate) fn get(&self, offset: usize) -> Option<&u64> {
        if offset >= self.len {
            return None;
        }
        let slot = slot_of(offset);
        if self.tags[slot] == tag_of(offset) {
            Some(&self.ids[slot])
        } else {
            Some(&ZERO_ID)
        }
    }

    /// The id recorded at `offset` for update; `None` past `len()` and when
    /// another offset owns the slot (it has no id of its own to update).
    #[inline]
    pub(crate) fn get_mut(&mut self, offset: usize) -> Option<&mut u64> {
        if offset >= self.len {
            return None;
        }
        let slot = slot_of(offset);
        if self.tags[slot] == tag_of(offset) {
            Some(&mut self.ids[slot])
        } else {
            None
        }
    }

    /// Record `id` at `offset`, which must be below `len()`. The slot becomes
    /// `offset`'s.
    ///
    /// Panics (a `BUG`) when another offset of the same slot still holds a
    /// non-zero id: two offsets less than a header apart cannot both be
    /// clause starts, so the write is at a non-start or stale offset and
    /// would silently erase a live clause's proof id (module note).
    #[inline]
    pub(crate) fn set(&mut self, offset: usize, id: u64) {
        assert!(
            offset < self.len,
            "BUG: clause id offset {offset} past table length {}",
            self.len
        );
        let slot = slot_of(offset);
        let tag = tag_of(offset);
        let owner = self.tags[slot];
        assert!(
            owner == UNOWNED || owner == tag || self.ids[slot] == 0,
            "BUG: clause id write at offset {offset} would erase id {} of clause start {}",
            self.ids[slot],
            slot * STRIDE + usize::from(owner.saturating_sub(1))
        );
        self.tags[slot] = tag;
        self.ids[slot] = id;
    }

    /// Whether every offset below `prefix.len()` reads here what it reads in
    /// `prefix` (the old `Vec::starts_with`).
    #[cfg(test)]
    pub(crate) fn starts_with(&self, prefix: &ClauseIdTable) -> bool {
        prefix.len <= self.len
            && (0..prefix.len).all(|offset| self.get(offset) == prefix.get(offset))
    }

    /// Slot `slot` as reads see it: an owned slot holding 0 reads exactly as
    /// an unowned one.
    #[inline]
    fn read_slot(&self, slot: usize) -> (u8, u64) {
        match self.ids[slot] {
            0 => (UNOWNED, 0),
            id => (self.tags[slot], id),
        }
    }

    /// Cover offsets `0..len` (the old `resize(len, 0)`); never shrinks.
    pub(crate) fn grow_to(&mut self, len: usize) {
        if len <= self.len {
            return;
        }
        self.len = len;
        let slots = slots_for(len);
        if slots > self.ids.len() {
            self.ids.resize(slots, 0);
            self.tags.resize(slots, UNOWNED);
        }
    }

    /// Reserve room for offsets `0..len` exactly (the old `reserve_exact`
    /// of an empty vector).
    pub(crate) fn reserve_exact_len(&mut self, len: usize) {
        let slots = slots_for(len);
        self.ids.reserve_exact(slots.saturating_sub(self.ids.len()));
        self.tags
            .reserve_exact(slots.saturating_sub(self.tags.len()));
    }

    /// Counted form of [`Self::reserve_exact_len`] for an unallocated table.
    pub(crate) fn try_reserve_exact_len_counted(
        &mut self,
        owner: &CountedAdmission,
        len: usize,
    ) -> counted_storage::Result<()> {
        let slots = slots_for(len);
        let additional = slots.saturating_sub(self.ids.len());
        if additional == 0 {
            return Ok(());
        }
        if !self.is_allocated() {
            self.ids = counted_storage::try_reserved_exact(owner, slots)?;
            self.tags = counted_storage::try_reserved_exact(owner, slots)?;
            return Ok(());
        }
        counted_storage::try_reserve(owner, &mut self.ids, additional)?;
        counted_storage::try_reserve(owner, &mut self.tags, additional)
    }

    /// Counted reservation so that offsets `0..len` are covered without
    /// further allocation.
    pub(crate) fn try_reserve_len_counted(
        &mut self,
        owner: &CountedAdmission,
        len: usize,
    ) -> counted_storage::Result<()> {
        let additional = slots_for(len).saturating_sub(self.ids.len());
        counted_storage::try_reserve(owner, &mut self.ids, additional)?;
        counted_storage::try_reserve(owner, &mut self.tags, additional)
    }

    /// Drop every entry, keeping the allocation (the old `clear`).
    pub(crate) fn clear(&mut self) {
        self.len = 0;
        self.ids.clear();
        self.tags.clear();
    }

    /// Give back the slack (the old `shrink_to_fit`).
    pub(crate) fn shrink_to_fit(&mut self) {
        self.ids.shrink_to_fit();
        self.tags.shrink_to_fit();
    }

    /// Whether some clause start carries `id`.
    pub(crate) fn contains(&self, id: &u64) -> bool {
        self.ids
            .iter()
            .zip(&self.tags)
            .any(|(stored, &tag)| tag != UNOWNED && stored == id)
    }

    /// Every recorded `(offset, id)`, ascending by offset, ids of 0 included.
    pub(crate) fn iter_recorded(&self) -> impl Iterator<Item = (usize, u64)> + '_ {
        self.ids
            .iter()
            .zip(&self.tags)
            .enumerate()
            .filter(|&(_, (_, &tag))| tag != UNOWNED)
            .map(|(slot, (&id, &tag))| (slot * STRIDE + usize::from(tag - 1), id))
    }
}

/// Equal when every offset reads the same id, as two per-word vectors of the
/// same length compare: an owned slot holding 0 equals an unowned one.
impl PartialEq for ClauseIdTable {
    fn eq(&self, other: &Self) -> bool {
        self.len == other.len
            && self.ids.len() == other.ids.len()
            && (0..self.ids.len()).all(|slot| self.read_slot(slot) == other.read_slot(slot))
    }
}

impl std::ops::Index<usize> for ClauseIdTable {
    type Output = u64;

    /// The id at `offset` (0 when none); panics past `len()` like the old
    /// vector.
    #[inline]
    fn index(&self, offset: usize) -> &u64 {
        match self.get(offset) {
            Some(id) => id,
            None => panic!(
                "BUG: clause id offset {offset} past table length {}",
                self.len
            ),
        }
    }
}

#[cfg(test)]
#[path = "clause_id_table_tests.rs"]
mod tests;
