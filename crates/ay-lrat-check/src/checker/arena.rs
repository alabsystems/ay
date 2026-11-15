// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause arena: literal storage, insertion, lookup, and compaction.
//!
//! Extracted from checker/mod.rs for the 500-line limit.

use crate::dimacs::Literal;
use std::io::Write;

use super::types::ClauseEntry;
use super::{LratChecker, MAX_DENSE_LITS, MAX_DENSE_VARS};

impl LratChecker {
    /// Look up clause literals by entry.
    ///
    /// Every entry in `clause_index` lies inside the arena (`insert_clause`
    /// and `compact_arena` maintain this). An entry that does not reads as
    /// no literals, which can only make a check fail, never pass: the one
    /// production caller asks whether the clause contains `~pivot`.
    #[inline]
    pub(crate) fn clause_lits(&self, entry: ClauseEntry) -> &[Literal] {
        let start = entry.start as usize;
        let end = start + entry.len as usize;
        self.clause_arena.get(start..end).unwrap_or(&[])
    }

    /// Insert a clause into the arena. Returns `None` on u32 overflow, or
    /// when a literal lies outside the dense envelope ([`MAX_DENSE_VARS`]).
    pub(super) fn insert_clause(
        &mut self,
        clause_id: u64,
        clause: &[Literal],
        tautological: bool,
        original: bool,
    ) -> Option<ClauseEntry> {
        let start = match u32::try_from(self.clause_arena.len()) {
            Ok(s) => s,
            Err(_) => {
                let _ = writeln!(
                    std::io::stderr(),
                    "LRAT FAIL: arena offset overflow ({} literals exceeds u32)",
                    self.clause_arena.len()
                );
                return None;
            }
        };
        let len = match u32::try_from(clause.len()) {
            Ok(l) => l,
            Err(_) => {
                let _ = writeln!(
                    std::io::stderr(),
                    "LRAT FAIL: clause length overflow ({} literals exceeds u32)",
                    clause.len()
                );
                return None;
            }
        };
        if start.checked_add(len).is_none() {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT FAIL: arena range overflow (start={start} + len={len})"
            );
            return None;
        }
        // Size the occurrence lists before touching the arena, so a literal
        // outside the dense envelope refuses the clause without leaving a
        // partial registration behind. Growth only adds empty lists.
        for &lit in clause {
            let idx = lit.index();
            if idx >= MAX_DENSE_LITS {
                let _ = writeln!(
                    std::io::stderr(),
                    "LRAT FAIL: literal {lit} exceeds the dense variable envelope {MAX_DENSE_VARS}"
                );
                return None;
            }
            if idx >= self.occ_lists.len() {
                self.occ_lists.resize_with(idx + 1, Vec::new);
            }
        }
        self.clause_arena.extend_from_slice(clause);
        // Register each literal in occurrence lists for O(occ) RAT lookup.
        for &lit in clause {
            match self.occ_lists.get_mut(lit.index()) {
                Some(occ) => occ.push(clause_id),
                // Unreachable: the loop above sized `occ_lists` for every
                // literal. Refusing keeps the clause out of `clause_index`, and
                // the caller records the failure.
                None => return None,
            }
        }
        let entry = ClauseEntry {
            start,
            len,
            hint_gen: 0,
            tautological,
            original,
        };
        self.clause_index.insert(clause_id, entry);
        Some(entry)
    }

    /// Compact the clause arena by removing dead space from deleted clauses (#8624).
    ///
    /// The arena is append-only: `delete()` removes a clause from `clause_index`
    /// but leaves its literals in `clause_arena`. Over long proofs this dead
    /// space accumulates. `compact_arena()` rebuilds the arena with only live
    /// clauses and updates `clause_index` entries accordingly.
    ///
    /// Called automatically when arena size exceeds 2x the live data size.
    ///
    /// Compaction is an optimization: if the allocator refuses the new arena,
    /// the old one is kept unchanged. An entry whose range does not lie inside
    /// the arena (never produced by `insert_clause`) is dropped from the index
    /// and recorded as a failure, so no later step can rest on it.
    pub(crate) fn compact_arena(&mut self) {
        let live: usize = self.clause_index.values().map(|e| e.len as usize).sum();
        let mut new_arena: Vec<Literal> = Vec::new();
        if new_arena.try_reserve_exact(live).is_err() {
            return;
        }

        let old_arena = &self.clause_arena;
        let mut dropped = 0u64;
        self.clause_index.retain(|_, entry| {
            let old_start = entry.start as usize;
            let old_end = old_start + entry.len as usize;
            let Some(lits) = old_arena.get(old_start..old_end) else {
                dropped = dropped.saturating_add(1);
                return false;
            };
            let new_start = new_arena.len() as u32;
            new_arena.extend_from_slice(lits);
            entry.start = new_start;
            true
        });

        self.clause_arena = new_arena;
        self.stats.compactions = self.stats.compactions.saturating_add(1);
        if dropped > 0 {
            let _ = writeln!(
                std::io::stderr(),
                "LRAT FAIL: arena compaction dropped {dropped} clause(s) whose range lay outside the arena"
            );
            self.record_failure();
        }
    }

    /// Check whether the arena should be compacted and do so if needed.
    ///
    /// Triggers when arena size exceeds 2x the total live clause literal count.
    pub(super) fn maybe_compact_arena(&mut self) {
        let live_size: usize = self.clause_index.values().map(|e| e.len as usize).sum();
        if self.clause_arena.len() > live_size.saturating_mul(2) && live_size > 0 {
            self.compact_arena();
        }
    }
}
