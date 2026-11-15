// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `FarkasLedger` — session-persistent, epoch-tagged record of theory conflicts
//! and eager propagation reasons, and attribution for the interpolation call
//! sites (design §2.9; contract C4; owner WP-4 / D).
//!
//! Rung 1 delivers `record` + `tag` + `partition` and the FALLBACK arm of
//! `attribute` (this epoch's Farkas entries, unfiltered, `attributed: false`,
//! `origins` from `partition`). The exact arm — a FRESH pure-SAT replay over
//! the query CNF ∪ guarded ledger clauses, the legacy activation-core trick —
//! lands in Rung 3 together with its consumers; nothing in Rung 1 calls
//! `attribute` (`HornSmt::farkas_for_last_unsat` is a counting stub).
//!
//! `FarkasConflict.farkas` is non-optional; entries with `farkas: None` feed
//! the replay but are never returned (critique A-sound M10).

use std::collections::VecDeque;

use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::{FarkasAnnotation, TermId, TheoryLit};
use ay_sat::Literal;

use super::{AssertId, HornSmt};
use crate::smt::types::{FarkasConflict, Partition};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum LedgerKind {
    Conflict,
    Propagation,
}

pub(crate) struct LedgerEntry {
    /// Query number.
    pub(crate) epoch: u64,
    pub(crate) kind: LedgerKind,
    /// Conflict literals (`Conflict`) or reason ∪ {¬propagated} (`Propagation`).
    pub(crate) lits: Vec<TheoryLit>,
    /// The exact clause handed to ay-sat.
    pub(crate) clause: Vec<Literal>,
    /// `Conflict` entries only.
    pub(crate) farkas: Option<FarkasAnnotation>,
    pub(crate) at_bcp: bool,
}

pub(crate) struct FarkasLedger {
    /// Session-persistent, FIFO-evicted at `cap`.
    entries: VecDeque<LedgerEntry>,
    /// `Split` for minted B&B atoms; the guard's partition for diseq/expr
    /// splits; else A/B/AB from the owning assertion.
    partition_of: FxHashMap<TermId, Partition>,
    cap: usize,
}

impl FarkasLedger {
    pub(crate) fn new(cap: usize) -> Self {
        Self {
            entries: VecDeque::with_capacity(cap.min(1024)),
            partition_of: FxHashMap::default(),
            cap,
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.entries.len()
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub(crate) fn entries(&self) -> impl Iterator<Item = &LedgerEntry> {
        self.entries.iter()
    }

    /// Cleared on `rebuild()`.
    pub(crate) fn clear(&mut self) {
        self.entries.clear();
        self.partition_of.clear();
    }

    /// Append one entry (FIFO eviction at `cap`).
    pub(crate) fn record(
        &mut self,
        epoch: u64,
        kind: LedgerKind,
        lits: &[TheoryLit],
        clause: &[Literal],
        farkas: Option<FarkasAnnotation>,
        at_bcp: bool,
    ) {
        if self.cap == 0 {
            return;
        }
        while self.entries.len() >= self.cap {
            self.entries.pop_front();
        }
        self.entries.push_back(LedgerEntry {
            epoch,
            kind,
            lits: lits.to_vec(),
            clause: clause.to_vec(),
            farkas,
            at_bcp,
        });
    }

    /// Fix the partition of an atom (first tag wins: a minted atom's partition
    /// is decided at mint time).
    pub(crate) fn tag(&mut self, atom: TermId, p: Partition) {
        self.partition_of.entry(atom).or_insert(p);
    }

    /// Epoch of the newest entry (`None` when empty).
    pub(crate) fn last_epoch(&self) -> Option<u64> {
        self.entries.back().map(|e| e.epoch)
    }

    /// Entries recorded during `epoch`, oldest first.
    pub(crate) fn entries_for_epoch(&self, epoch: u64) -> impl Iterator<Item = &LedgerEntry> {
        self.entries.iter().filter(move |e| e.epoch == epoch)
    }

    /// The tagged partition of `atom`, if any.
    pub(crate) fn tagged(&self, atom: TermId) -> Option<Partition> {
        self.partition_of.get(&atom).copied()
    }

    /// Partition view of `atom` for the `a`/`b` split of the last Unsat: the
    /// tagged partition first (minted atoms are decided at mint time), else
    /// the side of the owning assertion(s) — `A` when only `a` assertions
    /// mention it, `B` when only `b` ones do, `AB` when both do or none does
    /// (the `assumptions.rs` rule: an atom the split cannot place is shared,
    /// which is the conservative choice for interpolation).
    pub(crate) fn partition(
        &self,
        atom: TermId,
        a: &[AssertId],
        b: &[AssertId],
        s: &HornSmt,
    ) -> Partition {
        if let Some(p) = self.tagged(atom) {
            return p;
        }
        let mentions = |ids: &[AssertId]| {
            ids.iter().any(|&id| {
                s.assertions()
                    .get(id.0 as usize)
                    .is_some_and(|assertion| assertion.atoms.contains(&atom))
            })
        };
        match (mentions(a), mentions(b)) {
            (true, false) => Partition::A,
            (false, true) => Partition::B,
            _ => Partition::AB,
        }
    }

    /// Attribution for the LAST Unsat: the attributed Farkas conflicts and
    /// whether the attribution was exact (`true`) or the unfiltered fallback
    /// (`false`).
    ///
    /// Rung 1 implements the FALLBACK arm only: every `Conflict` entry of the
    /// last epoch that carries a Farkas annotation, `origins` from
    /// [`Self::partition`], `attributed = false` (consumers Craig-validate).
    /// The exact arm (fresh pure-SAT replay over the query CNF ∪ guarded
    /// ledger clauses; `Unsat(core)` ⇒ the entries whose guards are in the
    /// core) is Rung 3.
    pub(crate) fn attribute(
        &self,
        s: &HornSmt,
        _active: &[AssertId],
        a: &[AssertId],
        b: &[AssertId],
    ) -> (Vec<FarkasConflict>, bool) {
        let Some(epoch) = self.last_epoch() else {
            return (Vec::new(), false);
        };
        let conflicts = self
            .entries_for_epoch(epoch)
            .filter(|e| e.kind == LedgerKind::Conflict)
            .filter_map(|e| {
                let farkas = e.farkas.clone()?;
                let conflict_terms: Vec<TermId> = e.lits.iter().map(|l| l.term).collect();
                let polarities: Vec<bool> = e.lits.iter().map(|l| l.value).collect();
                let origins = conflict_terms
                    .iter()
                    .map(|&t| self.partition(t, a, b, s))
                    .collect();
                Some(FarkasConflict {
                    conflict_terms,
                    polarities,
                    farkas,
                    origins,
                })
            })
            .collect();
        (conflicts, false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::TermId;

    fn lit(t: u32, v: bool) -> TheoryLit {
        TheoryLit::new(TermId(t), v)
    }

    fn clause(ls: &[i32]) -> Vec<Literal> {
        ls.iter().map(|&d| Literal::from_dimacs(d)).collect()
    }

    #[test]
    fn record_keeps_order_and_evicts_fifo_at_cap() {
        let mut l = FarkasLedger::new(3);
        assert!(l.is_empty());
        for i in 0..5u64 {
            l.record(
                i,
                if i % 2 == 0 {
                    LedgerKind::Conflict
                } else {
                    LedgerKind::Propagation
                },
                &[lit(i as u32, true)],
                &clause(&[-(i as i32 + 1)]),
                None,
                i == 4,
            );
        }
        assert_eq!(l.len(), 3, "cap");
        let epochs: Vec<u64> = l.entries().map(|e| e.epoch).collect();
        assert_eq!(epochs, vec![2, 3, 4], "FIFO eviction keeps the newest");
        assert_eq!(l.last_epoch(), Some(4));
        assert_eq!(l.entries_for_epoch(3).count(), 1);
        assert_eq!(l.entries_for_epoch(0).count(), 0, "evicted");
        let last = l.entries().last().unwrap();
        assert!(last.at_bcp);
        assert_eq!(last.kind, LedgerKind::Conflict);
        assert_eq!(last.clause, clause(&[-5]));
        assert_eq!(last.lits.len(), 1);
    }

    #[test]
    fn zero_cap_records_nothing_and_clear_empties_both_tables() {
        let mut l = FarkasLedger::new(0);
        l.record(
            1,
            LedgerKind::Conflict,
            &[lit(1, true)],
            &clause(&[-1]),
            None,
            false,
        );
        assert!(l.is_empty());
        let mut l = FarkasLedger::new(8);
        l.record(
            1,
            LedgerKind::Conflict,
            &[lit(1, true)],
            &clause(&[-1]),
            None,
            false,
        );
        l.tag(TermId(1), Partition::Split);
        assert_eq!(l.len(), 1);
        assert_eq!(l.tagged(TermId(1)), Some(Partition::Split));
        l.clear();
        assert!(l.is_empty());
        assert_eq!(l.tagged(TermId(1)), None);
        assert_eq!(l.last_epoch(), None);
    }

    #[test]
    fn first_tag_wins() {
        let mut l = FarkasLedger::new(8);
        l.tag(TermId(7), Partition::A);
        l.tag(TermId(7), Partition::B);
        assert_eq!(l.tagged(TermId(7)), Some(Partition::A));
    }
}
