// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Durable identities belong to original admission, not to an arena rebuild.

use super::*;

pub(in crate::solver) mod counted;

/// Minted only by the exclusive fresh-input session, never by a caller's ID.
/// Only this session's original rows and shared empty-input emission can write
/// its trace. Tautological source rows consume ordinary IDs without a trace row.
pub(crate) struct FreshInputTraceEvent<'a> {
    id: u64,
    prefix: usize,
    previous: Option<u64>,
    kind: FreshEventKind,
    owner: &'a ay_core::original_query::CountedAdmission,
}

pub(crate) enum FreshEventKind {
    Original,
    Empty,
}

impl FreshInputTraceEvent<'_> {
    pub(crate) fn id(&self) -> u64 {
        self.id
    }
    pub(crate) fn prefix(&self) -> usize {
        self.prefix
    }
    pub(crate) fn previous(&self) -> Option<u64> {
        self.previous
    }
    pub(crate) fn is_original(&self) -> bool {
        matches!(self.kind, FreshEventKind::Original)
    }
    pub(crate) fn owner(&self) -> &ay_core::original_query::CountedAdmission {
        self.owner
    }
}

pub(super) enum OriginalLifetime {
    Scoped,
    Global,
}

impl Solver {
    /// Register the exact normalized input before it can be deferred or propagated.
    pub(super) fn register_ledger_original(
        &mut self,
        literals: &[Literal],
        lifetime: OriginalLifetime,
    ) -> u64 {
        let consuming_supported =
            matches!(&lifetime, OriginalLifetime::Scoped) && !literals.is_empty();
        let clause_id = self.register_original_identity(literals, lifetime);
        if self.consuming_trace_pending() {
            self.note_consuming_original(consuming_supported);
            return clause_id;
        }
        if self.cold.lrat_enabled {
            if self.has_live_clause_trace() {
                let units = (literals.len() as u64) * 4 + 16;
                let _ = self.charge_proof_bookkeeping(units);
            }
            if let Some(trace) = self.live_clause_trace_mut() {
                trace.add_clause_with_hint_slices(clause_id, literals, true, &[]);
            }
        } else if let Some(trace) = self.recording_clause_trace_mut() {
            // Literals-only recording after #A2b degradation (no charge).
            if trace.literals_only_recording() {
                trace.add_clause_with_hint_slices(clause_id, literals, true, &[]);
            }
        }
        clause_id
    }

    /// Shared original allocator/ledger kernel. Counted fresh-input use has
    /// reserved every write and prepared its attached trace transaction first.
    fn register_original_identity(
        &mut self,
        literals: &[Literal],
        lifetime: OriginalLifetime,
    ) -> u64 {
        let clause_id = self.allocate_original_clause_id();
        if let Some(checker) = self.cold.forward_checker.as_mut() {
            checker.add_original(literals);
        }
        if let Some(manager) = self.proof_manager.as_mut() {
            manager.register_original_clause(literals);
            if self.cold.lrat_enabled {
                manager.register_clause_id(clause_id);
                manager.retain_ledger_original_id(clause_id);
            }
        }
        match lifetime {
            OriginalLifetime::Global => self
                .cold
                .original_ledger
                .push_clause_global_with_id(literals, clause_id),
            OriginalLifetime::Scoped => self
                .cold
                .original_ledger
                .push_clause_with_id(literals, clause_id),
        }
        clause_id
    }

    /// The DB entry consumes this already registered identity immediately,
    /// before checks/callbacks. It cannot mint or reuse a second input ID.
    pub(super) fn add_registered_original_clause_db(
        &mut self,
        literals: &[Literal],
        clause_id: u64,
    ) -> usize {
        self.cold.registered_original_clause_id = Some(clause_id);
        self.add_clause_db(literals, false)
    }

    /// Authenticate every identity before any ledger row is restored.
    /// Refusal leaves the arena and propagation untouched; callers publish Unknown.
    pub(super) fn preflight_original_ledger_replay(&mut self, start: usize) -> bool {
        if !self.cold.lrat_enabled || self.proof_manager.is_none() {
            return true;
        }
        if self.original_ledger_replay_failed() {
            return false;
        }
        let stop = match ay_core::resource::current_check_stop() {
            Ok(stop) => stop,
            Err(_) => return self.refuse_original_ledger_replay(),
        };
        let Some(length) = self
            .cold
            .original_ledger
            .clause_ids()
            .len()
            .checked_sub(start)
        else {
            return self.refuse_original_ledger_replay();
        };
        if !self.ledger_replay_scan_open(&stop, 0) {
            return false;
        }
        let mut cursor = start;
        let end = start + length;
        while cursor < end {
            let next = cursor + (end - cursor).min(64);
            if !self.ledger_replay_scan_open(&stop, (next - cursor) as u64) {
                return false;
            }
            let ids = &self.cold.original_ledger.clause_ids()[cursor..next];
            if !self
                .proof_manager
                .as_mut()
                .is_some_and(|manager| manager.preflight_ledger_replay(Some(ids)))
            {
                return false;
            }
            cursor = next;
        }
        self.ledger_replay_scan_open(&stop, 0)
    }

    fn ledger_replay_scan_open(
        &mut self,
        stop: &Option<ay_core::resource::CheckStop>,
        work: u64,
    ) -> bool {
        if self.solve_deadline_expired()
            || self.is_interrupted()
            || ay_core::resource::process_cancelled()
            || stop.as_ref().is_some_and(|poll| poll())
            || !self.charge_proof_bookkeeping(work)
        {
            return self.refuse_original_ledger_replay();
        }
        true
    }

    fn refuse_original_ledger_replay(&mut self) -> bool {
        if let Some(manager) = self.proof_manager.as_mut() {
            manager.preflight_ledger_replay(None);
        }
        false
    }

    pub(super) fn original_ledger_replay_failed(&self) -> bool {
        self.proof_manager
            .as_ref()
            .is_some_and(ProofManager::ledger_replay_failed)
    }

    pub(super) fn refresh_ledger_original_retention(&mut self) {
        if let Some(manager) = self.proof_manager.as_mut() {
            manager.refresh_ledger_original_ids(self.cold.original_ledger.clause_ids());
        }
    }
}
