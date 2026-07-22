// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Execution-path ledger for proof-sensitive preprocessing transactions.

use std::collections::VecDeque;
use std::mem::size_of;

const MAX_RETAINED_COMPLETED: usize = 64;
const MODEL_RECONSTRUCTION_WITNESS_MISSING_REASON: &str = "model reconstruction witness missing";
const DECOMPOSE_MODEL_RECONSTRUCTION_WITNESS_MISSING_REASON: &str =
    "decompose model-reconstruction witness missing";
const DECOMPOSE_LRAT_PREFLIGHT_REJECTED_PREFIX: &str = "decompose LRAT preflight rejected:";
const DECOMPOSE_LRAT_CLAMPED_AFTER_DRY_RUN_REASON: &str =
    "decompose LRAT transaction remains clamped after checker-visible dry-run";
const PROOF_OBLIGATION_PENDING_REASON: &str = "proof obligation pending";
const PROOF_OBLIGATION_REJECTED_REASON: &str = "proof obligation rejected";
const ROUTE_ADMISSION_PACKET_INCOMPLETE_REASON: &str = "route admission packet incomplete";
const ROUTE_ADMISSION_PACKET_REJECTED_REASON: &str = "route admission packet rejected";
const ROUTE_ADMISSION_PACKET_MISSING_EXTERNAL_CHECKER_VERDICT_REASON: &str =
    "route admission packet missing external checker verdict artifact";
const ROUTE_ADMISSION_PACKET_MISSING_ORIGINAL_CLAUSE_AUTHORITY_REASON: &str =
    "route admission packet missing original clause authority";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct PreprocessTransactionId(u64);

impl PreprocessTransactionId {
    #[inline]
    pub(crate) const fn as_u64(self) -> u64 {
        self.0
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PreprocessPass {
    Decompose,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ProofObligationStatus {
    NotRequired,
    Pending,
    Satisfied,
    Rejected,
}

impl ProofObligationStatus {
    fn is_ready(self) -> bool {
        matches!(self, Self::NotRequired | Self::Satisfied)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ModelReconstructionWitnessStatus {
    NotApplicable,
    Present,
    Missing,
}

#[cfg_attr(not(test), allow(dead_code))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RouteAdmissionPacketKind {
    None,
    FmlaEquivChainMainLrat,
}

#[cfg_attr(not(test), allow(dead_code))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RouteAdmissionPacketStatus {
    NotAttempted,
    Incomplete,
    Rejected,
    Complete,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct RouteAdmissionPacket {
    pub kind: RouteAdmissionPacketKind,
    pub status: RouteAdmissionPacketStatus,
    pub original_dimacs_rows: u64,
    pub original_clause_authority_rows: u64,
    pub proof_obligation_rows: u64,
    pub model_reconstruction_rows: u64,
    pub external_proof_checker_verdict_artifact_rows: u64,
}

impl Default for RouteAdmissionPacket {
    fn default() -> Self {
        Self {
            kind: RouteAdmissionPacketKind::None,
            status: RouteAdmissionPacketStatus::NotAttempted,
            original_dimacs_rows: 0,
            original_clause_authority_rows: 0,
            proof_obligation_rows: 0,
            model_reconstruction_rows: 0,
            external_proof_checker_verdict_artifact_rows: 0,
        }
    }
}

impl RouteAdmissionPacket {
    fn commit_reject_reason(self) -> Option<&'static str> {
        match self.status {
            RouteAdmissionPacketStatus::NotAttempted => None,
            RouteAdmissionPacketStatus::Complete => {
                if self.kind == RouteAdmissionPacketKind::FmlaEquivChainMainLrat
                    && self.proof_obligation_rows > 0
                    && self.original_clause_authority_rows != self.proof_obligation_rows
                {
                    Some(ROUTE_ADMISSION_PACKET_MISSING_ORIGINAL_CLAUSE_AUTHORITY_REASON)
                } else if self.kind == RouteAdmissionPacketKind::FmlaEquivChainMainLrat
                    && self.proof_obligation_rows > 0
                    && self.external_proof_checker_verdict_artifact_rows
                        != self.proof_obligation_rows
                {
                    Some(ROUTE_ADMISSION_PACKET_MISSING_EXTERNAL_CHECKER_VERDICT_REASON)
                } else {
                    None
                }
            }
            RouteAdmissionPacketStatus::Incomplete => {
                Some(ROUTE_ADMISSION_PACKET_INCOMPLETE_REASON)
            }
            RouteAdmissionPacketStatus::Rejected => Some(ROUTE_ADMISSION_PACKET_REJECTED_REASON),
        }
    }

    fn external_checker_verified(self) -> bool {
        self.status == RouteAdmissionPacketStatus::Complete
            && self.proof_obligation_rows > 0
            && self.external_proof_checker_verdict_artifact_rows == self.proof_obligation_rows
    }
}

#[cfg_attr(not(test), allow(dead_code))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PreprocessTransactionOutcome {
    Active,
    Committed,
    RolledBack,
    FailClosed,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PlannedSubstitution {
    pub variable: usize,
    pub literal_dimacs: i32,
    pub representative_variable: usize,
    pub representative_dimacs: i32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PreprocessTransactionDraft {
    pub mutation_epoch: u64,
    pub pass_name: PreprocessPass,
    pub touched_variables: Vec<usize>,
    pub eliminated_variables: Vec<usize>,
    pub equivalent_variables: Vec<(usize, usize)>,
    pub planned_substitutions: Vec<PlannedSubstitution>,
    pub proof_obligation: ProofObligationStatus,
    pub model_reconstruction_witness: ModelReconstructionWitnessStatus,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PreprocessTransactionRecord {
    pub id: PreprocessTransactionId,
    pub mutation_epoch: u64,
    pub pass_name: PreprocessPass,
    pub touched_variables: Vec<usize>,
    pub eliminated_variables: Vec<usize>,
    pub equivalent_variables: Vec<(usize, usize)>,
    pub planned_substitutions: Vec<PlannedSubstitution>,
    pub proof_obligation: ProofObligationStatus,
    pub model_reconstruction_witness: ModelReconstructionWitnessStatus,
    pub route_admission_packet: RouteAdmissionPacket,
    pub outcome: PreprocessTransactionOutcome,
    pub rollback_reason: Option<String>,
    pub fail_closed_reason: Option<String>,
}

#[cfg_attr(not(test), allow(dead_code))]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PreprocessLedgerObserverEventKind {
    TransactionFinalized,
}

#[cfg_attr(not(test), allow(dead_code))]
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct PreprocessLedgerObserverEvent {
    pub kind: PreprocessLedgerObserverEventKind,
    pub transaction_id: u64,
    pub mutation_epoch: u64,
    pub pass_name: PreprocessPass,
    pub outcome: PreprocessTransactionOutcome,
    pub proof_obligation: ProofObligationStatus,
    pub model_reconstruction_witness: ModelReconstructionWitnessStatus,
    pub touched_variables: u64,
    pub eliminated_variables: u64,
    pub equivalent_variables: u64,
    pub planned_substitutions: u64,
    pub rollback_reason: Option<String>,
    pub fail_closed_reason: Option<String>,
    pub proof_obligation_ready: bool,
    pub external_checker_verified: bool,
}

/// Execution-path preprocessing transaction counters.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PreprocessTransactionStats {
    /// Transactions begun by preprocessing passes.
    pub started: u64,
    /// Transactions that committed a destructive preprocessing mutation.
    pub committed: u64,
    /// Transactions rolled back before mutation.
    pub rolled_back: u64,
    /// Transactions rejected fail-closed before mutation.
    pub fail_closed: u64,
    /// Finalized transactions whose proof obligation was not required.
    pub proof_obligation_not_required: u64,
    /// Finalized transactions whose proof obligation was satisfied.
    pub proof_obligation_satisfied: u64,
    /// Finalized transactions whose proof obligation was rejected.
    pub proof_obligation_rejected: u64,
    /// Finalized transactions whose proof obligation remained pending.
    pub proof_obligation_pending: u64,
    /// Finalized transactions with no model-reconstruction witness requirement.
    pub reconstruction_witness_not_applicable: u64,
    /// Finalized transactions with a present model-reconstruction witness.
    pub reconstruction_witness_present: u64,
    /// Finalized transactions missing a required model-reconstruction witness.
    pub reconstruction_witness_missing: u64,
    /// Total touched variables recorded by finalized transactions.
    pub touched_variables_total: u64,
    /// Total eliminated variables recorded by finalized transactions.
    pub eliminated_variables_total: u64,
    /// Total equivalent-variable pairs recorded by finalized transactions.
    pub equivalent_variables_total: u64,
    /// Total planned substitutions recorded by finalized transactions.
    pub planned_substitutions_total: u64,
    /// Maximum mutation epoch observed among begun transactions.
    pub max_mutation_epoch: u64,
    /// Transactions currently active in the ledger.
    pub active_transactions: u64,
    /// Completed transaction records retained for diagnostics.
    pub retained_completed: u64,
    /// Fail-closed transactions caused by a missing model-reconstruction witness.
    pub fail_closed_model_reconstruction_witness_missing: u64,
    /// Fail-closed transactions caused by a rejected decompose LRAT preflight.
    pub fail_closed_decompose_lrat_preflight_rejected: u64,
    /// Fail-closed decompose LRAT transactions clamped after checker-visible dry-run.
    pub fail_closed_decompose_lrat_clamped_after_dry_run: u64,
    /// Fail-closed transactions without a classified reason bucket.
    pub fail_closed_other: u64,
    /// Rolled-back transactions without a classified reason bucket.
    pub rolled_back_other: u64,
    /// Default-off observer events materialized for finalized transactions.
    pub observer_events_materialized: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum PreprocessTransactionCommitError {
    MissingTransaction,
    MissingModelReconstructionWitness,
    PendingProofObligation,
    RejectedProofObligation,
    RouteAdmissionPacketNotReady,
}

#[derive(Debug, Default)]
pub(crate) struct PreprocessTransactionLedger {
    next_id: u64,
    active: Vec<PreprocessTransactionRecord>,
    completed: VecDeque<PreprocessTransactionRecord>,
    stats: PreprocessTransactionStats,
    observer_events_enabled: bool,
    observer_events: Vec<PreprocessLedgerObserverEvent>,
}

#[cfg_attr(not(test), allow(dead_code))]
impl PreprocessTransactionLedger {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn begin(&mut self, draft: PreprocessTransactionDraft) -> PreprocessTransactionId {
        let id = PreprocessTransactionId(self.next_id);
        self.next_id = self.next_id.saturating_add(1);
        self.stats.started = self.stats.started.saturating_add(1);
        self.stats.max_mutation_epoch = self.stats.max_mutation_epoch.max(draft.mutation_epoch);
        self.active.push(PreprocessTransactionRecord {
            id,
            mutation_epoch: draft.mutation_epoch,
            pass_name: draft.pass_name,
            touched_variables: draft.touched_variables,
            eliminated_variables: draft.eliminated_variables,
            equivalent_variables: draft.equivalent_variables,
            planned_substitutions: draft.planned_substitutions,
            proof_obligation: draft.proof_obligation,
            model_reconstruction_witness: draft.model_reconstruction_witness,
            route_admission_packet: RouteAdmissionPacket::default(),
            outcome: PreprocessTransactionOutcome::Active,
            rollback_reason: None,
            fail_closed_reason: None,
        });
        id
    }

    pub(crate) fn set_proof_obligation(
        &mut self,
        id: PreprocessTransactionId,
        status: ProofObligationStatus,
    ) -> bool {
        let Some(record) = self.active_record_mut(id) else {
            return false;
        };
        record.proof_obligation = status;
        true
    }

    pub(crate) fn set_model_reconstruction_witness(
        &mut self,
        id: PreprocessTransactionId,
        status: ModelReconstructionWitnessStatus,
    ) -> bool {
        let Some(record) = self.active_record_mut(id) else {
            return false;
        };
        record.model_reconstruction_witness = status;
        true
    }

    pub(crate) fn set_route_admission_packet(
        &mut self,
        id: PreprocessTransactionId,
        packet: RouteAdmissionPacket,
    ) -> bool {
        let Some(record) = self.active_record_mut(id) else {
            return false;
        };
        record.route_admission_packet = packet;
        true
    }

    pub(crate) fn route_admission_packet(
        &self,
        id: PreprocessTransactionId,
    ) -> Option<RouteAdmissionPacket> {
        self.active_record(id)
            .map(|record| record.route_admission_packet)
    }

    pub(crate) fn commit(
        &mut self,
        id: PreprocessTransactionId,
    ) -> Result<(), PreprocessTransactionCommitError> {
        let Some(record) = self.active_record(id) else {
            return Err(PreprocessTransactionCommitError::MissingTransaction);
        };
        let requires_reconstruction_witness = record.requires_reconstruction_witness();
        let model_reconstruction_witness = record.model_reconstruction_witness;
        let proof_obligation = record.proof_obligation;
        let route_admission_packet = record.route_admission_packet;
        if requires_reconstruction_witness
            && model_reconstruction_witness != ModelReconstructionWitnessStatus::Present
        {
            self.fail_closed(id, MODEL_RECONSTRUCTION_WITNESS_MISSING_REASON);
            return Err(PreprocessTransactionCommitError::MissingModelReconstructionWitness);
        }
        match proof_obligation {
            ProofObligationStatus::NotRequired | ProofObligationStatus::Satisfied => {}
            ProofObligationStatus::Pending => {
                self.fail_closed(id, PROOF_OBLIGATION_PENDING_REASON);
                return Err(PreprocessTransactionCommitError::PendingProofObligation);
            }
            ProofObligationStatus::Rejected => {
                self.fail_closed(id, PROOF_OBLIGATION_REJECTED_REASON);
                return Err(PreprocessTransactionCommitError::RejectedProofObligation);
            }
        }
        if let Some(reason) = route_admission_packet.commit_reject_reason() {
            self.fail_closed(id, reason);
            return Err(PreprocessTransactionCommitError::RouteAdmissionPacketNotReady);
        }
        self.finalize(id, PreprocessTransactionOutcome::Committed, None, None);
        Ok(())
    }

    pub(crate) fn rollback(&mut self, id: PreprocessTransactionId, reason: impl Into<String>) {
        self.finalize(
            id,
            PreprocessTransactionOutcome::RolledBack,
            Some(reason.into()),
            None,
        );
    }

    pub(crate) fn fail_closed(&mut self, id: PreprocessTransactionId, reason: impl Into<String>) {
        self.finalize(
            id,
            PreprocessTransactionOutcome::FailClosed,
            None,
            Some(reason.into()),
        );
    }

    pub(crate) fn stats(&self) -> PreprocessTransactionStats {
        let mut stats = self.stats;
        stats.active_transactions = self.active.len() as u64;
        stats.retained_completed = self.completed.len() as u64;
        stats
    }

    pub(crate) fn last_completed(&self) -> Option<&PreprocessTransactionRecord> {
        self.completed.back()
    }

    pub(crate) fn set_observer_events_enabled(&mut self, enabled: bool) {
        self.observer_events_enabled = enabled;
    }

    pub(crate) fn observer_events(&self) -> &[PreprocessLedgerObserverEvent] {
        &self.observer_events
    }

    pub(crate) fn heap_bytes(&self) -> usize {
        let mut bytes = self.active.capacity() * size_of::<PreprocessTransactionRecord>()
            + self.completed.capacity() * size_of::<PreprocessTransactionRecord>()
            + self.observer_events.capacity() * size_of::<PreprocessLedgerObserverEvent>();
        for record in self.active.iter().chain(self.completed.iter()) {
            bytes += record.touched_variables.capacity() * size_of::<usize>();
            bytes += record.eliminated_variables.capacity() * size_of::<usize>();
            bytes += record.equivalent_variables.capacity() * size_of::<(usize, usize)>();
            bytes += record.planned_substitutions.capacity() * size_of::<PlannedSubstitution>();
            if let Some(reason) = &record.rollback_reason {
                bytes += reason.capacity();
            }
            if let Some(reason) = &record.fail_closed_reason {
                bytes += reason.capacity();
            }
        }
        for event in &self.observer_events {
            if let Some(reason) = &event.rollback_reason {
                bytes += reason.capacity();
            }
            if let Some(reason) = &event.fail_closed_reason {
                bytes += reason.capacity();
            }
        }
        bytes
    }

    fn active_record(&self, id: PreprocessTransactionId) -> Option<&PreprocessTransactionRecord> {
        self.active.iter().find(|record| record.id == id)
    }

    fn active_record_mut(
        &mut self,
        id: PreprocessTransactionId,
    ) -> Option<&mut PreprocessTransactionRecord> {
        self.active.iter_mut().find(|record| record.id == id)
    }

    fn finalize(
        &mut self,
        id: PreprocessTransactionId,
        outcome: PreprocessTransactionOutcome,
        rollback_reason: Option<String>,
        fail_closed_reason: Option<String>,
    ) {
        let Some(pos) = self.active.iter().position(|record| record.id == id) else {
            return;
        };
        let mut record = self.active.swap_remove(pos);
        record.outcome = outcome;
        record.rollback_reason = rollback_reason;
        record.fail_closed_reason = fail_closed_reason;
        self.observe_finalized(&record);
        self.observe_finalized_event(&record);
        self.completed.push_back(record);
        while self.completed.len() > MAX_RETAINED_COMPLETED {
            self.completed.pop_front();
        }
    }

    fn observe_finalized(&mut self, record: &PreprocessTransactionRecord) {
        match record.outcome {
            PreprocessTransactionOutcome::Active => {}
            PreprocessTransactionOutcome::Committed => {
                self.stats.committed = self.stats.committed.saturating_add(1);
            }
            PreprocessTransactionOutcome::RolledBack => {
                self.stats.rolled_back = self.stats.rolled_back.saturating_add(1);
            }
            PreprocessTransactionOutcome::FailClosed => {
                self.stats.fail_closed = self.stats.fail_closed.saturating_add(1);
            }
        }
        match record.proof_obligation {
            ProofObligationStatus::NotRequired => {
                self.stats.proof_obligation_not_required =
                    self.stats.proof_obligation_not_required.saturating_add(1);
            }
            ProofObligationStatus::Pending => {
                self.stats.proof_obligation_pending =
                    self.stats.proof_obligation_pending.saturating_add(1);
            }
            ProofObligationStatus::Satisfied => {
                self.stats.proof_obligation_satisfied =
                    self.stats.proof_obligation_satisfied.saturating_add(1);
            }
            ProofObligationStatus::Rejected => {
                self.stats.proof_obligation_rejected =
                    self.stats.proof_obligation_rejected.saturating_add(1);
            }
        }
        match record.model_reconstruction_witness {
            ModelReconstructionWitnessStatus::NotApplicable => {
                self.stats.reconstruction_witness_not_applicable = self
                    .stats
                    .reconstruction_witness_not_applicable
                    .saturating_add(1);
            }
            ModelReconstructionWitnessStatus::Present => {
                self.stats.reconstruction_witness_present =
                    self.stats.reconstruction_witness_present.saturating_add(1);
            }
            ModelReconstructionWitnessStatus::Missing => {
                self.stats.reconstruction_witness_missing =
                    self.stats.reconstruction_witness_missing.saturating_add(1);
            }
        }
        self.stats.touched_variables_total = self
            .stats
            .touched_variables_total
            .saturating_add(record.touched_variables.len() as u64);
        self.stats.eliminated_variables_total = self
            .stats
            .eliminated_variables_total
            .saturating_add(record.eliminated_variables.len() as u64);
        self.stats.equivalent_variables_total = self
            .stats
            .equivalent_variables_total
            .saturating_add(record.equivalent_variables.len() as u64);
        self.stats.planned_substitutions_total = self
            .stats
            .planned_substitutions_total
            .saturating_add(record.planned_substitutions.len() as u64);
        self.observe_reject_reason(record);
    }

    fn observe_reject_reason(&mut self, record: &PreprocessTransactionRecord) {
        match record.outcome {
            PreprocessTransactionOutcome::RolledBack => {
                self.stats.rolled_back_other = self.stats.rolled_back_other.saturating_add(1);
            }
            PreprocessTransactionOutcome::FailClosed => {
                let reason = record.fail_closed_reason.as_deref().unwrap_or_default();
                if reason == MODEL_RECONSTRUCTION_WITNESS_MISSING_REASON
                    || reason == DECOMPOSE_MODEL_RECONSTRUCTION_WITNESS_MISSING_REASON
                {
                    self.stats.fail_closed_model_reconstruction_witness_missing = self
                        .stats
                        .fail_closed_model_reconstruction_witness_missing
                        .saturating_add(1);
                } else if reason.starts_with(DECOMPOSE_LRAT_PREFLIGHT_REJECTED_PREFIX) {
                    self.stats.fail_closed_decompose_lrat_preflight_rejected = self
                        .stats
                        .fail_closed_decompose_lrat_preflight_rejected
                        .saturating_add(1);
                } else if reason == DECOMPOSE_LRAT_CLAMPED_AFTER_DRY_RUN_REASON {
                    self.stats.fail_closed_decompose_lrat_clamped_after_dry_run = self
                        .stats
                        .fail_closed_decompose_lrat_clamped_after_dry_run
                        .saturating_add(1);
                } else {
                    self.stats.fail_closed_other = self.stats.fail_closed_other.saturating_add(1);
                }
            }
            PreprocessTransactionOutcome::Active | PreprocessTransactionOutcome::Committed => {}
        }
    }

    fn observe_finalized_event(&mut self, record: &PreprocessTransactionRecord) {
        if !self.observer_events_enabled {
            return;
        }
        self.observer_events
            .push(PreprocessLedgerObserverEvent::finalized(record));
        self.stats.observer_events_materialized =
            self.stats.observer_events_materialized.saturating_add(1);
        if self.observer_events.len() > MAX_RETAINED_COMPLETED {
            let drop_count = self.observer_events.len() - MAX_RETAINED_COMPLETED;
            self.observer_events.drain(0..drop_count);
        }
    }
}

impl PreprocessTransactionRecord {
    fn requires_reconstruction_witness(&self) -> bool {
        !self.eliminated_variables.is_empty() || !self.planned_substitutions.is_empty()
    }
}

impl PreprocessLedgerObserverEvent {
    fn finalized(record: &PreprocessTransactionRecord) -> Self {
        Self {
            kind: PreprocessLedgerObserverEventKind::TransactionFinalized,
            transaction_id: record.id.as_u64(),
            mutation_epoch: record.mutation_epoch,
            pass_name: record.pass_name,
            outcome: record.outcome,
            proof_obligation: record.proof_obligation,
            model_reconstruction_witness: record.model_reconstruction_witness,
            touched_variables: record.touched_variables.len() as u64,
            eliminated_variables: record.eliminated_variables.len() as u64,
            equivalent_variables: record.equivalent_variables.len() as u64,
            planned_substitutions: record.planned_substitutions.len() as u64,
            rollback_reason: record.rollback_reason.clone(),
            fail_closed_reason: record.fail_closed_reason.clone(),
            proof_obligation_ready: record.proof_obligation.is_ready(),
            external_checker_verified: record.route_admission_packet.external_checker_verified(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn draft() -> PreprocessTransactionDraft {
        PreprocessTransactionDraft {
            mutation_epoch: 7,
            pass_name: PreprocessPass::Decompose,
            touched_variables: vec![0, 1],
            eliminated_variables: Vec::new(),
            equivalent_variables: vec![(1, 0)],
            planned_substitutions: vec![PlannedSubstitution {
                variable: 1,
                literal_dimacs: 2,
                representative_variable: 0,
                representative_dimacs: 1,
            }],
            proof_obligation: ProofObligationStatus::Satisfied,
            model_reconstruction_witness: ModelReconstructionWitnessStatus::Present,
        }
    }

    #[test]
    fn test_preprocess_transaction_ledger_commit_records_transaction() {
        let mut ledger = PreprocessTransactionLedger::new();
        let id = ledger.begin(draft());

        ledger.commit(id).expect("commit should accept witness");

        let stats = ledger.stats();
        assert_eq!(stats.started, 1);
        assert_eq!(stats.committed, 1);
        assert_eq!(stats.fail_closed, 0);
        assert_eq!(stats.proof_obligation_satisfied, 1);
        assert_eq!(stats.reconstruction_witness_present, 1);
        assert_eq!(stats.planned_substitutions_total, 1);
        assert_eq!(stats.max_mutation_epoch, 7);

        let record = ledger.last_completed().expect("committed record retained");
        assert_eq!(record.outcome, PreprocessTransactionOutcome::Committed);
        assert_eq!(record.touched_variables, vec![0, 1]);
        assert_eq!(record.planned_substitutions[0].representative_dimacs, 1);
        assert_eq!(
            record.route_admission_packet,
            RouteAdmissionPacket::default()
        );
        assert_eq!(stats.observer_events_materialized, 0);
        assert!(ledger.observer_events().is_empty());
    }

    #[test]
    fn test_preprocess_transaction_ledger_rollback_records_reason() {
        let mut ledger = PreprocessTransactionLedger::new();
        let id = ledger.begin(PreprocessTransactionDraft {
            model_reconstruction_witness: ModelReconstructionWitnessStatus::NotApplicable,
            planned_substitutions: Vec::new(),
            proof_obligation: ProofObligationStatus::Pending,
            ..draft()
        });

        ledger.rollback(id, "unit-test rollback");

        let stats = ledger.stats();
        assert_eq!(stats.started, 1);
        assert_eq!(stats.rolled_back, 1);
        assert_eq!(stats.proof_obligation_pending, 1);
        assert_eq!(stats.reconstruction_witness_not_applicable, 1);
        assert_eq!(stats.rolled_back_other, 1);
        let record = ledger.last_completed().expect("rollback record retained");
        assert_eq!(record.outcome, PreprocessTransactionOutcome::RolledBack);
        assert_eq!(
            record.rollback_reason.as_deref(),
            Some("unit-test rollback")
        );
    }

    #[test]
    fn test_preprocess_transaction_ledger_commit_without_witness_fails_closed() {
        let mut ledger = PreprocessTransactionLedger::new();
        let id = ledger.begin(PreprocessTransactionDraft {
            model_reconstruction_witness: ModelReconstructionWitnessStatus::Missing,
            proof_obligation: ProofObligationStatus::Rejected,
            ..draft()
        });

        let err = ledger
            .commit(id)
            .expect_err("destructive commit without witness must fail closed");

        assert_eq!(
            err,
            PreprocessTransactionCommitError::MissingModelReconstructionWitness
        );
        let stats = ledger.stats();
        assert_eq!(stats.started, 1);
        assert_eq!(stats.committed, 0);
        assert_eq!(stats.fail_closed, 1);
        assert_eq!(stats.proof_obligation_rejected, 1);
        assert_eq!(stats.reconstruction_witness_missing, 1);
        assert_eq!(stats.fail_closed_model_reconstruction_witness_missing, 1);
        let record = ledger
            .last_completed()
            .expect("fail-closed record retained");
        assert_eq!(record.outcome, PreprocessTransactionOutcome::FailClosed);
        assert_eq!(
            record.fail_closed_reason.as_deref(),
            Some("model reconstruction witness missing")
        );
        assert_eq!(stats.observer_events_materialized, 0);
        assert!(ledger.observer_events().is_empty());
    }

    #[test]
    fn test_preprocess_transaction_observer_materializes_finalized_event_when_enabled() {
        let mut ledger = PreprocessTransactionLedger::new();
        ledger.set_observer_events_enabled(true);
        let id = ledger.begin(PreprocessTransactionDraft {
            model_reconstruction_witness: ModelReconstructionWitnessStatus::Missing,
            proof_obligation: ProofObligationStatus::Rejected,
            ..draft()
        });

        let err = ledger
            .commit(id)
            .expect_err("destructive commit without witness must fail closed");

        assert_eq!(
            err,
            PreprocessTransactionCommitError::MissingModelReconstructionWitness
        );
        let stats = ledger.stats();
        assert_eq!(stats.committed, 0);
        assert_eq!(stats.fail_closed, 1);
        assert_eq!(stats.observer_events_materialized, 1);
        let events = ledger.observer_events();
        assert_eq!(events.len(), 1);
        let event = &events[0];
        assert_eq!(
            event.kind,
            PreprocessLedgerObserverEventKind::TransactionFinalized
        );
        assert_eq!(event.transaction_id, id.as_u64());
        assert_eq!(event.mutation_epoch, 7);
        assert_eq!(event.pass_name, PreprocessPass::Decompose);
        assert_eq!(event.outcome, PreprocessTransactionOutcome::FailClosed);
        assert_eq!(event.proof_obligation, ProofObligationStatus::Rejected);
        assert_eq!(
            event.model_reconstruction_witness,
            ModelReconstructionWitnessStatus::Missing
        );
        assert_eq!(event.touched_variables, 2);
        assert_eq!(event.eliminated_variables, 0);
        assert_eq!(event.equivalent_variables, 1);
        assert_eq!(event.planned_substitutions, 1);
        assert!(event.rollback_reason.is_none());
        assert_eq!(
            event.fail_closed_reason.as_deref(),
            Some("model reconstruction witness missing")
        );
        assert!(!event.proof_obligation_ready);
        assert!(!event.external_checker_verified);
    }

    #[test]
    fn test_preprocess_transaction_observer_derives_proof_obligation_readiness() {
        for (proof_obligation, expected_ready) in [
            (ProofObligationStatus::NotRequired, true),
            (ProofObligationStatus::Satisfied, true),
            (ProofObligationStatus::Pending, false),
            (ProofObligationStatus::Rejected, false),
        ] {
            let mut ledger = PreprocessTransactionLedger::new();
            ledger.set_observer_events_enabled(true);
            let id = ledger.begin(PreprocessTransactionDraft {
                proof_obligation,
                ..draft()
            });

            let result = ledger.commit(id);
            assert_eq!(
                result.is_ok(),
                expected_ready,
                "unexpected commit result for {proof_obligation:?}: {result:?}"
            );

            let event = ledger
                .observer_events()
                .last()
                .expect("observer event should be retained");
            assert_eq!(event.proof_obligation, proof_obligation);
            assert_eq!(
                event.proof_obligation_ready, expected_ready,
                "observer proof readiness should derive from finalized proof obligation"
            );
            assert!(!event.external_checker_verified);
        }
    }

    #[test]
    fn test_preprocess_transaction_observer_derives_external_checker_verification() {
        for (label, packet, expect_commit_ok, expected_external_checker_verified) in [
            (
                "complete-matching-proof-rows",
                RouteAdmissionPacket {
                    kind: RouteAdmissionPacketKind::FmlaEquivChainMainLrat,
                    status: RouteAdmissionPacketStatus::Complete,
                    original_dimacs_rows: 31,
                    original_clause_authority_rows: 7,
                    proof_obligation_rows: 7,
                    model_reconstruction_rows: 3,
                    external_proof_checker_verdict_artifact_rows: 7,
                },
                true,
                true,
            ),
            (
                "complete-without-proof-rows",
                RouteAdmissionPacket {
                    kind: RouteAdmissionPacketKind::FmlaEquivChainMainLrat,
                    status: RouteAdmissionPacketStatus::Complete,
                    original_dimacs_rows: 31,
                    original_clause_authority_rows: 0,
                    proof_obligation_rows: 0,
                    model_reconstruction_rows: 3,
                    external_proof_checker_verdict_artifact_rows: 0,
                },
                true,
                false,
            ),
            (
                "complete-missing-verdict-rows",
                RouteAdmissionPacket {
                    kind: RouteAdmissionPacketKind::FmlaEquivChainMainLrat,
                    status: RouteAdmissionPacketStatus::Complete,
                    original_dimacs_rows: 31,
                    original_clause_authority_rows: 7,
                    proof_obligation_rows: 7,
                    model_reconstruction_rows: 3,
                    external_proof_checker_verdict_artifact_rows: 3,
                },
                false,
                false,
            ),
            (
                "incomplete-matching-rows",
                RouteAdmissionPacket {
                    kind: RouteAdmissionPacketKind::FmlaEquivChainMainLrat,
                    status: RouteAdmissionPacketStatus::Incomplete,
                    original_dimacs_rows: 31,
                    original_clause_authority_rows: 7,
                    proof_obligation_rows: 7,
                    model_reconstruction_rows: 3,
                    external_proof_checker_verdict_artifact_rows: 7,
                },
                false,
                false,
            ),
        ] {
            let mut ledger = PreprocessTransactionLedger::new();
            ledger.set_observer_events_enabled(true);
            let id = ledger.begin(draft());
            assert!(ledger.set_route_admission_packet(id, packet));

            let result = ledger.commit(id);
            assert_eq!(
                result.is_ok(),
                expect_commit_ok,
                "{label} unexpected commit result: {result:?}"
            );

            let event = ledger
                .observer_events()
                .last()
                .expect("observer event should be retained");
            assert!(event.proof_obligation_ready, "{label}");
            assert_eq!(
                event.external_checker_verified, expected_external_checker_verified,
                "{label}"
            );
        }
    }

    #[test]
    fn test_preprocess_transaction_ledger_commit_without_proof_obligation_fails_closed() {
        for (proof_obligation, expected_error, expected_reason) in [
            (
                ProofObligationStatus::Pending,
                PreprocessTransactionCommitError::PendingProofObligation,
                "proof obligation pending",
            ),
            (
                ProofObligationStatus::Rejected,
                PreprocessTransactionCommitError::RejectedProofObligation,
                "proof obligation rejected",
            ),
        ] {
            let mut ledger = PreprocessTransactionLedger::new();
            let id = ledger.begin(PreprocessTransactionDraft {
                proof_obligation,
                model_reconstruction_witness: ModelReconstructionWitnessStatus::Present,
                ..draft()
            });

            let err = ledger
                .commit(id)
                .expect_err("destructive commit without proof obligation must fail closed");

            assert_eq!(err, expected_error);
            let stats = ledger.stats();
            assert_eq!(stats.started, 1);
            assert_eq!(stats.committed, 0);
            assert_eq!(stats.fail_closed, 1);
            assert_eq!(stats.reconstruction_witness_present, 1);
            match proof_obligation {
                ProofObligationStatus::Pending => assert_eq!(stats.proof_obligation_pending, 1),
                ProofObligationStatus::Rejected => assert_eq!(stats.proof_obligation_rejected, 1),
                _ => unreachable!("test only covers unsatisfied proof obligations"),
            }
            let record = ledger
                .last_completed()
                .expect("proof-obligation fail-closed record retained");
            assert_eq!(record.outcome, PreprocessTransactionOutcome::FailClosed);
            assert_eq!(record.fail_closed_reason.as_deref(), Some(expected_reason));
        }
    }

    #[test]
    fn test_preprocess_transaction_route_admission_packet_is_inert_and_readable() {
        let mut ledger = PreprocessTransactionLedger::new();
        let id = ledger.begin(draft());
        let packet = RouteAdmissionPacket {
            kind: RouteAdmissionPacketKind::FmlaEquivChainMainLrat,
            status: RouteAdmissionPacketStatus::Complete,
            original_dimacs_rows: 31,
            original_clause_authority_rows: 7,
            proof_obligation_rows: 7,
            model_reconstruction_rows: 3,
            external_proof_checker_verdict_artifact_rows: 7,
        };

        assert_eq!(
            ledger.route_admission_packet(id),
            Some(RouteAdmissionPacket::default())
        );
        assert!(!ledger.set_route_admission_packet(PreprocessTransactionId(99), packet));
        assert_eq!(
            ledger.route_admission_packet(PreprocessTransactionId(99)),
            None
        );
        assert!(ledger.set_route_admission_packet(id, packet));
        assert_eq!(ledger.route_admission_packet(id), Some(packet));

        ledger
            .commit(id)
            .expect("complete packet must not change commit semantics");

        let stats = ledger.stats();
        assert_eq!(stats.started, 1);
        assert_eq!(stats.committed, 1);
        assert_eq!(stats.fail_closed, 0);
        let record = ledger.last_completed().expect("committed record retained");
        assert_eq!(record.route_admission_packet, packet);
    }

    #[test]
    fn test_preprocess_transaction_route_admission_packet_fails_closed_when_not_ready() {
        for (status, expected_reason) in [
            (
                RouteAdmissionPacketStatus::Incomplete,
                ROUTE_ADMISSION_PACKET_INCOMPLETE_REASON,
            ),
            (
                RouteAdmissionPacketStatus::Rejected,
                ROUTE_ADMISSION_PACKET_REJECTED_REASON,
            ),
        ] {
            let mut ledger = PreprocessTransactionLedger::new();
            let id = ledger.begin(draft());
            assert!(ledger.set_route_admission_packet(
                id,
                RouteAdmissionPacket {
                    kind: RouteAdmissionPacketKind::FmlaEquivChainMainLrat,
                    status,
                    original_dimacs_rows: 31,
                    original_clause_authority_rows: 0,
                    proof_obligation_rows: 0,
                    model_reconstruction_rows: 0,
                    external_proof_checker_verdict_artifact_rows: 0,
                },
            ));

            let err = ledger
                .commit(id)
                .expect_err("not-ready route packet must fail closed");

            assert_eq!(
                err,
                PreprocessTransactionCommitError::RouteAdmissionPacketNotReady
            );
            let stats = ledger.stats();
            assert_eq!(stats.started, 1);
            assert_eq!(stats.committed, 0);
            assert_eq!(stats.fail_closed, 1);
            assert_eq!(stats.fail_closed_other, 1);
            let record = ledger
                .last_completed()
                .expect("route-admission fail-closed record retained");
            assert_eq!(record.outcome, PreprocessTransactionOutcome::FailClosed);
            assert_eq!(record.route_admission_packet.status, status);
            assert_eq!(record.fail_closed_reason.as_deref(), Some(expected_reason));
        }
    }

    #[test]
    fn test_preprocess_transaction_route_admission_packet_fails_closed_without_checker_verdict_artifact(
    ) {
        for artifact_rows in [0, 3] {
            let mut ledger = PreprocessTransactionLedger::new();
            let id = ledger.begin(draft());
            assert!(ledger.set_route_admission_packet(
                id,
                RouteAdmissionPacket {
                    kind: RouteAdmissionPacketKind::FmlaEquivChainMainLrat,
                    status: RouteAdmissionPacketStatus::Complete,
                    original_dimacs_rows: 1,
                    original_clause_authority_rows: 4,
                    proof_obligation_rows: 4,
                    model_reconstruction_rows: 1,
                    external_proof_checker_verdict_artifact_rows: artifact_rows,
                },
            ));

            let err = ledger
                .commit(id)
                .expect_err("complete Fmla LRAT packet without checker verdict must fail closed");

            assert_eq!(
                err,
                PreprocessTransactionCommitError::RouteAdmissionPacketNotReady
            );
            let record = ledger
                .last_completed()
                .expect("checker-verdict fail-closed record retained");
            assert_eq!(record.outcome, PreprocessTransactionOutcome::FailClosed);
            assert_eq!(
                record.fail_closed_reason.as_deref(),
                Some(ROUTE_ADMISSION_PACKET_MISSING_EXTERNAL_CHECKER_VERDICT_REASON)
            );
        }
    }

    #[test]
    fn test_preprocess_transaction_route_admission_packet_fails_closed_without_original_clause_authority(
    ) {
        let mut ledger = PreprocessTransactionLedger::new();
        let id = ledger.begin(draft());
        assert!(ledger.set_route_admission_packet(
            id,
            RouteAdmissionPacket {
                kind: RouteAdmissionPacketKind::FmlaEquivChainMainLrat,
                status: RouteAdmissionPacketStatus::Complete,
                original_dimacs_rows: 1,
                original_clause_authority_rows: 3,
                proof_obligation_rows: 4,
                model_reconstruction_rows: 1,
                external_proof_checker_verdict_artifact_rows: 4,
            },
        ));

        let err = ledger.commit(id).expect_err(
            "complete Fmla LRAT packet without original-clause authority must fail closed",
        );

        assert_eq!(
            err,
            PreprocessTransactionCommitError::RouteAdmissionPacketNotReady
        );
        let record = ledger
            .last_completed()
            .expect("original-clause-authority fail-closed record retained");
        assert_eq!(record.outcome, PreprocessTransactionOutcome::FailClosed);
        assert_eq!(
            record.fail_closed_reason.as_deref(),
            Some(ROUTE_ADMISSION_PACKET_MISSING_ORIGINAL_CLAUSE_AUTHORITY_REASON)
        );
    }
}
