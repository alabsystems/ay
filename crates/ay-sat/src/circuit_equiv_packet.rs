// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Default-off circuit/equivalence packet facade.
//!
//! This module only copies witness data produced by existing read-only scouts.
//! The default packet path does not admit a route, emit a SAT/UNSAT result,
//! mutate clauses, or grant proof/model output authority. Authority can be
//! bound only through explicit retained original-DIMACS checker evidence.

use crate::circuit_scout::{
    audit_original_dimacs_sat_model_authority, validate_original_dimacs_assignment,
    CircuitMaterializedAssignment, CircuitModelValidationError, CircuitModelWitnessRejection,
    CircuitOriginalDimacsSatModelAuthorityAudit, CircuitOriginalDimacsSatModelAuthorityPacket,
    CircuitOriginalDimacsSatModelAuthorityStatus, CircuitParsedSourceFrameValueLedger,
    CircuitScoutRejection, CircuitScoutReport, CircuitSourceFrameAudit, CircuitSourceFrameFamily,
    CircuitSourceFrameKind, CircuitSourceFrameRow, CircuitSourceFrameValueLedgerKind,
    CircuitW210ValueLedgerAudit,
};
use crate::fmla_guarded_equiv_scout::{
    FmlaGuardedEquivRejection, FmlaGuardedEquivScout, FmlaGuardedEquivWitnesses,
};
use crate::literal::Literal;
use std::collections::BTreeMap;

/// Stable schema version for packet consumers.
pub(crate) const CIRCUIT_EQUIV_PACKET_SCHEMA_VERSION: u32 = 1;

/// Scoreboard row carried by a packet.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitEquivScoreboardRow {
    /// `Circuit_multiplier22`, expected SAT in the local SAT-COMP sample manifest.
    CircuitMultiplier22,
    /// `FmlaEquivChain_4_6_6`, expected UNSAT in the local SAT-COMP sample manifest.
    FmlaEquivChain466,
}

impl CircuitEquivScoreboardRow {
    /// Stable row identifier used in reports and future stats ingress.
    pub(crate) const fn as_str(self) -> &'static str {
        match self {
            Self::CircuitMultiplier22 => "Circuit_multiplier22",
            Self::FmlaEquivChain466 => "FmlaEquivChain_4_6_6",
        }
    }

    /// Manifest status known for this named row.
    pub(crate) const fn expected_status(self) -> CircuitEquivExpectedStatus {
        match self {
            Self::CircuitMultiplier22 => CircuitEquivExpectedStatus::Sat,
            Self::FmlaEquivChain466 => CircuitEquivExpectedStatus::Unsat,
        }
    }
}

/// Expected manifest status for a scoreboard row.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitEquivExpectedStatus {
    /// SAT row; any promoted route needs an original-DIMACS valid model.
    Sat,
    /// UNSAT row; any promoted route needs an externally checked proof.
    Unsat,
}

/// Packet-level SAT model obligation status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitEquivModelObligationStatus {
    /// Model output is not the relevant proof obligation for an expected UNSAT row.
    NotRequiredForExpectedUnsat,
    /// A SAT row packet is missing its circuit scout snapshot.
    MissingCircuitWitness,
    /// Direct original-variable assignments are still needed before replay.
    PendingDirectAssignment,
    /// Replay metadata is present, but no original-DIMACS source-frame audit exists yet.
    PendingOriginalDimacsValidation,
    /// Source-frame rows do not cover every original DIMACS variable.
    SourceFrameIncomplete,
    /// Source-frame validation rejected rows before replay.
    SourceFrameRejected,
    /// Source-frame replay leaves falsified original DIMACS clauses.
    SourceFrameResidualNonZero,
    /// Source-frame replay claims original-DIMACS validation; authority still remains false.
    OriginalDimacsValidated,
    /// Existing witness metadata is fail-closed and cannot support a model.
    FailClosed,
}

/// Packet-level UNSAT proof obligation status.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitEquivProofObligationStatus {
    /// Proof output is not the relevant obligation for an expected SAT row.
    NotRequiredForExpectedSat,
    /// An expected UNSAT row has no usable structural witness copy.
    MissingUnsatWitness,
    /// A later route would need an externally checked proof before authority.
    PendingExternalChecker,
    /// External checker accepted the proof obligation; authority still remains separate.
    ExternallyChecked,
}

/// Packet-level route admission decision for future callers.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitEquivRouteAdmissionStatus {
    /// This packet is allowed to drive a result-producing route.
    Admitted,
    /// Route is blocked with a typed reason.
    Blocked(CircuitEquivRouteAdmissionBlocker),
}

impl CircuitEquivRouteAdmissionStatus {
    /// True only for a fully admitted route.
    pub(crate) const fn is_admitted(self) -> bool {
        matches!(self, Self::Admitted)
    }
}

/// Typed route-admission blockers for result-silent packets.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitEquivRouteAdmissionBlocker {
    /// Packet-level authority bits are still absent.
    AuthorityAbsent,
    /// Packet authority bits are internally inconsistent.
    AuthorityInconsistent,
    /// SAT route has validation counters but no complete original-DIMACS model payload.
    MissingOriginalDimacsModel,
    /// SAT row still lacks a valid original-DIMACS model obligation.
    ModelObligation(CircuitEquivModelObligationStatus),
    /// UNSAT row still lacks an externally checked proof obligation.
    ProofObligation(CircuitEquivProofObligationStatus),
}

/// Result-silent packet that carries copied scout evidence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitEquivPacket {
    /// Schema version for deterministic consumers.
    pub(crate) schema_version: u32,
    /// Scoreboard row this packet intends to move later.
    pub(crate) scoreboard_row: CircuitEquivScoreboardRow,
    /// Expected manifest status for the row.
    pub(crate) expected_status: CircuitEquivExpectedStatus,
    /// Hard false until a separate legal-routing gate is implemented.
    pub(crate) route_admitted: bool,
    /// Hard false: the packet must never authorize SAT/UNSAT by itself.
    pub(crate) result_authority: bool,
    /// Hard false: SAT stdout is outside this facade.
    pub(crate) sat_output_authority: bool,
    /// Hard false: UNSAT stdout is outside this facade.
    pub(crate) unsat_output_authority: bool,
    /// Hard false: original-DIMACS model output is outside this facade.
    pub(crate) model_output_authority: bool,
    /// Hard false: proof output is outside this facade.
    pub(crate) proof_output_authority: bool,
    /// Current SAT model obligation state. This never grants model authority.
    pub(crate) model_obligation: CircuitEquivModelObligationStatus,
    /// Current UNSAT proof obligation state. This never grants proof authority.
    pub(crate) proof_obligation: CircuitEquivProofObligationStatus,
    /// Copied circuit/multiplier scout counters, if applicable.
    pub(crate) circuit: Option<CircuitEquivCircuitSnapshot>,
    /// Copied Fmla guarded-equivalence counters and witnesses, if applicable.
    pub(crate) fmla: Option<CircuitEquivFmlaSnapshot>,
    /// Optional copied source-frame audit rows; this is provenance only.
    pub(crate) source_frame: Option<CircuitEquivSourceFrameSnapshot>,
    /// Optional copied W210 value-ledger audit; this is fail-closed provenance only.
    pub(crate) w210_value_ledger: Option<CircuitEquivW210ValueLedgerSnapshot>,
    /// Optional complete original-DIMACS model validated for future SAT output.
    pub(crate) original_dimacs_model: Option<CircuitEquivOriginalDimacsModel>,
}

/// Complete original-DIMACS model payload after full CNF validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitEquivOriginalDimacsModel {
    /// Number of original DIMACS variables covered by `assignment`.
    pub(crate) original_model_vars: usize,
    /// Original clauses scanned before accepting the model payload.
    pub(crate) original_clauses_checked: usize,
    /// Complete assignment in zero-based original variable order.
    pub(crate) assignment: Vec<bool>,
}

/// Sealed outcome for the Circuit_multiplier22 SAT-model authority facade.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum CircuitEquivOriginalDimacsSatModelAuthorityDecision {
    /// Retained checker evidence and packet admission both authorized SAT/model output.
    Admitted {
        /// Complete original-DIMACS assignment in zero-based variable order.
        assignment: Vec<bool>,
        /// Stable copied counters for report/route consumers.
        counters: CircuitEquivPacketCounters,
    },
    /// The facade stayed fail-closed with copied diagnostics only.
    Blocked {
        /// Original-DIMACS authority audit status.
        authority_status: CircuitOriginalDimacsSatModelAuthorityStatus,
        /// Packet-level route admission status after binding source-frame counters.
        route_admission_status: CircuitEquivRouteAdmissionStatus,
        /// Stable copied counters for report/route consumers.
        counters: CircuitEquivPacketCounters,
    },
}

impl CircuitEquivOriginalDimacsSatModelAuthorityDecision {
    /// True only when the facade returned a checker-backed assignment.
    pub(crate) const fn is_admitted(&self) -> bool {
        matches!(self, Self::Admitted { .. })
    }

    /// Copied packet counters for diagnostics and route guards.
    pub(crate) const fn counters(&self) -> &CircuitEquivPacketCounters {
        match self {
            Self::Admitted { counters, .. } | Self::Blocked { counters, .. } => counters,
        }
    }
}

/// Fail-closed facade for Circuit_multiplier22 original-DIMACS SAT model authority.
///
/// The caller supplies retained artifact-bound checker evidence, but this
/// function owns the authority audit and packet handoff. It returns only a
/// blocked/admitted decision and never exposes mutable packet authority bits.
pub(crate) fn circuit_multiplier22_original_dimacs_sat_model_authority_decision(
    circuit: &CircuitScoutReport,
    num_vars: usize,
    clauses: &[Vec<Literal>],
    source_rows: &[CircuitSourceFrameRow],
    retained: CircuitOriginalDimacsSatModelAuthorityPacket,
) -> CircuitEquivOriginalDimacsSatModelAuthorityDecision {
    let audit = audit_original_dimacs_sat_model_authority(
        num_vars,
        clauses,
        source_rows,
        Some(&retained.artifacts),
        Some(&retained.checker_evidence),
    );
    let authority_status = audit.authority_status.clone();
    let packet = CircuitEquivPacket::for_circuit_multiplier22(circuit)
        .with_source_frame_rows(source_rows, &audit.source_frame_audit)
        .with_original_dimacs_sat_model_authority_audit(&audit);
    let route_admission_status = packet.route_admission_status();
    let counters = packet.counters();

    if route_admission_status.is_admitted() {
        if let Some(model) = packet.original_dimacs_model {
            return CircuitEquivOriginalDimacsSatModelAuthorityDecision::Admitted {
                assignment: model.assignment,
                counters,
            };
        }
    }

    CircuitEquivOriginalDimacsSatModelAuthorityDecision::Blocked {
        authority_status,
        route_admission_status,
        counters,
    }
}

impl CircuitEquivPacket {
    /// Build a result-silent packet for `Circuit_multiplier22`.
    pub(crate) fn for_circuit_multiplier22(circuit: &CircuitScoutReport) -> Self {
        let circuit = CircuitEquivCircuitSnapshot::from(circuit);
        let model_obligation = model_obligation_for(
            CircuitEquivScoreboardRow::CircuitMultiplier22,
            Some(&circuit),
            None,
            None,
        );
        Self {
            schema_version: CIRCUIT_EQUIV_PACKET_SCHEMA_VERSION,
            scoreboard_row: CircuitEquivScoreboardRow::CircuitMultiplier22,
            expected_status: CircuitEquivScoreboardRow::CircuitMultiplier22.expected_status(),
            route_admitted: false,
            result_authority: false,
            sat_output_authority: false,
            unsat_output_authority: false,
            model_output_authority: false,
            proof_output_authority: false,
            model_obligation,
            proof_obligation: CircuitEquivProofObligationStatus::NotRequiredForExpectedSat,
            circuit: Some(circuit),
            fmla: None,
            source_frame: None,
            w210_value_ledger: None,
            original_dimacs_model: None,
        }
    }

    /// Build a result-silent packet for `FmlaEquivChain_4_6_6`.
    pub(crate) fn for_fmla_equiv_chain_4_6_6(
        scout: &FmlaGuardedEquivScout,
        witnesses: Option<&FmlaGuardedEquivWitnesses>,
    ) -> Self {
        let fmla = CircuitEquivFmlaSnapshot::from_scout(scout, witnesses);
        let proof_obligation = proof_obligation_for_fmla(&fmla);
        Self {
            schema_version: CIRCUIT_EQUIV_PACKET_SCHEMA_VERSION,
            scoreboard_row: CircuitEquivScoreboardRow::FmlaEquivChain466,
            expected_status: CircuitEquivScoreboardRow::FmlaEquivChain466.expected_status(),
            route_admitted: false,
            result_authority: false,
            sat_output_authority: false,
            unsat_output_authority: false,
            model_output_authority: false,
            proof_output_authority: false,
            model_obligation: CircuitEquivModelObligationStatus::NotRequiredForExpectedUnsat,
            proof_obligation,
            circuit: None,
            fmla: Some(fmla),
            source_frame: None,
            w210_value_ledger: None,
            original_dimacs_model: None,
        }
    }

    /// Attach copied source-frame audit rows without materializing a model.
    pub(crate) fn with_source_frame_rows(
        mut self,
        rows: &[CircuitSourceFrameRow],
        audit: &CircuitSourceFrameAudit,
    ) -> Self {
        self.source_frame = Some(CircuitEquivSourceFrameSnapshot::from_rows(rows, audit));
        self.model_obligation = model_obligation_for(
            self.scoreboard_row,
            self.circuit.as_ref(),
            self.source_frame.as_ref(),
            self.w210_value_ledger.as_ref(),
        );
        self
    }

    /// Attach a complete model only after validating it against the original CNF.
    ///
    /// This payload is necessary but not sufficient for route admission; packet
    /// authority bits still remain controlled by a separate future caller.
    pub(crate) fn with_original_dimacs_model(
        mut self,
        num_vars: usize,
        clauses: &[Vec<Literal>],
        assignment: &[bool],
    ) -> Result<Self, CircuitModelValidationError> {
        let checked_assignment: Vec<_> = assignment.iter().copied().map(Some).collect();
        validate_original_dimacs_assignment(num_vars, clauses, &checked_assignment)?;
        self.original_dimacs_model = Some(CircuitEquivOriginalDimacsModel {
            original_model_vars: num_vars,
            original_clauses_checked: clauses.len(),
            assignment: assignment.to_vec(),
        });
        Ok(self)
    }

    /// Attach the real scout-side materialization output to the packet payload gate.
    ///
    /// The source-frame audit is copied first so route admission still observes
    /// the same provenance counters that produced the model. The assignment is
    /// then rechecked against the original CNF before storing the payload. This
    /// does not grant route, SAT stdout, or model-output authority.
    pub(crate) fn with_materialized_source_frame_model(
        self,
        rows: &[CircuitSourceFrameRow],
        materialized: &CircuitMaterializedAssignment,
        num_vars: usize,
        clauses: &[Vec<Literal>],
    ) -> Result<Self, CircuitModelValidationError> {
        self.with_source_frame_rows(rows, &materialized.audit)
            .with_original_dimacs_model(num_vars, clauses, &materialized.assignment)
    }

    /// Bind artifact-backed SAT/model authority from the scout-side original-DIMACS audit.
    ///
    /// This is the narrow production handoff for expected-SAT rows: source-frame
    /// replay must already be complete, retained `ay check model --json` evidence
    /// must have admitted the audit, and proof authority stays false. Any missing
    /// or rejected evidence leaves the packet unchanged and fail-closed.
    pub(crate) fn with_original_dimacs_sat_model_authority_audit(
        mut self,
        audit: &CircuitOriginalDimacsSatModelAuthorityAudit,
    ) -> Self {
        if self.expected_status != CircuitEquivExpectedStatus::Sat
            || !audit.authority_status.is_admitted()
            || !audit.retained_artifacts_supplied
            || !audit.checker_evidence_supplied
            || !audit.source_frame_audit.validation_passed
            || !audit.source_frame_audit.assignment_complete
            || audit.source_frame_audit.missing_source_rows != 0
            || audit.source_frame_audit.residual_falsified_count != 0
            || !audit.sat_output_authority
            || !audit.model_output_authority
            || audit.proof_output_authority
            || !audit.solver_verdict_authority
        {
            return self;
        }
        let Some(assignment) = audit.materialized_assignment.as_ref() else {
            return self;
        };

        self.model_obligation = CircuitEquivModelObligationStatus::OriginalDimacsValidated;
        self.original_dimacs_model = Some(CircuitEquivOriginalDimacsModel {
            original_model_vars: assignment.len(),
            original_clauses_checked: audit.source_frame_audit.original_clauses_checked,
            assignment: assignment.clone(),
        });
        self.route_admitted = true;
        self.result_authority = true;
        self.sat_output_authority = true;
        self.unsat_output_authority = false;
        self.model_output_authority = true;
        self.proof_output_authority = false;
        self
    }

    /// Attach copied W210 value-ledger audit evidence without granting authority.
    pub(crate) fn with_w210_value_ledger_audit(
        mut self,
        frontier: &CircuitParsedSourceFrameValueLedger,
        scc_choice: &CircuitParsedSourceFrameValueLedger,
        forced_gate: &CircuitParsedSourceFrameValueLedger,
        audit: &CircuitW210ValueLedgerAudit,
    ) -> Self {
        self.w210_value_ledger = Some(CircuitEquivW210ValueLedgerSnapshot::from_ledgers(
            frontier,
            scc_choice,
            forced_gate,
            audit,
        ));
        self.model_obligation = model_obligation_for(
            self.scoreboard_row,
            self.circuit.as_ref(),
            self.source_frame.as_ref(),
            self.w210_value_ledger.as_ref(),
        );
        self
    }

    /// True only when every authority bit remains fail-closed.
    pub(crate) const fn authority_is_absent(&self) -> bool {
        !self.route_admitted
            && !self.result_authority
            && !self.sat_output_authority
            && !self.unsat_output_authority
            && !self.model_output_authority
            && !self.proof_output_authority
    }

    /// Determine whether this packet may drive a future result route.
    pub(crate) fn route_admission_status(&self) -> CircuitEquivRouteAdmissionStatus {
        match self.expected_status {
            CircuitEquivExpectedStatus::Sat => {
                if self.model_obligation
                    != CircuitEquivModelObligationStatus::OriginalDimacsValidated
                {
                    return CircuitEquivRouteAdmissionStatus::Blocked(
                        CircuitEquivRouteAdmissionBlocker::ModelObligation(self.model_obligation),
                    );
                }
                if self.original_dimacs_model.is_none() {
                    return CircuitEquivRouteAdmissionStatus::Blocked(
                        CircuitEquivRouteAdmissionBlocker::MissingOriginalDimacsModel,
                    );
                }
            }
            CircuitEquivExpectedStatus::Unsat => {
                if self.proof_obligation != CircuitEquivProofObligationStatus::ExternallyChecked {
                    return CircuitEquivRouteAdmissionStatus::Blocked(
                        CircuitEquivRouteAdmissionBlocker::ProofObligation(self.proof_obligation),
                    );
                }
            }
        }
        if self.authority_is_absent() {
            return CircuitEquivRouteAdmissionStatus::Blocked(
                CircuitEquivRouteAdmissionBlocker::AuthorityAbsent,
            );
        }
        if !self.route_admitted || !self.result_authority {
            return CircuitEquivRouteAdmissionStatus::Blocked(
                CircuitEquivRouteAdmissionBlocker::AuthorityInconsistent,
            );
        }
        match self.expected_status {
            CircuitEquivExpectedStatus::Sat => {
                if !self.sat_output_authority || !self.model_output_authority {
                    return CircuitEquivRouteAdmissionStatus::Blocked(
                        CircuitEquivRouteAdmissionBlocker::AuthorityInconsistent,
                    );
                }
            }
            CircuitEquivExpectedStatus::Unsat => {
                if !self.unsat_output_authority || !self.proof_output_authority {
                    return CircuitEquivRouteAdmissionStatus::Blocked(
                        CircuitEquivRouteAdmissionBlocker::AuthorityInconsistent,
                    );
                }
            }
        }
        CircuitEquivRouteAdmissionStatus::Admitted
    }

    /// Stable counters expected to move for this default-off facade.
    pub(crate) fn counters(&self) -> CircuitEquivPacketCounters {
        let circuit = self.circuit.as_ref();
        let fmla = self.fmla.as_ref();
        let source_frame = self.source_frame.as_ref();
        let w210_value_ledger = self.w210_value_ledger.as_ref();
        let mut missing_witness_copies = 0usize;
        match self.scoreboard_row {
            CircuitEquivScoreboardRow::CircuitMultiplier22 if circuit.is_none() => {
                missing_witness_copies += 1;
            }
            CircuitEquivScoreboardRow::FmlaEquivChain466 if fmla.is_none() => {
                missing_witness_copies += 1;
            }
            _ => {}
        }

        CircuitEquivPacketCounters {
            schema_version: self.schema_version,
            row_id: self.scoreboard_row.as_str(),
            circuit_gate_output_witnesses: circuit
                .map(|snapshot| snapshot.model_witness.gate_output_witnesses)
                .unwrap_or(0),
            circuit_equivalence_alias_witnesses: circuit
                .map(|snapshot| snapshot.model_witness.equivalence_alias_witnesses)
                .unwrap_or(0),
            circuit_source_frame_rows: source_frame
                .map(|snapshot| snapshot.rows.len())
                .unwrap_or(0),
            circuit_w210_value_ledger_rows: w210_value_ledger
                .map(|snapshot| snapshot.audit.rows_seen)
                .unwrap_or(0),
            circuit_w210_value_ledger_residual_falsified_count: w210_value_ledger
                .map(|snapshot| snapshot.audit.residual_falsified_count)
                .unwrap_or(0),
            circuit_w210_value_ledger_assignment_complete: w210_value_ledger
                .map(|snapshot| snapshot.audit.assignment_complete)
                .unwrap_or(false),
            circuit_w210_value_ledger_validation_passed: w210_value_ledger
                .map(|snapshot| snapshot.audit.validation_passed)
                .unwrap_or(false),
            circuit_original_dimacs_model_present: self.original_dimacs_model.is_some(),
            circuit_original_dimacs_model_vars: self
                .original_dimacs_model
                .as_ref()
                .map(|model| model.original_model_vars)
                .unwrap_or(0),
            fmla_onehot_group_witnesses: fmla
                .map(|snapshot| snapshot.onehot_group_witnesses.len())
                .unwrap_or(0),
            fmla_guarded_equivalence_witnesses: fmla
                .map(|snapshot| snapshot.guarded_equivalence_witnesses.len())
                .unwrap_or(0),
            missing_witness_copies,
            model_obligation: self.model_obligation,
            proof_obligation: self.proof_obligation,
            route_admission_status: self.route_admission_status(),
            route_admitted: self.route_admitted,
            result_authority: self.result_authority,
        }
    }
}

fn model_obligation_for(
    row: CircuitEquivScoreboardRow,
    circuit: Option<&CircuitEquivCircuitSnapshot>,
    source_frame: Option<&CircuitEquivSourceFrameSnapshot>,
    w210_value_ledger: Option<&CircuitEquivW210ValueLedgerSnapshot>,
) -> CircuitEquivModelObligationStatus {
    if row.expected_status() == CircuitEquivExpectedStatus::Unsat {
        return CircuitEquivModelObligationStatus::NotRequiredForExpectedUnsat;
    }
    let Some(circuit) = circuit else {
        return CircuitEquivModelObligationStatus::MissingCircuitWitness;
    };
    let witness = &circuit.model_witness;
    if witness.fail_closed {
        return CircuitEquivModelObligationStatus::FailClosed;
    }
    let w210_obligation = w210_value_ledger.map(w210_model_obligation_for);
    if let Some(obligation) = w210_obligation {
        if obligation != CircuitEquivModelObligationStatus::OriginalDimacsValidated {
            return obligation;
        }
    }
    let Some(source_frame) = source_frame else {
        if let Some(obligation) = w210_obligation {
            return obligation;
        }
        if witness.partial_assignment_required_vars > 0 || witness.blocked_gate_output_vars > 0 {
            return CircuitEquivModelObligationStatus::PendingDirectAssignment;
        }
        return CircuitEquivModelObligationStatus::PendingOriginalDimacsValidation;
    };
    let source_frame_obligation = source_frame_model_obligation_for(source_frame);
    if source_frame_obligation != CircuitEquivModelObligationStatus::OriginalDimacsValidated {
        return source_frame_obligation;
    }
    w210_obligation.unwrap_or(CircuitEquivModelObligationStatus::OriginalDimacsValidated)
}

fn w210_model_obligation_for(
    w210_value_ledger: &CircuitEquivW210ValueLedgerSnapshot,
) -> CircuitEquivModelObligationStatus {
    let audit = &w210_value_ledger.audit;
    if audit.conflicting_rows > 0 {
        return CircuitEquivModelObligationStatus::SourceFrameRejected;
    }
    if !audit.assignment_complete || audit.missing_vars > 0 {
        return CircuitEquivModelObligationStatus::SourceFrameIncomplete;
    }
    if audit.residual_falsified_count > 0 || !audit.validation_passed {
        return CircuitEquivModelObligationStatus::SourceFrameResidualNonZero;
    }
    CircuitEquivModelObligationStatus::OriginalDimacsValidated
}

fn source_frame_model_obligation_for(
    source_frame: &CircuitEquivSourceFrameSnapshot,
) -> CircuitEquivModelObligationStatus {
    let audit = &source_frame.audit;
    if audit.rows_rejected > 0
        || audit.unsupported_family > 0
        || audit.var_out_of_range > 0
        || audit.literal_var_mismatch > 0
        || audit.clause_out_of_range > 0
        || audit.literal_missing_from_clause > 0
        || audit.conflicts > 0
    {
        return CircuitEquivModelObligationStatus::SourceFrameRejected;
    }
    if !audit.assignment_complete || audit.missing_source_rows > 0 {
        return CircuitEquivModelObligationStatus::SourceFrameIncomplete;
    }
    if audit.residual_falsified_count > 0 || !audit.validation_passed {
        return CircuitEquivModelObligationStatus::SourceFrameResidualNonZero;
    }
    CircuitEquivModelObligationStatus::OriginalDimacsValidated
}

fn proof_obligation_for_fmla(fmla: &CircuitEquivFmlaSnapshot) -> CircuitEquivProofObligationStatus {
    if fmla.rejection != CircuitEquivFmlaRejection::None
        || fmla.onehot_group_witnesses.is_empty()
        || fmla.guarded_equivalence_witnesses.is_empty()
    {
        CircuitEquivProofObligationStatus::MissingUnsatWitness
    } else {
        CircuitEquivProofObligationStatus::PendingExternalChecker
    }
}

/// Lightweight packet counters for tests and future report ingress.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitEquivPacketCounters {
    /// Packet schema version.
    pub(crate) schema_version: u32,
    /// Scoreboard row identifier.
    pub(crate) row_id: &'static str,
    /// Copied circuit gate-output witness count.
    pub(crate) circuit_gate_output_witnesses: u64,
    /// Copied circuit equivalence-alias witness count.
    pub(crate) circuit_equivalence_alias_witnesses: u64,
    /// Copied circuit source-frame row count.
    pub(crate) circuit_source_frame_rows: usize,
    /// Copied W210 value-ledger row count.
    pub(crate) circuit_w210_value_ledger_rows: usize,
    /// Copied W210 residual falsified-clause count.
    pub(crate) circuit_w210_value_ledger_residual_falsified_count: usize,
    /// Copied W210 complete-assignment bit.
    pub(crate) circuit_w210_value_ledger_assignment_complete: bool,
    /// Copied W210 original-DIMACS validation bit.
    pub(crate) circuit_w210_value_ledger_validation_passed: bool,
    /// True when a complete validated original-DIMACS model payload is attached.
    pub(crate) circuit_original_dimacs_model_present: bool,
    /// Original variable count covered by the attached model payload.
    pub(crate) circuit_original_dimacs_model_vars: usize,
    /// Copied Fmla one-hot group witness count.
    pub(crate) fmla_onehot_group_witnesses: usize,
    /// Copied Fmla guarded-equivalence witness count.
    pub(crate) fmla_guarded_equivalence_witnesses: usize,
    /// Missing row-required witness families.
    pub(crate) missing_witness_copies: usize,
    /// Current model obligation status; does not imply authority.
    pub(crate) model_obligation: CircuitEquivModelObligationStatus,
    /// Current proof obligation status; does not imply authority.
    pub(crate) proof_obligation: CircuitEquivProofObligationStatus,
    /// Current route admission status; does not imply authority.
    pub(crate) route_admission_status: CircuitEquivRouteAdmissionStatus,
    /// Copied authority bit; must remain false for this facade.
    pub(crate) route_admitted: bool,
    /// Copied authority bit; must remain false for this facade.
    pub(crate) result_authority: bool,
}

/// Copied circuit scout counters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitEquivCircuitSnapshot {
    /// Number of variables supplied by the DIMACS header.
    pub(crate) num_vars: usize,
    /// Number of clauses supplied by the parser.
    pub(crate) num_clauses: usize,
    /// Recovered AND gates.
    pub(crate) gate_and: u64,
    /// Recovered XOR gates.
    pub(crate) gate_xor: u64,
    /// Recovered ITE gates.
    pub(crate) gate_ite: u64,
    /// Recovered equivalence gates.
    pub(crate) gate_equiv: u64,
    /// Total recovered gate records.
    pub(crate) gates_total: u64,
    /// Sign-aware equivalence classes with more than one variable member.
    pub(crate) equivalence_classes: u64,
    /// Variable members participating in non-singleton equivalence classes.
    pub(crate) equivalence_members: u64,
    /// Duplicate structural gate fingerprints available for hashing.
    pub(crate) structural_hash_groups: u64,
    /// Extra gate outputs inside duplicate structural-hash groups.
    pub(crate) structural_hash_opportunities: u64,
    /// Half-adder motifs.
    pub(crate) half_adders: u64,
    /// Full-adder motifs.
    pub(crate) full_adders: u64,
    /// AND carry-term links participating in adder motifs.
    pub(crate) adder_carry_links: u64,
    /// AND2 gates whose inputs are not recovered gate outputs.
    pub(crate) partial_product_ands: u64,
    /// Multiplier-like cones supported by partial products and adder motifs.
    pub(crate) multiplier_cones: u64,
    /// Source scout rejection, copied for diagnostics only.
    pub(crate) rejection: CircuitEquivCircuitRejection,
    /// Copied model-witness obligations.
    pub(crate) model_witness: CircuitEquivModelWitnessSnapshot,
}

impl From<&CircuitScoutReport> for CircuitEquivCircuitSnapshot {
    fn from(report: &CircuitScoutReport) -> Self {
        Self {
            num_vars: report.num_vars,
            num_clauses: report.num_clauses,
            gate_and: report.gate_and,
            gate_xor: report.gate_xor,
            gate_ite: report.gate_ite,
            gate_equiv: report.gate_equiv,
            gates_total: report.gates_total,
            equivalence_classes: report.equivalence_classes,
            equivalence_members: report.equivalence_members,
            structural_hash_groups: report.structural_hash_groups,
            structural_hash_opportunities: report.structural_hash_opportunities,
            half_adders: report.half_adders,
            full_adders: report.full_adders,
            adder_carry_links: report.adder_carry_links,
            partial_product_ands: report.partial_product_ands,
            multiplier_cones: report.multiplier_cones,
            rejection: CircuitEquivCircuitRejection::from(report.rejection),
            model_witness: CircuitEquivModelWitnessSnapshot::from(&report.model_witness),
        }
    }
}

/// Stable copy of circuit scout rejection reasons.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitEquivCircuitRejection {
    /// No rejection in the source scout.
    None,
    /// Dense clique/mutex shape.
    DenseCliqueShape,
    /// Equivalence-chain shape without multiplier gate evidence.
    EquivalenceChainShape,
    /// Too few recovered AND/XOR gates.
    MissingGateMix,
    /// Gates were present, but no adder-like cones were recovered.
    MissingAdderCone,
    /// Adders were present, but no multiplier partial-product cone was visible.
    MissingMultiplierCone,
}

impl From<CircuitScoutRejection> for CircuitEquivCircuitRejection {
    fn from(rejection: CircuitScoutRejection) -> Self {
        match rejection {
            CircuitScoutRejection::None => Self::None,
            CircuitScoutRejection::DenseCliqueShape => Self::DenseCliqueShape,
            CircuitScoutRejection::EquivalenceChainShape => Self::EquivalenceChainShape,
            CircuitScoutRejection::MissingGateMix => Self::MissingGateMix,
            CircuitScoutRejection::MissingAdderCone => Self::MissingAdderCone,
            CircuitScoutRejection::MissingMultiplierCone => Self::MissingMultiplierCone,
        }
    }
}

/// Copied model-reconstruction obligations from the circuit scout.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitEquivModelWitnessSnapshot {
    /// Original DIMACS variable count that a complete model must cover.
    pub(crate) original_model_vars: usize,
    /// Recovered gate-output witnesses over original variables.
    pub(crate) gate_output_witnesses: u64,
    /// AND gate output witnesses.
    pub(crate) and_output_witnesses: u64,
    /// XOR gate output witnesses.
    pub(crate) xor_output_witnesses: u64,
    /// ITE gate output witnesses.
    pub(crate) ite_output_witnesses: u64,
    /// Equivalence gate output witnesses.
    pub(crate) equiv_output_witnesses: u64,
    /// Non-representative members of recovered equivalence classes.
    pub(crate) equivalence_alias_witnesses: u64,
    /// Half/full adder sum-output witnesses.
    pub(crate) adder_sum_witnesses: u64,
    /// AND carry-term witnesses used by recovered adder motifs.
    pub(crate) adder_carry_witnesses: u64,
    /// Partial-product AND witnesses whose inputs are not recovered gate outputs.
    pub(crate) partial_product_witnesses: u64,
    /// Original variables that a partial specialist assignment must provide.
    pub(crate) partial_assignment_required_vars: usize,
    /// Unique gate-output variables derivable from the frontier.
    pub(crate) derivable_gate_output_vars: usize,
    /// Deterministic topological replay order length over derivable outputs.
    pub(crate) acyclic_replay_order_len: usize,
    /// Unique gate-output variables requiring direct assignment.
    pub(crate) blocked_gate_output_vars: usize,
    /// Blocked outputs whose defining gate depends on a cycle.
    pub(crate) blocked_by_cycle_output_vars: usize,
    /// Blocked outputs sharing a duplicate recovered definition.
    pub(crate) blocked_by_duplicate_output_vars: usize,
    /// Blocked outputs with malformed or out-of-range dependencies.
    pub(crate) blocked_by_malformed_dependency_output_vars: usize,
    /// Blocked outputs with unresolved non-cyclic dependencies.
    pub(crate) blocked_by_unresolved_dependency_output_vars: usize,
    /// Dependency edges from blocked gate outputs to other blocked outputs.
    pub(crate) blocked_output_dependency_edges: usize,
    /// Duplicate recovered gate definitions for the same output variable.
    pub(crate) duplicate_gate_output_defs: u64,
    /// Recovered gate outputs outside the DIMACS header range.
    pub(crate) out_of_range_gate_outputs: u64,
    /// Recovered gate inputs outside the DIMACS header range.
    pub(crate) out_of_range_gate_inputs: u64,
    /// Number of original variables covered by frontier plus derivable outputs.
    pub(crate) complete_original_model_vars: usize,
    /// True when reconstruction metadata must not be used for model output.
    pub(crate) fail_closed: bool,
    /// First fail-closed reason.
    pub(crate) rejection: CircuitEquivModelWitnessRejection,
}

impl From<&crate::circuit_scout::CircuitModelWitnessReport> for CircuitEquivModelWitnessSnapshot {
    fn from(report: &crate::circuit_scout::CircuitModelWitnessReport) -> Self {
        Self {
            original_model_vars: report.original_model_vars,
            gate_output_witnesses: report.gate_output_witnesses,
            and_output_witnesses: report.and_output_witnesses,
            xor_output_witnesses: report.xor_output_witnesses,
            ite_output_witnesses: report.ite_output_witnesses,
            equiv_output_witnesses: report.equiv_output_witnesses,
            equivalence_alias_witnesses: report.equivalence_alias_witnesses,
            adder_sum_witnesses: report.adder_sum_witnesses,
            adder_carry_witnesses: report.adder_carry_witnesses,
            partial_product_witnesses: report.partial_product_witnesses,
            partial_assignment_required_vars: report.partial_assignment_required_vars,
            derivable_gate_output_vars: report.derivable_gate_output_vars,
            acyclic_replay_order_len: report.acyclic_replay_order_len,
            blocked_gate_output_vars: report.blocked_gate_output_vars,
            blocked_by_cycle_output_vars: report.blocked_by_cycle_output_vars,
            blocked_by_duplicate_output_vars: report.blocked_by_duplicate_output_vars,
            blocked_by_malformed_dependency_output_vars: report
                .blocked_by_malformed_dependency_output_vars,
            blocked_by_unresolved_dependency_output_vars: report
                .blocked_by_unresolved_dependency_output_vars,
            blocked_output_dependency_edges: report.blocked_output_dependency_edges,
            duplicate_gate_output_defs: report.duplicate_gate_output_defs,
            out_of_range_gate_outputs: report.out_of_range_gate_outputs,
            out_of_range_gate_inputs: report.out_of_range_gate_inputs,
            complete_original_model_vars: report.complete_original_model_vars,
            fail_closed: report.fail_closed,
            rejection: CircuitEquivModelWitnessRejection::from(report.rejection),
        }
    }
}

/// Stable copy of circuit model-witness rejection reasons.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitEquivModelWitnessRejection {
    /// No rejection in the source scout.
    None,
    /// A recovered gate output variable was outside the DIMACS header range.
    GateOutputOutOfRange,
    /// A recovered gate input variable was outside the DIMACS header range.
    GateInputOutOfRange,
    /// More than one recovered gate tried to define the same output variable.
    DuplicateGateOutput,
    /// Some gate outputs could not be covered as direct or derivable values.
    BlockedGateOutput,
}

impl From<CircuitModelWitnessRejection> for CircuitEquivModelWitnessRejection {
    fn from(rejection: CircuitModelWitnessRejection) -> Self {
        match rejection {
            CircuitModelWitnessRejection::None => Self::None,
            CircuitModelWitnessRejection::GateOutputOutOfRange => Self::GateOutputOutOfRange,
            CircuitModelWitnessRejection::GateInputOutOfRange => Self::GateInputOutOfRange,
            CircuitModelWitnessRejection::DuplicateGateOutput => Self::DuplicateGateOutput,
            CircuitModelWitnessRejection::BlockedGateOutput => Self::BlockedGateOutput,
        }
    }
}

/// Copied Fmla guarded-equivalence scout counters and witnesses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitEquivFmlaSnapshot {
    /// Number of variables declared by the DIMACS header.
    pub(crate) num_vars: usize,
    /// Number of clauses supplied to the scout.
    pub(crate) num_clauses: usize,
    /// Positive clauses whose variables have all pairwise negative mutexes.
    pub(crate) onehot_groups: usize,
    /// Width histogram for recovered exactly-one groups.
    pub(crate) onehot_width_hist: BTreeMap<usize, usize>,
    /// Distinct variables covered by recovered exactly-one groups.
    pub(crate) onehot_variables: usize,
    /// Recovered guarded equivalences.
    pub(crate) guarded_equivalence_pairs: usize,
    /// Distinct one-hot guard variables used by recovered guarded equivalences.
    pub(crate) guarded_equivalence_guards: usize,
    /// Histogram of recovered guarded-equivalence fanout per guard.
    pub(crate) guarded_equivalence_guard_fanout_hist: BTreeMap<usize, usize>,
    /// Stable fail-closed classification from the source scout.
    pub(crate) rejection: CircuitEquivFmlaRejection,
    /// Copied exactly-one group witnesses.
    pub(crate) onehot_group_witnesses: Vec<CircuitEquivOneHotGroupWitness>,
    /// Copied guarded-equivalence witnesses.
    pub(crate) guarded_equivalence_witnesses: Vec<CircuitEquivGuardedEquivalenceWitness>,
}

impl CircuitEquivFmlaSnapshot {
    fn from_scout(
        scout: &FmlaGuardedEquivScout,
        witnesses: Option<&FmlaGuardedEquivWitnesses>,
    ) -> Self {
        let (onehot_group_witnesses, guarded_equivalence_witnesses) =
            if let Some(witnesses) = witnesses {
                (
                    witnesses
                        .onehot_groups
                        .iter()
                        .map(CircuitEquivOneHotGroupWitness::from)
                        .collect(),
                    witnesses
                        .guarded_equivalences
                        .iter()
                        .map(CircuitEquivGuardedEquivalenceWitness::from)
                        .collect(),
                )
            } else {
                (Vec::new(), Vec::new())
            };
        Self {
            num_vars: scout.num_vars,
            num_clauses: scout.num_clauses,
            onehot_groups: scout.onehot_groups,
            onehot_width_hist: scout.onehot_width_hist.clone(),
            onehot_variables: scout.onehot_variables,
            guarded_equivalence_pairs: scout.guarded_equivalence_pairs,
            guarded_equivalence_guards: scout.guarded_equivalence_guards,
            guarded_equivalence_guard_fanout_hist: scout
                .guarded_equivalence_guard_fanout_hist
                .clone(),
            rejection: CircuitEquivFmlaRejection::from(scout.rejection),
            onehot_group_witnesses,
            guarded_equivalence_witnesses,
        }
    }
}

/// Stable copy of Fmla guarded-equivalence rejection reasons.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitEquivFmlaRejection {
    /// The scout found a guarded-equivalence packet.
    None,
    /// No exactly-one guard groups were recovered.
    NoOnehotGroups,
    /// One-hot groups exist, but not with the Fmla width-6 surface.
    NoWidthSixOnehotGroups,
    /// No paired guarded equivalences were recovered over one-hot guards.
    NoGuardedEquivalencePairs,
}

impl From<FmlaGuardedEquivRejection> for CircuitEquivFmlaRejection {
    fn from(rejection: FmlaGuardedEquivRejection) -> Self {
        match rejection {
            FmlaGuardedEquivRejection::None => Self::None,
            FmlaGuardedEquivRejection::NoOnehotGroups => Self::NoOnehotGroups,
            FmlaGuardedEquivRejection::NoWidthSixOnehotGroups => Self::NoWidthSixOnehotGroups,
            FmlaGuardedEquivRejection::NoGuardedEquivalencePairs => Self::NoGuardedEquivalencePairs,
        }
    }
}

/// Copied DIMACS-source witness for one exactly-one guard group.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitEquivOneHotGroupWitness {
    /// One-based DIMACS clause id of the positive support clause.
    pub(crate) support_clause_id: usize,
    /// Positive DIMACS variables in the guard group.
    pub(crate) vars: Vec<i32>,
    /// One-based DIMACS clause ids for all pairwise mutex clauses.
    pub(crate) mutex_clause_ids: Vec<usize>,
}

impl From<&crate::fmla_guarded_equiv_scout::FmlaOneHotGroupWitness>
    for CircuitEquivOneHotGroupWitness
{
    fn from(witness: &crate::fmla_guarded_equiv_scout::FmlaOneHotGroupWitness) -> Self {
        Self {
            support_clause_id: witness.support_clause_id,
            vars: witness.vars.clone(),
            mutex_clause_ids: witness.mutex_clause_ids.clone(),
        }
    }
}

/// Copied DIMACS-source witness for one guarded equivalence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitEquivGuardedEquivalenceWitness {
    /// Positive DIMACS guard variable.
    pub(crate) guard: i32,
    /// Lower positive DIMACS endpoint variable.
    pub(crate) lhs: i32,
    /// Higher positive DIMACS endpoint variable.
    pub(crate) rhs: i32,
    /// One-based DIMACS clause id for `-guard -lhs rhs`.
    pub(crate) forward_clause_id: usize,
    /// One-based DIMACS clause id for `-guard -rhs lhs`.
    pub(crate) reverse_clause_id: usize,
    /// Forward clause literals as they appeared in the input.
    pub(crate) forward_clause_lits: Vec<i32>,
    /// Reverse clause literals as they appeared in the input.
    pub(crate) reverse_clause_lits: Vec<i32>,
}

impl From<&crate::fmla_guarded_equiv_scout::FmlaGuardedEquivalenceWitness>
    for CircuitEquivGuardedEquivalenceWitness
{
    fn from(witness: &crate::fmla_guarded_equiv_scout::FmlaGuardedEquivalenceWitness) -> Self {
        Self {
            guard: witness.guard,
            lhs: witness.lhs,
            rhs: witness.rhs,
            forward_clause_id: witness.forward_clause_id,
            reverse_clause_id: witness.reverse_clause_id,
            forward_clause_lits: witness.forward_clause_lits.clone(),
            reverse_clause_lits: witness.reverse_clause_lits.clone(),
        }
    }
}

/// Copied circuit source-frame rows and audit counters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitEquivSourceFrameSnapshot {
    /// Copied rows from the audited source-frame surface.
    pub(crate) rows: Vec<CircuitEquivSourceFrameRow>,
    /// Copied audit counters.
    pub(crate) audit: CircuitEquivSourceFrameAuditSnapshot,
}

impl CircuitEquivSourceFrameSnapshot {
    fn from_rows(rows: &[CircuitSourceFrameRow], audit: &CircuitSourceFrameAudit) -> Self {
        Self {
            rows: rows.iter().map(CircuitEquivSourceFrameRow::from).collect(),
            audit: CircuitEquivSourceFrameAuditSnapshot::from(audit),
        }
    }
}

/// Copied source-frame row bound to an original DIMACS clause literal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitEquivSourceFrameRow {
    /// Stable source row identifier from the producing packet.
    pub(crate) source_row_id: u64,
    /// Zero-based original DIMACS variable index.
    pub(crate) var: usize,
    /// Literal copied in DIMACS signed-integer form.
    pub(crate) literal_dimacs: i32,
    /// Zero-based original clause index containing `literal_dimacs`.
    pub(crate) clause_id: usize,
    /// Source-frame truth value for `var`.
    pub(crate) source_value: bool,
    /// Provenance family for this value.
    pub(crate) family: CircuitEquivSourceFrameFamily,
    /// Source-frame row kind for diagnostics.
    pub(crate) kind: CircuitEquivSourceFrameKind,
}

impl From<&CircuitSourceFrameRow> for CircuitEquivSourceFrameRow {
    fn from(row: &CircuitSourceFrameRow) -> Self {
        Self {
            source_row_id: row.source_row_id,
            var: row.var,
            literal_dimacs: row.literal.to_dimacs(),
            clause_id: row.clause_id,
            source_value: row.source_value,
            family: CircuitEquivSourceFrameFamily::from(row.family),
            kind: CircuitEquivSourceFrameKind::from(row.kind),
        }
    }
}

/// Stable copy of circuit source-frame family.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitEquivSourceFrameFamily {
    /// W390/A162-approved forced-gate source-frame bridge input.
    ForcedGateReplayBridge,
    /// W210 frontier value ledger rows.
    W210Frontier,
    /// W210 SCC choice value ledger rows.
    W210SccChoice,
    /// W377 combined selector rows, retained as negative evidence only.
    W377CombinedSelector,
    /// Any selector whose only accepted evidence is proxy-frame closure.
    ProxyOnlySelector,
    /// Unknown or not-yet-audited source frame family.
    Other,
}

impl From<CircuitSourceFrameFamily> for CircuitEquivSourceFrameFamily {
    fn from(family: CircuitSourceFrameFamily) -> Self {
        match family {
            CircuitSourceFrameFamily::ForcedGateReplayBridge => Self::ForcedGateReplayBridge,
            CircuitSourceFrameFamily::W210Frontier => Self::W210Frontier,
            CircuitSourceFrameFamily::W210SccChoice => Self::W210SccChoice,
            CircuitSourceFrameFamily::W377CombinedSelector => Self::W377CombinedSelector,
            CircuitSourceFrameFamily::ProxyOnlySelector => Self::ProxyOnlySelector,
            CircuitSourceFrameFamily::Other => Self::Other,
        }
    }
}

/// Stable copy of circuit source-frame row kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitEquivSourceFrameKind {
    /// Forced gate replay bridge value.
    ForcedGateReplayBridge,
    /// Frontier value from W210-style ledger rows.
    FrontierValue,
    /// SCC choice value from W210-style ledger rows.
    SccChoiceValue,
    /// Other accepted direct value from an audited source family.
    DirectValue,
    /// Direct value for an original DIMACS variable that has no clause occurrence.
    UnreferencedOriginalValue,
}

impl From<CircuitSourceFrameKind> for CircuitEquivSourceFrameKind {
    fn from(kind: CircuitSourceFrameKind) -> Self {
        match kind {
            CircuitSourceFrameKind::ForcedGateReplayBridge => Self::ForcedGateReplayBridge,
            CircuitSourceFrameKind::FrontierValue => Self::FrontierValue,
            CircuitSourceFrameKind::SccChoiceValue => Self::SccChoiceValue,
            CircuitSourceFrameKind::DirectValue => Self::DirectValue,
            CircuitSourceFrameKind::UnreferencedOriginalValue => Self::UnreferencedOriginalValue,
        }
    }
}

/// Copied source-frame audit counters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitEquivSourceFrameAuditSnapshot {
    /// Input source-frame rows scanned.
    pub(crate) rows_seen: usize,
    /// Rows accepted into the direct assignment seed.
    pub(crate) rows_accepted: usize,
    /// Rows rejected before assignment replay.
    pub(crate) rows_rejected: usize,
    /// Rows rejected because their family is not an original-DIMACS source.
    pub(crate) unsupported_family: usize,
    /// Rows with `var` outside the original DIMACS range.
    pub(crate) var_out_of_range: usize,
    /// Rows whose literal variable did not match `var`.
    pub(crate) literal_var_mismatch: usize,
    /// Rows with `clause_id` outside the original clause list.
    pub(crate) clause_out_of_range: usize,
    /// Rows whose bound literal was absent from the named original clause.
    pub(crate) literal_missing_from_clause: usize,
    /// Rows accepted because the original variable has no clause occurrence.
    pub(crate) unreferenced_original_var_rows: usize,
    /// Rows that claimed unreferenced-variable status for an occurring variable.
    pub(crate) unreferenced_var_occurs: usize,
    /// Rows that conflicted with an earlier source value for the same variable.
    pub(crate) conflicts: usize,
    /// Variables still unassigned after source rows plus replay.
    pub(crate) missing_source_rows: usize,
    /// Original clauses scanned after replay.
    pub(crate) original_clauses_checked: usize,
    /// Falsified original clauses after replay.
    pub(crate) residual_falsified_count: usize,
    /// First falsified original clause, if any.
    pub(crate) first_residual_clause: Option<usize>,
    /// Falsified original clause IDs after replay.
    pub(crate) residual_clause_ids: Vec<usize>,
    /// True when every original variable has a value after replay.
    pub(crate) assignment_complete: bool,
    /// True only when the final original-DIMACS validation passes.
    pub(crate) validation_passed: bool,
}

impl From<&CircuitSourceFrameAudit> for CircuitEquivSourceFrameAuditSnapshot {
    fn from(audit: &CircuitSourceFrameAudit) -> Self {
        Self {
            rows_seen: audit.rows_seen,
            rows_accepted: audit.rows_accepted,
            rows_rejected: audit.rows_rejected,
            unsupported_family: audit.unsupported_family,
            var_out_of_range: audit.var_out_of_range,
            literal_var_mismatch: audit.literal_var_mismatch,
            clause_out_of_range: audit.clause_out_of_range,
            literal_missing_from_clause: audit.literal_missing_from_clause,
            unreferenced_original_var_rows: audit.unreferenced_original_var_rows,
            unreferenced_var_occurs: audit.unreferenced_var_occurs,
            conflicts: audit.conflicts,
            missing_source_rows: audit.missing_source_rows,
            original_clauses_checked: audit.original_clauses_checked,
            residual_falsified_count: audit.residual_falsified_count,
            first_residual_clause: audit.first_residual_clause,
            residual_clause_ids: audit.residual_clause_ids.clone(),
            assignment_complete: audit.assignment_complete,
            validation_passed: audit.validation_passed,
        }
    }
}

/// Copied W210 value-ledger stats and combined residual audit.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitEquivW210ValueLedgerSnapshot {
    /// Copied frontier ledger stats.
    pub(crate) frontier: CircuitEquivW210ValueLedgerStatsSnapshot,
    /// Copied SCC-choice ledger stats.
    pub(crate) scc_choice: CircuitEquivW210ValueLedgerStatsSnapshot,
    /// Copied forced-gate ledger stats.
    pub(crate) forced_gate: CircuitEquivW210ValueLedgerStatsSnapshot,
    /// Copied combined assignment/residual audit.
    pub(crate) audit: CircuitEquivW210ValueLedgerAuditSnapshot,
}

impl CircuitEquivW210ValueLedgerSnapshot {
    fn from_ledgers(
        frontier: &CircuitParsedSourceFrameValueLedger,
        scc_choice: &CircuitParsedSourceFrameValueLedger,
        forced_gate: &CircuitParsedSourceFrameValueLedger,
        audit: &CircuitW210ValueLedgerAudit,
    ) -> Self {
        Self {
            frontier: CircuitEquivW210ValueLedgerStatsSnapshot::from_ledger(frontier),
            scc_choice: CircuitEquivW210ValueLedgerStatsSnapshot::from_ledger(scc_choice),
            forced_gate: CircuitEquivW210ValueLedgerStatsSnapshot::from_ledger(forced_gate),
            audit: CircuitEquivW210ValueLedgerAuditSnapshot::from(audit),
        }
    }
}

/// Stable copy of a W210 value-ledger role.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum CircuitEquivW210ValueLedgerKind {
    /// `frontier-value-ledger.tsv`.
    Frontier,
    /// `scc-choice-value-ledger.tsv`.
    SccChoice,
    /// `forced-gate-value-ledger.tsv`.
    ForcedGate,
}

impl From<CircuitSourceFrameValueLedgerKind> for CircuitEquivW210ValueLedgerKind {
    fn from(kind: CircuitSourceFrameValueLedgerKind) -> Self {
        match kind {
            CircuitSourceFrameValueLedgerKind::W210Frontier => Self::Frontier,
            CircuitSourceFrameValueLedgerKind::W210SccChoice => Self::SccChoice,
            CircuitSourceFrameValueLedgerKind::W210ForcedGate => Self::ForcedGate,
        }
    }
}

/// Copied W210 per-ledger parse counters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitEquivW210ValueLedgerStatsSnapshot {
    /// Ledger role copied.
    pub(crate) kind: CircuitEquivW210ValueLedgerKind,
    /// Data rows scanned.
    pub(crate) rows_seen: usize,
    /// Data rows accepted by the parser.
    pub(crate) rows_accepted: usize,
    /// Rows that incorrectly claimed route eligibility.
    pub(crate) route_eligible_rows: usize,
    /// Rows carrying the accepted fail-closed route blocker.
    pub(crate) route_blocked_rows: usize,
    /// Rows present in W159's remaining falsified-clause surface.
    pub(crate) present_in_remaining_clause_rows: usize,
    /// Maximum one-based original variable ID seen.
    pub(crate) max_original_var_1_based: usize,
}

impl CircuitEquivW210ValueLedgerStatsSnapshot {
    fn from_ledger(ledger: &CircuitParsedSourceFrameValueLedger) -> Self {
        Self {
            kind: CircuitEquivW210ValueLedgerKind::from(ledger.kind),
            rows_seen: ledger.stats.rows_seen,
            rows_accepted: ledger.stats.rows_accepted,
            route_eligible_rows: ledger.stats.route_eligible_rows,
            route_blocked_rows: ledger.stats.route_blocked_rows,
            present_in_remaining_clause_rows: ledger.stats.present_in_remaining_clause_rows,
            max_original_var_1_based: ledger.stats.max_original_var_1_based,
        }
    }
}

/// Copied W210 combined assignment/residual counters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CircuitEquivW210ValueLedgerAuditSnapshot {
    /// Total parsed W210 rows scanned.
    pub(crate) rows_seen: usize,
    /// Rows accepted as the first value for an original variable.
    pub(crate) rows_accepted: usize,
    /// Duplicate rows that repeated the same value.
    pub(crate) duplicate_same_value_rows: usize,
    /// Duplicate rows that conflicted with an already covered variable.
    pub(crate) conflicting_rows: usize,
    /// Original variables covered by at least one W210 row.
    pub(crate) covered_vars: usize,
    /// Original variables not covered by the combined W210 ledgers.
    pub(crate) missing_vars: usize,
    /// First missing original variable, if any.
    pub(crate) first_missing_var: Option<usize>,
    /// Original clauses scanned by residual diagnostics.
    pub(crate) original_clauses_checked: usize,
    /// Falsified original clauses under the combined W210 value surface.
    pub(crate) residual_falsified_count: usize,
    /// First falsified original clause, if any.
    pub(crate) first_residual_clause: Option<usize>,
    /// All falsified original clause IDs.
    pub(crate) residual_clause_ids: Vec<usize>,
    /// True when every original variable was covered.
    pub(crate) assignment_complete: bool,
    /// True only after a complete, conflict-free, satisfying original-DIMACS audit.
    pub(crate) validation_passed: bool,
}

impl From<&CircuitW210ValueLedgerAudit> for CircuitEquivW210ValueLedgerAuditSnapshot {
    fn from(audit: &CircuitW210ValueLedgerAudit) -> Self {
        Self {
            rows_seen: audit.rows_seen,
            rows_accepted: audit.rows_accepted,
            duplicate_same_value_rows: audit.duplicate_same_value_rows,
            conflicting_rows: audit.conflicting_rows,
            covered_vars: audit.covered_vars,
            missing_vars: audit.missing_vars,
            first_missing_var: audit.first_missing_var,
            original_clauses_checked: audit.original_clauses_checked,
            residual_falsified_count: audit.residual_falsified_count,
            first_residual_clause: audit.first_residual_clause,
            residual_clause_ids: audit.residual_clause_ids.clone(),
            assignment_complete: audit.assignment_complete,
            validation_passed: audit.validation_passed,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::circuit_scout::{
        audit_original_dimacs_sat_model_authority, audit_w210_route_admission_blocker,
        materialize_original_dimacs_assignment_from_source_frame_rows,
        parse_w210_source_frame_value_ledger, produce_original_dimacs_sat_model_authority_packet,
        scout_formula, CircuitModelWitnessReport, CircuitOriginalDimacsSatModelAuthorityPacket,
        CircuitParsedSourceFrameValueLedger, CircuitSourceFrameRow, CircuitSourceFrameValue,
        CircuitSourceFrameValueLedgerRow, CircuitSourceFrameValueLedgerStats,
        CircuitW210RouteAdmissionBlocker, CircuitW210RouteAdmissionStatus,
        CircuitW210ValueLedgerAudit,
    };
    use crate::dimacs::parse_str;
    use crate::fmla_guarded_equiv_scout::{
        FmlaGuardedEquivWitnesses, FmlaGuardedEquivalenceWitness, FmlaOneHotGroupWitness,
    };
    use crate::literal::{Literal, Variable};
    use std::path::{Path, PathBuf};

    const CIRCUIT_MULTIPLIER22_CNF: &str =
        "benchmarks/sat/satcomp2024-sample/c5ae0ec49de0959cd14431ce851c14f8-Circuit_multiplier22.cnf.xz";
    const W210_FRONTIER_LEDGER: &str = "the development design notes";
    const W210_SCC_LEDGER: &str = "the development design notes";
    const W210_FORCED_LEDGER: &str = "the development design notes";

    fn retained_model_check_json(
        formula_path: &str,
        model_stdout_path: &str,
        num_vars: usize,
        clauses_checked: usize,
        valid: bool,
    ) -> Vec<u8> {
        let model_status = if valid { "valid" } else { "invalid" };
        format!(
            r#"{{"schema":"ay.satcomp-model-check/v1","formula":"{formula_path}","stdout":"{model_stdout_path}","model_status":"{model_status}","valid":{valid},"num_vars":{num_vars},"clauses_checked":{clauses_checked},"first_unsatisfied_clause":null,"elapsed_ms":0,"ay_build":{{"stamp":"packet-authority-test"}}}}"#
        )
        .into_bytes()
    }

    fn circuit_multiplier22_authority_fixture(
        checker_valid: bool,
    ) -> (
        Vec<Vec<Literal>>,
        Vec<CircuitSourceFrameRow>,
        CircuitScoutReport,
        CircuitOriginalDimacsSatModelAuthorityPacket,
    ) {
        let out = Variable::new(2);
        let a = Variable::new(0);
        let b = Variable::new(1);
        let clauses = vec![
            vec![Literal::negative(out), Literal::positive(a)],
            vec![Literal::negative(out), Literal::positive(b)],
            vec![
                Literal::positive(out),
                Literal::negative(a),
                Literal::negative(b),
            ],
        ];
        let source_rows = vec![
            CircuitSourceFrameRow {
                source_row_id: 10,
                var: 0,
                literal: Literal::positive(a),
                clause_id: 0,
                source_value: true,
                family: CircuitSourceFrameFamily::W210Frontier,
                kind: CircuitSourceFrameKind::FrontierValue,
            },
            CircuitSourceFrameRow {
                source_row_id: 11,
                var: 1,
                literal: Literal::positive(b),
                clause_id: 1,
                source_value: false,
                family: CircuitSourceFrameFamily::ForcedGateReplayBridge,
                kind: CircuitSourceFrameKind::ForcedGateReplayBridge,
            },
        ];
        let report = CircuitScoutReport {
            num_vars: 3,
            num_clauses: clauses.len(),
            model_witness: CircuitModelWitnessReport {
                original_model_vars: 3,
                gate_output_witnesses: 1,
                derivable_gate_output_vars: 1,
                acyclic_replay_order_len: 1,
                complete_original_model_vars: 3,
                ..CircuitModelWitnessReport::default()
            },
            ..CircuitScoutReport::default()
        };
        let authority_packet = produce_original_dimacs_sat_model_authority_packet(
            3,
            &clauses,
            &source_rows,
            "retained/circuit-authority.cnf",
            "retained/circuit-authority-model.stdout",
            vec![
                "ay".to_owned(),
                "check".to_owned(),
                "model".to_owned(),
                "retained/circuit-authority.cnf".to_owned(),
                "retained/circuit-authority-model.stdout".to_owned(),
                "--json".to_owned(),
            ],
            if checker_valid { 0 } else { 1 },
            retained_model_check_json(
                "retained/circuit-authority.cnf",
                "retained/circuit-authority-model.stdout",
                3,
                clauses.len(),
                checker_valid,
            ),
        )
        .expect("authority packet should bind retained checker output");

        (clauses, source_rows, report, authority_packet)
    }

    #[test]
    fn circuit_equiv_packet_copies_circuit_scout_without_authority() {
        let report = CircuitScoutReport {
            num_vars: 1013,
            num_clauses: 18_793,
            gate_and: 96,
            gate_xor: 401,
            gate_ite: 0,
            gate_equiv: 13,
            gates_total: 510,
            equivalence_classes: 6,
            equivalence_members: 19,
            structural_hash_groups: 2,
            structural_hash_opportunities: 2,
            half_adders: 63,
            full_adders: 13,
            adder_carry_links: 89,
            partial_product_ands: 2,
            multiplier_cones: 1,
            rejection: CircuitScoutRejection::None,
            model_witness: CircuitModelWitnessReport {
                original_model_vars: 1013,
                gate_output_witnesses: 510,
                and_output_witnesses: 96,
                xor_output_witnesses: 401,
                equiv_output_witnesses: 13,
                equivalence_alias_witnesses: 6,
                adder_sum_witnesses: 76,
                adder_carry_witnesses: 89,
                partial_product_witnesses: 2,
                partial_assignment_required_vars: 1011,
                derivable_gate_output_vars: 2,
                blocked_gate_output_vars: 508,
                complete_original_model_vars: 1013,
                ..CircuitModelWitnessReport::default()
            },
            ..CircuitScoutReport::default()
        };

        let packet = CircuitEquivPacket::for_circuit_multiplier22(&report);
        let counters = packet.counters();
        let circuit = packet.circuit.as_ref().expect("circuit snapshot");

        assert_eq!(
            packet.scoreboard_row,
            CircuitEquivScoreboardRow::CircuitMultiplier22
        );
        assert_eq!(packet.expected_status, CircuitEquivExpectedStatus::Sat);
        assert!(packet.authority_is_absent());
        assert_eq!(
            packet.model_obligation,
            CircuitEquivModelObligationStatus::PendingDirectAssignment
        );
        assert_eq!(
            packet.proof_obligation,
            CircuitEquivProofObligationStatus::NotRequiredForExpectedSat
        );
        assert_eq!(circuit.rejection, CircuitEquivCircuitRejection::None);
        assert_eq!(circuit.gate_xor, 401);
        assert_eq!(circuit.model_witness.blocked_gate_output_vars, 508);
        assert_eq!(counters.row_id, "Circuit_multiplier22");
        assert_eq!(counters.circuit_gate_output_witnesses, 510);
        assert_eq!(counters.circuit_equivalence_alias_witnesses, 6);
        assert_eq!(counters.missing_witness_copies, 0);
        assert_eq!(
            counters.model_obligation,
            CircuitEquivModelObligationStatus::PendingDirectAssignment
        );
        assert_eq!(
            counters.route_admission_status,
            CircuitEquivRouteAdmissionStatus::Blocked(
                CircuitEquivRouteAdmissionBlocker::ModelObligation(
                    CircuitEquivModelObligationStatus::PendingDirectAssignment
                )
            )
        );
        assert!(!counters.route_admission_status.is_admitted());
        assert!(!counters.route_admitted);
        assert!(!counters.result_authority);
    }

    #[test]
    fn circuit_equiv_packet_copies_fmla_witnesses_deterministically() {
        let scout = FmlaGuardedEquivScout {
            num_vars: 54_411,
            num_clauses: 437_952,
            onehot_groups: 7_770,
            onehot_width_hist: BTreeMap::from([(6, 7_770)]),
            onehot_variables: 27_195,
            guarded_equivalence_pairs: 155_520,
            guarded_equivalence_guards: 27_195,
            guarded_equivalence_guard_fanout_hist: BTreeMap::from([
                (1, 6_480),
                (2, 16_200),
                (6, 1_080),
                (12, 2_700),
                (36, 180),
                (72, 450),
                (216, 30),
                (432, 75),
            ]),
            rejection: FmlaGuardedEquivRejection::None,
        };
        let witnesses = FmlaGuardedEquivWitnesses {
            onehot_groups: vec![FmlaOneHotGroupWitness {
                support_clause_id: 1,
                vars: vec![1, 2, 3, 4, 5, 6],
                mutex_clause_ids: (2..=16).collect(),
            }],
            guarded_equivalences: vec![FmlaGuardedEquivalenceWitness {
                guard: 1,
                lhs: 7,
                rhs: 8,
                forward_clause_id: 17,
                reverse_clause_id: 18,
                forward_clause_lits: vec![-1, -7, 8],
                reverse_clause_lits: vec![-1, -8, 7],
            }],
        };

        let packet = CircuitEquivPacket::for_fmla_equiv_chain_4_6_6(&scout, Some(&witnesses));
        let fmla = packet.fmla.as_ref().expect("fmla snapshot");
        let counters = packet.counters();

        assert_eq!(
            packet.scoreboard_row,
            CircuitEquivScoreboardRow::FmlaEquivChain466
        );
        assert_eq!(packet.expected_status, CircuitEquivExpectedStatus::Unsat);
        assert!(packet.authority_is_absent());
        assert_eq!(
            packet.model_obligation,
            CircuitEquivModelObligationStatus::NotRequiredForExpectedUnsat
        );
        assert_eq!(
            packet.proof_obligation,
            CircuitEquivProofObligationStatus::PendingExternalChecker
        );
        assert_eq!(fmla.onehot_width_hist.get(&6), Some(&7_770));
        assert_eq!(fmla.onehot_group_witnesses[0].mutex_clause_ids.len(), 15);
        assert_eq!(
            fmla.guarded_equivalence_witnesses[0].forward_clause_lits,
            vec![-1, -7, 8]
        );
        assert_eq!(counters.row_id, "FmlaEquivChain_4_6_6");
        assert_eq!(counters.fmla_onehot_group_witnesses, 1);
        assert_eq!(counters.fmla_guarded_equivalence_witnesses, 1);
        assert_eq!(counters.missing_witness_copies, 0);
        assert_eq!(
            counters.proof_obligation,
            CircuitEquivProofObligationStatus::PendingExternalChecker
        );
        assert_eq!(
            counters.route_admission_status,
            CircuitEquivRouteAdmissionStatus::Blocked(
                CircuitEquivRouteAdmissionBlocker::ProofObligation(
                    CircuitEquivProofObligationStatus::PendingExternalChecker
                )
            )
        );
        assert!(!counters.route_admission_status.is_admitted());
    }

    #[test]
    fn circuit_equiv_packet_copies_source_frame_rows_without_materialization() {
        let report = CircuitScoutReport {
            num_vars: 2,
            num_clauses: 1,
            model_witness: CircuitModelWitnessReport {
                original_model_vars: 2,
                gate_output_witnesses: 1,
                ..CircuitModelWitnessReport::default()
            },
            ..CircuitScoutReport::default()
        };
        let rows = vec![CircuitSourceFrameRow {
            source_row_id: 42,
            var: 0,
            literal: Literal::positive(Variable::new(0)),
            clause_id: 0,
            source_value: true,
            family: CircuitSourceFrameFamily::W210Frontier,
            kind: CircuitSourceFrameKind::FrontierValue,
        }];
        let audit = CircuitSourceFrameAudit {
            rows_seen: 1,
            rows_accepted: 1,
            original_clauses_checked: 1,
            residual_clause_ids: vec![9, 11],
            ..CircuitSourceFrameAudit::default()
        };

        let packet = CircuitEquivPacket::for_circuit_multiplier22(&report)
            .with_source_frame_rows(&rows, &audit);
        let source_frame = packet.source_frame.as_ref().expect("source-frame snapshot");
        let counters = packet.counters();

        assert!(packet.authority_is_absent());
        assert_eq!(
            packet.model_obligation,
            CircuitEquivModelObligationStatus::SourceFrameIncomplete
        );
        assert_eq!(source_frame.rows.len(), 1);
        assert_eq!(source_frame.rows[0].source_row_id, 42);
        assert_eq!(source_frame.rows[0].literal_dimacs, 1);
        assert_eq!(
            source_frame.rows[0].family,
            CircuitEquivSourceFrameFamily::W210Frontier
        );
        assert_eq!(source_frame.audit.residual_clause_ids, vec![9, 11]);
        assert_eq!(counters.circuit_source_frame_rows, 1);
        assert!(!counters.result_authority);
    }

    #[test]
    fn circuit_equiv_packet_source_frame_validation_never_grants_authority() {
        let report = CircuitScoutReport {
            num_vars: 2,
            num_clauses: 1,
            model_witness: CircuitModelWitnessReport {
                original_model_vars: 2,
                gate_output_witnesses: 1,
                complete_original_model_vars: 2,
                ..CircuitModelWitnessReport::default()
            },
            ..CircuitScoutReport::default()
        };
        let rows = vec![CircuitSourceFrameRow {
            source_row_id: 7,
            var: 0,
            literal: Literal::positive(Variable::new(0)),
            clause_id: 0,
            source_value: true,
            family: CircuitSourceFrameFamily::W210Frontier,
            kind: CircuitSourceFrameKind::FrontierValue,
        }];
        let residual_audit = CircuitSourceFrameAudit {
            rows_seen: 1,
            rows_accepted: 1,
            original_clauses_checked: 1,
            residual_falsified_count: 1,
            first_residual_clause: Some(0),
            residual_clause_ids: vec![0],
            assignment_complete: true,
            validation_passed: false,
            ..CircuitSourceFrameAudit::default()
        };

        let residual_packet = CircuitEquivPacket::for_circuit_multiplier22(&report)
            .with_source_frame_rows(&rows, &residual_audit);

        assert_eq!(
            residual_packet.model_obligation,
            CircuitEquivModelObligationStatus::SourceFrameResidualNonZero
        );
        assert!(residual_packet.authority_is_absent());

        let validated_audit = CircuitSourceFrameAudit {
            rows_seen: 1,
            rows_accepted: 1,
            original_clauses_checked: 1,
            assignment_complete: true,
            validation_passed: true,
            ..CircuitSourceFrameAudit::default()
        };
        let validated_packet = CircuitEquivPacket::for_circuit_multiplier22(&report)
            .with_source_frame_rows(&rows, &validated_audit);

        assert_eq!(
            validated_packet.model_obligation,
            CircuitEquivModelObligationStatus::OriginalDimacsValidated
        );
        assert!(validated_packet.authority_is_absent());
        assert_eq!(
            validated_packet.route_admission_status(),
            CircuitEquivRouteAdmissionStatus::Blocked(
                CircuitEquivRouteAdmissionBlocker::MissingOriginalDimacsModel
            )
        );
        assert!(!validated_packet.route_admitted);
        assert!(!validated_packet.sat_output_authority);
        assert!(!validated_packet.model_output_authority);
        assert!(!validated_packet.proof_output_authority);
        assert!(!validated_packet.result_authority);
    }

    #[test]
    fn circuit_equiv_packet_copies_w210_value_ledger_residual_without_authority() {
        let report = CircuitScoutReport {
            num_vars: 1013,
            num_clauses: 18_793,
            model_witness: CircuitModelWitnessReport {
                original_model_vars: 1013,
                gate_output_witnesses: 510,
                complete_original_model_vars: 1013,
                ..CircuitModelWitnessReport::default()
            },
            ..CircuitScoutReport::default()
        };
        let frontier = parsed_w210_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(1, 0, true), (2, 1, false)],
            503,
            503,
        );
        let scc_choice = parsed_w210_ledger(
            CircuitSourceFrameValueLedgerKind::W210SccChoice,
            &[(1, 2, true)],
            379,
            379,
        );
        let forced_gate = parsed_w210_ledger(
            CircuitSourceFrameValueLedgerKind::W210ForcedGate,
            &[(1, 3, false)],
            131,
            131,
        );
        let audit = CircuitW210ValueLedgerAudit {
            rows_seen: 1013,
            rows_accepted: 1013,
            covered_vars: 1013,
            missing_vars: 0,
            original_clauses_checked: 18_793,
            residual_falsified_count: 8,
            first_residual_clause: Some(1014),
            residual_clause_ids: vec![1014, 5649, 6506, 10594, 13397, 17195, 17522, 18400],
            assignment_complete: true,
            validation_passed: false,
            ..CircuitW210ValueLedgerAudit::default()
        };

        let packet = CircuitEquivPacket::for_circuit_multiplier22(&report)
            .with_w210_value_ledger_audit(&frontier, &scc_choice, &forced_gate, &audit);
        let w210 = packet
            .w210_value_ledger
            .as_ref()
            .expect("W210 value-ledger snapshot");
        let counters = packet.counters();

        assert!(packet.authority_is_absent());
        assert_eq!(
            packet.model_obligation,
            CircuitEquivModelObligationStatus::SourceFrameResidualNonZero
        );
        assert_eq!(
            counters.route_admission_status,
            CircuitEquivRouteAdmissionStatus::Blocked(
                CircuitEquivRouteAdmissionBlocker::ModelObligation(
                    CircuitEquivModelObligationStatus::SourceFrameResidualNonZero
                )
            )
        );
        assert_eq!(
            w210.frontier.kind,
            CircuitEquivW210ValueLedgerKind::Frontier
        );
        assert_eq!(w210.frontier.rows_seen, 503);
        assert_eq!(w210.scc_choice.rows_seen, 379);
        assert_eq!(w210.forced_gate.rows_seen, 131);
        assert_eq!(w210.audit.rows_seen, 1013);
        assert_eq!(w210.audit.rows_accepted, 1013);
        assert_eq!(w210.audit.covered_vars, 1013);
        assert_eq!(w210.audit.original_clauses_checked, 18_793);
        assert_eq!(w210.audit.residual_falsified_count, 8);
        assert_eq!(
            w210.audit.residual_clause_ids,
            vec![1014, 5649, 6506, 10594, 13397, 17195, 17522, 18400]
        );
        assert_eq!(counters.circuit_w210_value_ledger_rows, 1013);
        assert_eq!(
            counters.circuit_w210_value_ledger_residual_falsified_count,
            8
        );
        assert!(counters.circuit_w210_value_ledger_assignment_complete);
        assert!(!counters.circuit_w210_value_ledger_validation_passed);
        assert!(!packet.route_admitted);
        assert!(!packet.sat_output_authority);
        assert!(!packet.model_output_authority);
        assert!(!packet.proof_output_authority);
        assert!(!packet.result_authority);
    }

    #[test]
    fn circuit_equiv_packet_w210_validation_still_never_grants_authority() {
        let report = CircuitScoutReport {
            num_vars: 1,
            num_clauses: 1,
            model_witness: CircuitModelWitnessReport {
                original_model_vars: 1,
                complete_original_model_vars: 1,
                ..CircuitModelWitnessReport::default()
            },
            ..CircuitScoutReport::default()
        };
        let frontier = parsed_w210_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(1, 0, true)],
            1,
            1,
        );
        let scc_choice =
            parsed_w210_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[], 0, 0);
        let forced_gate =
            parsed_w210_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[], 0, 0);
        let validated_audit = CircuitW210ValueLedgerAudit {
            rows_seen: 1,
            rows_accepted: 1,
            covered_vars: 1,
            original_clauses_checked: 1,
            assignment_complete: true,
            validation_passed: true,
            ..CircuitW210ValueLedgerAudit::default()
        };

        let packet = CircuitEquivPacket::for_circuit_multiplier22(&report)
            .with_w210_value_ledger_audit(&frontier, &scc_choice, &forced_gate, &validated_audit);

        assert_eq!(
            packet.model_obligation,
            CircuitEquivModelObligationStatus::OriginalDimacsValidated
        );
        assert!(packet.authority_is_absent());
        assert_eq!(
            packet.route_admission_status(),
            CircuitEquivRouteAdmissionStatus::Blocked(
                CircuitEquivRouteAdmissionBlocker::MissingOriginalDimacsModel
            )
        );
        assert!(!packet.route_admitted);
        assert!(!packet.result_authority);
        assert!(!packet.model_output_authority);
        assert!(!packet.sat_output_authority);
        assert!(!packet.proof_output_authority);
    }

    #[test]
    fn circuit_equiv_packet_partial_authority_bits_remain_inconsistent() {
        let report = CircuitScoutReport {
            num_vars: 1,
            num_clauses: 1,
            model_witness: CircuitModelWitnessReport {
                original_model_vars: 1,
                complete_original_model_vars: 1,
                ..CircuitModelWitnessReport::default()
            },
            ..CircuitScoutReport::default()
        };
        let frontier = parsed_w210_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(1, 0, true)],
            1,
            1,
        );
        let scc_choice =
            parsed_w210_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[], 0, 0);
        let forced_gate =
            parsed_w210_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[], 0, 0);
        let validated_audit = CircuitW210ValueLedgerAudit {
            rows_seen: 1,
            rows_accepted: 1,
            covered_vars: 1,
            original_clauses_checked: 1,
            assignment_complete: true,
            validation_passed: true,
            ..CircuitW210ValueLedgerAudit::default()
        };

        let mut packet = CircuitEquivPacket::for_circuit_multiplier22(&report)
            .with_w210_value_ledger_audit(&frontier, &scc_choice, &forced_gate, &validated_audit);

        packet.route_admitted = true;
        packet.result_authority = true;
        packet.sat_output_authority = true;

        assert_eq!(
            packet.model_obligation,
            CircuitEquivModelObligationStatus::OriginalDimacsValidated
        );
        assert_eq!(
            packet.route_admission_status(),
            CircuitEquivRouteAdmissionStatus::Blocked(
                CircuitEquivRouteAdmissionBlocker::MissingOriginalDimacsModel
            )
        );
        assert!(!packet.route_admission_status().is_admitted());
        assert!(!packet.model_output_authority);
        assert!(!packet.proof_output_authority);
    }

    #[test]
    fn circuit_equiv_packet_original_model_payload_is_checked_before_authority() {
        let report = CircuitScoutReport {
            num_vars: 1,
            num_clauses: 1,
            model_witness: CircuitModelWitnessReport {
                original_model_vars: 1,
                complete_original_model_vars: 1,
                ..CircuitModelWitnessReport::default()
            },
            ..CircuitScoutReport::default()
        };
        let frontier = parsed_w210_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(1, 0, true)],
            1,
            1,
        );
        let scc_choice =
            parsed_w210_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[], 0, 0);
        let forced_gate =
            parsed_w210_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[], 0, 0);
        let validated_audit = CircuitW210ValueLedgerAudit {
            rows_seen: 1,
            rows_accepted: 1,
            covered_vars: 1,
            original_clauses_checked: 1,
            assignment_complete: true,
            validation_passed: true,
            ..CircuitW210ValueLedgerAudit::default()
        };
        let clauses = vec![vec![Literal::positive(Variable::new(0))]];
        let packet = CircuitEquivPacket::for_circuit_multiplier22(&report)
            .with_w210_value_ledger_audit(&frontier, &scc_choice, &forced_gate, &validated_audit);

        assert_eq!(
            packet
                .clone()
                .with_original_dimacs_model(1, &clauses, &[false]),
            Err(CircuitModelValidationError::UnsatisfiedClause { clause_index: 0 })
        );

        let mut certified_packet = packet
            .with_original_dimacs_model(1, &clauses, &[true])
            .expect("model should satisfy original DIMACS");
        let counters = certified_packet.counters();
        let model = certified_packet
            .original_dimacs_model
            .as_ref()
            .expect("validated model payload");

        assert_eq!(model.original_model_vars, 1);
        assert_eq!(model.original_clauses_checked, 1);
        assert_eq!(model.assignment, vec![true]);
        assert!(counters.circuit_original_dimacs_model_present);
        assert_eq!(counters.circuit_original_dimacs_model_vars, 1);
        assert_eq!(
            certified_packet.route_admission_status(),
            CircuitEquivRouteAdmissionStatus::Blocked(
                CircuitEquivRouteAdmissionBlocker::AuthorityAbsent
            )
        );

        certified_packet.route_admitted = true;
        certified_packet.result_authority = true;
        certified_packet.sat_output_authority = true;

        assert_eq!(
            certified_packet.route_admission_status(),
            CircuitEquivRouteAdmissionStatus::Blocked(
                CircuitEquivRouteAdmissionBlocker::AuthorityInconsistent
            )
        );
        assert!(!certified_packet.model_output_authority);
        assert!(!certified_packet.route_admission_status().is_admitted());
    }

    #[test]
    fn circuit_equiv_packet_accepts_real_materialized_source_frame_model_only_as_payload() {
        let out = Variable::new(2);
        let a = Variable::new(0);
        let b = Variable::new(1);
        let clauses = vec![
            vec![Literal::negative(out), Literal::positive(a)],
            vec![Literal::negative(out), Literal::positive(b)],
            vec![
                Literal::positive(out),
                Literal::negative(a),
                Literal::negative(b),
            ],
        ];
        let source_rows = vec![
            CircuitSourceFrameRow {
                source_row_id: 10,
                var: 0,
                literal: Literal::positive(a),
                clause_id: 0,
                source_value: true,
                family: CircuitSourceFrameFamily::W210Frontier,
                kind: CircuitSourceFrameKind::FrontierValue,
            },
            CircuitSourceFrameRow {
                source_row_id: 11,
                var: 1,
                literal: Literal::positive(b),
                clause_id: 1,
                source_value: false,
                family: CircuitSourceFrameFamily::ForcedGateReplayBridge,
                kind: CircuitSourceFrameKind::ForcedGateReplayBridge,
            },
        ];
        let materialized = materialize_original_dimacs_assignment_from_source_frame_rows(
            3,
            &clauses,
            &source_rows,
        )
        .expect("source-frame rows should replay and validate the original DIMACS model");
        let report = CircuitScoutReport {
            num_vars: 3,
            num_clauses: clauses.len(),
            model_witness: CircuitModelWitnessReport {
                original_model_vars: 3,
                gate_output_witnesses: 1,
                derivable_gate_output_vars: 1,
                acyclic_replay_order_len: 1,
                complete_original_model_vars: 3,
                ..CircuitModelWitnessReport::default()
            },
            ..CircuitScoutReport::default()
        };

        let packet = CircuitEquivPacket::for_circuit_multiplier22(&report)
            .with_materialized_source_frame_model(&source_rows, &materialized, 3, &clauses)
            .expect("materialized assignment should pass the packet payload gate");
        let counters = packet.counters();
        let model = packet
            .original_dimacs_model
            .as_ref()
            .expect("validated original-DIMACS payload");

        assert_eq!(materialized.assignment, vec![true, false, false]);
        assert_eq!(
            packet.model_obligation,
            CircuitEquivModelObligationStatus::OriginalDimacsValidated
        );
        assert_eq!(model.original_model_vars, 3);
        assert_eq!(model.original_clauses_checked, clauses.len());
        assert_eq!(model.assignment, materialized.assignment);
        assert!(counters.circuit_original_dimacs_model_present);
        assert_eq!(counters.circuit_original_dimacs_model_vars, 3);
        assert_eq!(
            packet.route_admission_status(),
            CircuitEquivRouteAdmissionStatus::Blocked(
                CircuitEquivRouteAdmissionBlocker::AuthorityAbsent
            )
        );
        assert!(packet.authority_is_absent());
        assert!(!packet.route_admitted);
        assert!(!packet.result_authority);
        assert!(!packet.sat_output_authority);
        assert!(!packet.model_output_authority);
        assert!(!packet.proof_output_authority);
    }

    #[test]
    fn circuit_equiv_packet_authority_facade_admits_retained_checker_backed_model() {
        let (clauses, source_rows, report, authority_packet) =
            circuit_multiplier22_authority_fixture(true);

        let decision = circuit_multiplier22_original_dimacs_sat_model_authority_decision(
            &report,
            3,
            &clauses,
            &source_rows,
            authority_packet,
        );

        assert!(decision.is_admitted());
        match decision {
            CircuitEquivOriginalDimacsSatModelAuthorityDecision::Admitted {
                assignment,
                counters,
            } => {
                assert_eq!(assignment, vec![true, false, false]);
                assert_eq!(counters.circuit_source_frame_rows, 2);
                assert!(counters.circuit_original_dimacs_model_present);
                assert_eq!(counters.circuit_original_dimacs_model_vars, 3);
                assert_eq!(
                    counters.model_obligation,
                    CircuitEquivModelObligationStatus::OriginalDimacsValidated
                );
                assert_eq!(
                    counters.route_admission_status,
                    CircuitEquivRouteAdmissionStatus::Admitted
                );
                assert!(counters.route_admitted);
                assert!(counters.result_authority);
            }
            CircuitEquivOriginalDimacsSatModelAuthorityDecision::Blocked { .. } => {
                panic!("retained checker-backed model should admit")
            }
        }
    }

    #[test]
    fn circuit_equiv_packet_authority_facade_blocks_invalid_checker_evidence() {
        let (clauses, source_rows, report, authority_packet) =
            circuit_multiplier22_authority_fixture(false);

        let decision = circuit_multiplier22_original_dimacs_sat_model_authority_decision(
            &report,
            3,
            &clauses,
            &source_rows,
            authority_packet,
        );

        assert!(!decision.is_admitted());
        assert_eq!(decision.counters().circuit_source_frame_rows, 2);
        match decision {
            CircuitEquivOriginalDimacsSatModelAuthorityDecision::Blocked {
                authority_status,
                route_admission_status,
                counters,
            } => {
                assert!(!authority_status.is_admitted());
                assert_eq!(
                    route_admission_status,
                    CircuitEquivRouteAdmissionStatus::Blocked(
                        CircuitEquivRouteAdmissionBlocker::MissingOriginalDimacsModel
                    )
                );
                assert!(!counters.circuit_original_dimacs_model_present);
                assert!(!counters.route_admitted);
                assert!(!counters.result_authority);
            }
            CircuitEquivOriginalDimacsSatModelAuthorityDecision::Admitted { .. } => {
                panic!("invalid retained checker evidence must stay blocked")
            }
        }
    }

    #[test]
    fn circuit_equiv_packet_authority_facade_blocks_source_frame_residual() {
        let (clauses, mut source_rows, report, authority_packet) =
            circuit_multiplier22_authority_fixture(true);
        source_rows[1].source_value = true;
        source_rows.push(CircuitSourceFrameRow {
            source_row_id: 12,
            var: 2,
            literal: Literal::negative(Variable::new(2)),
            clause_id: 0,
            source_value: false,
            family: CircuitSourceFrameFamily::ForcedGateReplayBridge,
            kind: CircuitSourceFrameKind::ForcedGateReplayBridge,
        });

        let decision = circuit_multiplier22_original_dimacs_sat_model_authority_decision(
            &report,
            3,
            &clauses,
            &source_rows,
            authority_packet,
        );

        assert!(!decision.is_admitted());
        match decision {
            CircuitEquivOriginalDimacsSatModelAuthorityDecision::Blocked {
                authority_status,
                route_admission_status,
                counters,
            } => {
                assert!(!authority_status.is_admitted());
                assert_eq!(counters.circuit_source_frame_rows, 3);
                assert!(!counters.circuit_original_dimacs_model_present);
                assert_eq!(
                    counters.model_obligation,
                    CircuitEquivModelObligationStatus::SourceFrameResidualNonZero
                );
                assert_eq!(
                    route_admission_status,
                    CircuitEquivRouteAdmissionStatus::Blocked(
                        CircuitEquivRouteAdmissionBlocker::ModelObligation(
                            CircuitEquivModelObligationStatus::SourceFrameResidualNonZero
                        )
                    )
                );
            }
            CircuitEquivOriginalDimacsSatModelAuthorityDecision::Admitted { .. } => {
                panic!("residual source-frame rows must stay blocked")
            }
        }
    }

    #[test]
    fn circuit_equiv_packet_binds_artifact_backed_sat_model_authority() {
        let out = Variable::new(2);
        let a = Variable::new(0);
        let b = Variable::new(1);
        let clauses = vec![
            vec![Literal::negative(out), Literal::positive(a)],
            vec![Literal::negative(out), Literal::positive(b)],
            vec![
                Literal::positive(out),
                Literal::negative(a),
                Literal::negative(b),
            ],
        ];
        let source_rows = vec![
            CircuitSourceFrameRow {
                source_row_id: 10,
                var: 0,
                literal: Literal::positive(a),
                clause_id: 0,
                source_value: true,
                family: CircuitSourceFrameFamily::W210Frontier,
                kind: CircuitSourceFrameKind::FrontierValue,
            },
            CircuitSourceFrameRow {
                source_row_id: 11,
                var: 1,
                literal: Literal::positive(b),
                clause_id: 1,
                source_value: false,
                family: CircuitSourceFrameFamily::ForcedGateReplayBridge,
                kind: CircuitSourceFrameKind::ForcedGateReplayBridge,
            },
        ];
        let report = CircuitScoutReport {
            num_vars: 3,
            num_clauses: clauses.len(),
            model_witness: CircuitModelWitnessReport {
                original_model_vars: 3,
                gate_output_witnesses: 1,
                derivable_gate_output_vars: 1,
                acyclic_replay_order_len: 1,
                complete_original_model_vars: 3,
                ..CircuitModelWitnessReport::default()
            },
            ..CircuitScoutReport::default()
        };
        let authority_packet = produce_original_dimacs_sat_model_authority_packet(
            3,
            &clauses,
            &source_rows,
            "retained/circuit-authority.cnf",
            "retained/circuit-authority-model.stdout",
            vec![
                "ay".to_owned(),
                "check".to_owned(),
                "model".to_owned(),
                "retained/circuit-authority.cnf".to_owned(),
                "retained/circuit-authority-model.stdout".to_owned(),
                "--json".to_owned(),
            ],
            0,
            retained_model_check_json(
                "retained/circuit-authority.cnf",
                "retained/circuit-authority-model.stdout",
                3,
                clauses.len(),
                true,
            ),
        )
        .expect("authority packet should be retained and checker-bound");
        let audit = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&authority_packet.artifacts),
            Some(&authority_packet.checker_evidence),
        );

        assert!(audit.authority_status.is_admitted());
        let packet = CircuitEquivPacket::for_circuit_multiplier22(&report)
            .with_original_dimacs_sat_model_authority_audit(&audit);
        let model = packet
            .original_dimacs_model
            .as_ref()
            .expect("artifact-backed original model");

        assert_eq!(
            packet.model_obligation,
            CircuitEquivModelObligationStatus::OriginalDimacsValidated
        );
        assert_eq!(model.assignment, vec![true, false, false]);
        assert_eq!(model.original_model_vars, 3);
        assert_eq!(model.original_clauses_checked, clauses.len());
        assert_eq!(
            packet.route_admission_status(),
            CircuitEquivRouteAdmissionStatus::Admitted
        );
        assert!(packet.route_admitted);
        assert!(packet.result_authority);
        assert!(packet.sat_output_authority);
        assert!(packet.model_output_authority);
        assert!(!packet.unsat_output_authority);
        assert!(!packet.proof_output_authority);
    }

    #[test]
    fn circuit_equiv_packet_rejects_sat_model_authority_without_checker_acceptance() {
        let out = Variable::new(2);
        let a = Variable::new(0);
        let b = Variable::new(1);
        let clauses = vec![
            vec![Literal::negative(out), Literal::positive(a)],
            vec![Literal::negative(out), Literal::positive(b)],
            vec![
                Literal::positive(out),
                Literal::negative(a),
                Literal::negative(b),
            ],
        ];
        let source_rows = vec![
            CircuitSourceFrameRow {
                source_row_id: 10,
                var: 0,
                literal: Literal::positive(a),
                clause_id: 0,
                source_value: true,
                family: CircuitSourceFrameFamily::W210Frontier,
                kind: CircuitSourceFrameKind::FrontierValue,
            },
            CircuitSourceFrameRow {
                source_row_id: 11,
                var: 1,
                literal: Literal::positive(b),
                clause_id: 1,
                source_value: false,
                family: CircuitSourceFrameFamily::ForcedGateReplayBridge,
                kind: CircuitSourceFrameKind::ForcedGateReplayBridge,
            },
        ];
        let report = CircuitScoutReport {
            num_vars: 3,
            num_clauses: clauses.len(),
            model_witness: CircuitModelWitnessReport {
                original_model_vars: 3,
                complete_original_model_vars: 3,
                ..CircuitModelWitnessReport::default()
            },
            ..CircuitScoutReport::default()
        };
        let authority_packet = produce_original_dimacs_sat_model_authority_packet(
            3,
            &clauses,
            &source_rows,
            "retained/circuit-authority.cnf",
            "retained/circuit-authority-model.stdout",
            vec![
                "ay".to_owned(),
                "check".to_owned(),
                "model".to_owned(),
                "retained/circuit-authority.cnf".to_owned(),
                "retained/circuit-authority-model.stdout".to_owned(),
                "--json".to_owned(),
            ],
            0,
            retained_model_check_json(
                "retained/circuit-authority.cnf",
                "retained/circuit-authority-model.stdout",
                3,
                clauses.len(),
                false,
            ),
        )
        .expect("invalid checker verdict should still bind as retained evidence");
        let audit = audit_original_dimacs_sat_model_authority(
            3,
            &clauses,
            &source_rows,
            Some(&authority_packet.artifacts),
            Some(&authority_packet.checker_evidence),
        );

        assert!(!audit.authority_status.is_admitted());
        let packet = CircuitEquivPacket::for_circuit_multiplier22(&report)
            .with_original_dimacs_sat_model_authority_audit(&audit);

        assert!(packet.authority_is_absent());
        assert!(packet.original_dimacs_model.is_none());
        assert_eq!(
            packet.route_admission_status(),
            CircuitEquivRouteAdmissionStatus::Blocked(
                CircuitEquivRouteAdmissionBlocker::ModelObligation(
                    CircuitEquivModelObligationStatus::PendingOriginalDimacsValidation
                )
            )
        );
    }

    #[test]
    fn circuit_equiv_packet_validated_w210_does_not_mask_source_frame_rejection() {
        let report = CircuitScoutReport {
            num_vars: 1,
            num_clauses: 1,
            model_witness: CircuitModelWitnessReport {
                original_model_vars: 1,
                complete_original_model_vars: 1,
                ..CircuitModelWitnessReport::default()
            },
            ..CircuitScoutReport::default()
        };
        let rows = vec![CircuitSourceFrameRow {
            source_row_id: 9,
            var: 0,
            literal: Literal::positive(Variable::new(0)),
            clause_id: 0,
            source_value: true,
            family: CircuitSourceFrameFamily::W210Frontier,
            kind: CircuitSourceFrameKind::FrontierValue,
        }];
        let rejected_source_audit = CircuitSourceFrameAudit {
            rows_seen: 1,
            rows_accepted: 1,
            conflicts: 1,
            assignment_complete: true,
            validation_passed: false,
            ..CircuitSourceFrameAudit::default()
        };
        let frontier = parsed_w210_ledger(
            CircuitSourceFrameValueLedgerKind::W210Frontier,
            &[(1, 0, true)],
            1,
            1,
        );
        let scc_choice =
            parsed_w210_ledger(CircuitSourceFrameValueLedgerKind::W210SccChoice, &[], 0, 0);
        let forced_gate =
            parsed_w210_ledger(CircuitSourceFrameValueLedgerKind::W210ForcedGate, &[], 0, 0);
        let validated_w210_audit = CircuitW210ValueLedgerAudit {
            rows_seen: 1,
            rows_accepted: 1,
            covered_vars: 1,
            assignment_complete: true,
            validation_passed: true,
            ..CircuitW210ValueLedgerAudit::default()
        };

        let packet = CircuitEquivPacket::for_circuit_multiplier22(&report)
            .with_w210_value_ledger_audit(
                &frontier,
                &scc_choice,
                &forced_gate,
                &validated_w210_audit,
            )
            .with_source_frame_rows(&rows, &rejected_source_audit);

        assert_eq!(
            packet.model_obligation,
            CircuitEquivModelObligationStatus::SourceFrameRejected
        );
        assert!(packet.authority_is_absent());
    }

    fn parse_w210_fixture(
        kind: CircuitSourceFrameValueLedgerKind,
        repo_relative: &str,
    ) -> CircuitParsedSourceFrameValueLedger {
        parse_w210_source_frame_value_ledger(1_013, kind, &report_text(repo_relative))
            .unwrap_or_else(|err| panic!("failed to parse {repo_relative}: {err:?}"))
    }

    fn report_text(repo_relative: &str) -> String {
        let path = repo_root().join(repo_relative);
        std::fs::read_to_string(&path)
            .unwrap_or_else(|err| panic!("failed to read {}: {err}", path.display()))
    }

    fn decompress_required_benchmark(repo_relative: &str) -> String {
        crate::test_xz::decompress_required_repo_xz(repo_relative)
    }

    fn repo_root() -> PathBuf {
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
    }

    fn parsed_w210_ledger(
        kind: CircuitSourceFrameValueLedgerKind,
        rows: &[(u64, usize, bool)],
        stats_rows_seen: usize,
        stats_rows_accepted: usize,
    ) -> CircuitParsedSourceFrameValueLedger {
        let row_prefix = match kind {
            CircuitSourceFrameValueLedgerKind::W210Frontier => "w210_frontier_value_",
            CircuitSourceFrameValueLedgerKind::W210SccChoice => "w210_scc_choice_value_",
            CircuitSourceFrameValueLedgerKind::W210ForcedGate => "w210_forced_gate_value_",
        };
        let family = match kind {
            CircuitSourceFrameValueLedgerKind::W210Frontier => {
                CircuitSourceFrameFamily::W210Frontier
            }
            CircuitSourceFrameValueLedgerKind::W210SccChoice => {
                CircuitSourceFrameFamily::W210SccChoice
            }
            CircuitSourceFrameValueLedgerKind::W210ForcedGate => {
                CircuitSourceFrameFamily::ForcedGateReplayBridge
            }
        };
        let rows: Vec<_> = rows
            .iter()
            .map(
                |&(source_row_id, var, value)| CircuitSourceFrameValueLedgerRow {
                    source_row_id,
                    ledger_row_id: format!("{row_prefix}{source_row_id}"),
                    value: CircuitSourceFrameValue { var, value, family },
                    present_in_w159_remaining_clause: false,
                    remaining_clause_ids_1_based: Vec::new(),
                    route_eligible: false,
                    route_blocker: Some("original_dimacs_validation_failed".to_string()),
                },
            )
            .collect();
        CircuitParsedSourceFrameValueLedger {
            kind,
            stats: CircuitSourceFrameValueLedgerStats {
                rows_seen: stats_rows_seen,
                rows_accepted: stats_rows_accepted,
                route_blocked_rows: stats_rows_accepted,
                max_original_var_1_based: rows
                    .iter()
                    .map(|row| row.value.var + 1)
                    .max()
                    .unwrap_or(0),
                ..CircuitSourceFrameValueLedgerStats::default()
            },
            rows,
        }
    }
}
