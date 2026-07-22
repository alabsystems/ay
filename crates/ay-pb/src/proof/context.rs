// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! State skeleton for PB proof-mode bookkeeping.

use std::{collections::BTreeSet as HashSet, error::Error, fmt};

use super::{ConstraintId, ProofConclusionKind};

/// Imported proof row IDs associated with one parsed PB input row.
///
/// Most input rows import as one VeriPB row. Equality rows may import as two
/// rows, so the skeleton keeps the optional split row without committing the
/// solver to a proof encoding path yet.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InputRowIds {
    primary: ConstraintId,
    split: Option<ConstraintId>,
}

impl InputRowIds {
    /// Records an input row imported as a single proof row.
    pub const fn single(primary: ConstraintId) -> Self {
        Self {
            primary,
            split: None,
        }
    }

    /// Records an input row imported as two proof rows.
    pub const fn split(primary: ConstraintId, split: ConstraintId) -> Self {
        Self {
            primary,
            split: Some(split),
        }
    }

    /// Returns the primary imported proof row ID.
    pub const fn primary(&self) -> ConstraintId {
        self.primary
    }

    /// Returns the optional second imported proof row ID.
    pub const fn split_row(&self) -> Option<ConstraintId> {
        self.split
    }

    /// Returns the number of proof rows imported for this input row.
    pub const fn len(&self) -> usize {
        if self.split.is_some() {
            2
        } else {
            1
        }
    }

    /// Returns true if this input row did not import any proof rows.
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// Iterates over the imported proof row IDs for this input row.
    pub fn ids(&self) -> impl Iterator<Item = ConstraintId> + '_ {
        [Some(self.primary), self.split].into_iter().flatten()
    }
}

/// Relation as it appeared in the source PB input before canonicalization.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum SourceRelation {
    /// Greater-than-or-equal (`>=`).
    GreaterEqual,
    /// Equality (`=`).
    Equal,
    /// Less-than-or-equal (`<=`).
    LessEqual,
}

impl SourceRelation {
    /// Returns the source spelling of this relation.
    pub const fn symbol(self) -> &'static str {
        match self {
            Self::GreaterEqual => ">=",
            Self::Equal => "=",
            Self::LessEqual => "<=",
        }
    }

    /// Returns the current proof support for this source relation.
    pub const fn proof_support(self) -> SourceRelationProofSupport {
        match self {
            Self::GreaterEqual | Self::Equal | Self::LessEqual => {
                SourceRelationProofSupport::Supported
            }
        }
    }
}

impl fmt::Display for SourceRelation {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.symbol())
    }
}

/// Proof support classification for an input source relation.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum SourceRelationProofSupport {
    /// The relation has a proof-safe import path in the skeleton.
    Supported,
    /// The source relation must fail closed until its import path is proof-safe.
    UnsupportedSourceRelation,
    /// The source/projection path must fail closed until its proof obligations are certified.
    UnsupportedProjection,
}

impl SourceRelationProofSupport {
    /// Returns true if this support marker allows proof mode to continue.
    pub const fn is_supported(self) -> bool {
        matches!(self, Self::Supported)
    }

    /// Returns true if this support marker requires proof mode to fail closed.
    pub const fn is_unsupported(self) -> bool {
        !self.is_supported()
    }
}

/// State marker tying a source relation to its proof support.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct SourceRelationProofMarker {
    relation: SourceRelation,
    proof_support: SourceRelationProofSupport,
}

impl SourceRelationProofMarker {
    /// Creates a marker for a source relation.
    pub const fn new(relation: SourceRelation) -> Self {
        Self {
            relation,
            proof_support: relation.proof_support(),
        }
    }

    /// Creates a marker with an explicit proof support classification.
    pub const fn with_proof_support(
        relation: SourceRelation,
        proof_support: SourceRelationProofSupport,
    ) -> Self {
        Self {
            relation,
            proof_support,
        }
    }

    /// Returns the marked source relation.
    pub const fn relation(&self) -> SourceRelation {
        self.relation
    }

    /// Returns the proof support classification for the relation.
    pub const fn proof_support(&self) -> SourceRelationProofSupport {
        self.proof_support
    }

    /// Returns true if proof mode can proceed with this source relation.
    pub const fn is_proof_supported(&self) -> bool {
        self.proof_support.is_supported()
    }

    /// Returns a fail-closed reason when this source relation is unsupported.
    pub fn unsupported_fail_closed_reason(&self) -> Option<FailClosedReason> {
        match self.proof_support {
            SourceRelationProofSupport::Supported => None,
            SourceRelationProofSupport::UnsupportedSourceRelation => {
                Some(FailClosedReason::UnsupportedSourceRelation(self.relation))
            }
            SourceRelationProofSupport::UnsupportedProjection => {
                Some(FailClosedReason::UnsupportedProjection(self.relation))
            }
        }
    }
}

/// Objective proof state tracked separately from the final proof conclusion.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub enum ObjectiveProofState {
    /// No optimization objective is active.
    #[default]
    None,
    /// An objective is active, optionally tied to a proof row.
    Active { row_id: Option<ConstraintId> },
    /// Concrete lower and upper objective bounds have been established.
    Bounds { lower: i128, upper: i128 },
    /// The objective has been proven infeasible.
    Infeasible,
}

/// Terminal proof state for a context.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ProofConclusionState {
    /// Proof logging is still open.
    #[default]
    Open,
    /// Proof logging reached a final conclusion.
    Concluded(ProofConclusionKind),
}

/// Reason proof mode failed closed before producing a trusted proof.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FailClosedReason {
    /// A source relation does not have a proof-safe import path yet.
    UnsupportedSourceRelation(SourceRelation),
    /// A source/projection path does not have certified proof obligations yet.
    UnsupportedProjection(SourceRelation),
    /// A proof obligation reached an implementation path that is not proof-safe.
    UnsupportedFeature(String),
    /// The proof context observed inconsistent row or objective state.
    InvalidState(String),
    /// Emitting or persisting proof output failed.
    ProofEmissionFailed(String),
    /// No more non-zero proof row IDs can be allocated.
    RowIdOverflow,
}

impl fmt::Display for FailClosedReason {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::UnsupportedSourceRelation(relation) => {
                write!(
                    formatter,
                    "unsupported source relation for proof mode: {relation}"
                )
            }
            Self::UnsupportedProjection(relation) => {
                write!(
                    formatter,
                    "unsupported source projection for proof mode: {relation}"
                )
            }
            Self::UnsupportedFeature(feature) => {
                write!(formatter, "unsupported proof feature: {feature}")
            }
            Self::InvalidState(detail) => write!(formatter, "invalid proof state: {detail}"),
            Self::ProofEmissionFailed(detail) => {
                write!(formatter, "proof emission failed: {detail}")
            }
            Self::RowIdOverflow => formatter.write_str("proof row ID space exhausted"),
        }
    }
}

/// Errors produced by [`ProofContext`] state transitions.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofContextError {
    /// An input row ID was listed more than once.
    DuplicateInputRowId(ConstraintId),
    /// No more non-zero proof row IDs can be allocated.
    ConstraintIdOverflow,
    /// The objective bounds are inconsistent.
    InvalidObjectiveBounds { lower: i128, upper: i128 },
    /// The proof context observed inconsistent row or objective state.
    InvalidState(String),
    /// The context has already reached a terminal proof conclusion.
    AlreadyConcluded(ProofConclusionKind),
    /// The context has already failed closed.
    FailedClosed(FailClosedReason),
}

impl fmt::Display for ProofContextError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateInputRowId(id) => write!(formatter, "duplicate input proof row ID {id}"),
            Self::ConstraintIdOverflow => formatter.write_str("proof row ID space exhausted"),
            Self::InvalidObjectiveBounds { lower, upper } => write!(
                formatter,
                "invalid objective bounds: lower bound {lower} exceeds upper bound {upper}"
            ),
            Self::InvalidState(detail) => write!(formatter, "invalid proof state: {detail}"),
            Self::AlreadyConcluded(kind) => write!(formatter, "proof already concluded as {kind}"),
            Self::FailedClosed(reason) => {
                write!(formatter, "proof context failed closed: {reason}")
            }
        }
    }
}

impl Error for ProofContextError {}

/// Convenient result type for proof-context state transitions.
pub type ProofContextResult<T> = Result<T, ProofContextError>;

/// State-only proof-mode context for future PB proof integration.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ProofContext {
    input_rows: Vec<InputRowIds>,
    source_relations: Vec<Option<SourceRelationProofMarker>>,
    derived_rows: Vec<ConstraintId>,
    next_row_id: Option<u64>,
    objective: ObjectiveProofState,
    conclusion: ProofConclusionState,
    fail_closed_reason: Option<FailClosedReason>,
}

impl ProofContext {
    /// Creates a context from the proof row IDs imported for each input row.
    pub fn new(input_rows: Vec<InputRowIds>) -> ProofContextResult<Self> {
        let mut seen = HashSet::new();
        let mut max_row_id = 0u64;

        for row in &input_rows {
            for id in row.ids() {
                if !seen.insert(id) {
                    return Err(ProofContextError::DuplicateInputRowId(id));
                }
                max_row_id = max_row_id.max(id.get());
            }
        }

        Ok(Self {
            source_relations: vec![None; input_rows.len()],
            input_rows,
            derived_rows: Vec::new(),
            next_row_id: max_row_id.checked_add(1),
            objective: ObjectiveProofState::None,
            conclusion: ProofConclusionState::Open,
            fail_closed_reason: None,
        })
    }

    /// Creates a context for contiguous single-row imports `1..=input_row_count`.
    pub fn from_input_row_count(input_row_count: usize) -> ProofContextResult<Self> {
        let mut input_rows = Vec::with_capacity(input_row_count);

        for index in 0..input_row_count {
            let raw_id = u64::try_from(index)
                .ok()
                .and_then(|value| value.checked_add(1))
                .ok_or(ProofContextError::ConstraintIdOverflow)?;
            let id = ConstraintId::new(raw_id).ok_or(ProofContextError::ConstraintIdOverflow)?;
            input_rows.push(InputRowIds::single(id));
        }

        Self::new(input_rows)
    }

    /// Returns imported proof row IDs grouped by parsed input row.
    pub fn input_rows(&self) -> &[InputRowIds] {
        &self.input_rows
    }

    /// Returns imported proof row IDs for one parsed input row.
    pub fn input_row(&self, row_index: usize) -> Option<InputRowIds> {
        self.input_rows.get(row_index).copied()
    }

    /// Returns source-relation proof markers grouped by parsed input row.
    pub fn input_source_relation_markers(&self) -> &[Option<SourceRelationProofMarker>] {
        &self.source_relations
    }

    /// Returns the source-relation proof marker for one parsed input row.
    pub fn input_source_relation_marker(
        &self,
        row_index: usize,
    ) -> Option<SourceRelationProofMarker> {
        self.source_relations.get(row_index).copied().flatten()
    }

    /// Records a source relation and fails closed if it is not proof-supported.
    pub fn mark_input_source_relation(
        &mut self,
        row_index: usize,
        relation: SourceRelation,
    ) -> ProofContextResult<SourceRelationProofMarker> {
        self.mark_input_source_relation_with_support(row_index, relation, relation.proof_support())
    }

    /// Records a source relation with explicit support and fails closed if needed.
    pub fn mark_input_source_relation_with_support(
        &mut self,
        row_index: usize,
        relation: SourceRelation,
        proof_support: SourceRelationProofSupport,
    ) -> ProofContextResult<SourceRelationProofMarker> {
        self.ensure_open()?;

        if row_index >= self.source_relations.len() {
            return Err(ProofContextError::InvalidState(format!(
                "source relation row index {row_index} is outside input row count {}",
                self.source_relations.len()
            )));
        }

        let marker = SourceRelationProofMarker::with_proof_support(relation, proof_support);
        self.source_relations[row_index] = Some(marker);

        if let Some(reason) = marker.unsupported_fail_closed_reason() {
            self.fail_closed(reason.clone());
            return Err(ProofContextError::FailedClosed(reason));
        }

        Ok(marker)
    }

    /// Returns proof row IDs allocated for derived proof rows.
    pub fn derived_rows(&self) -> &[ConstraintId] {
        &self.derived_rows
    }

    /// Returns the next derived proof row ID, if the ID space is not exhausted.
    pub fn next_derived_row_id(&self) -> Option<ConstraintId> {
        self.next_row_id.and_then(ConstraintId::new)
    }

    /// Allocates and records the next derived proof row ID.
    pub fn allocate_derived_row(&mut self) -> ProofContextResult<ConstraintId> {
        self.ensure_open()?;

        let raw_id = self
            .next_row_id
            .ok_or(ProofContextError::ConstraintIdOverflow)?;
        let id = ConstraintId::new(raw_id).ok_or(ProofContextError::ConstraintIdOverflow)?;
        self.next_row_id = raw_id.checked_add(1);
        self.derived_rows.push(id);
        Ok(id)
    }

    /// Returns the current objective proof state.
    pub const fn objective_state(&self) -> &ObjectiveProofState {
        &self.objective
    }

    /// Marks an objective as active without assigning a proof row yet.
    pub fn mark_objective_active(&mut self) -> ProofContextResult<()> {
        self.ensure_open()?;
        self.objective = ObjectiveProofState::Active { row_id: None };
        Ok(())
    }

    /// Records the proof row currently representing the active objective.
    pub fn set_objective_row(&mut self, row_id: ConstraintId) -> ProofContextResult<()> {
        self.ensure_open()?;
        self.objective = ObjectiveProofState::Active {
            row_id: Some(row_id),
        };
        Ok(())
    }

    /// Records concrete optimization bounds.
    pub fn set_objective_bounds(&mut self, lower: i128, upper: i128) -> ProofContextResult<()> {
        self.ensure_open()?;

        if lower > upper {
            return Err(ProofContextError::InvalidObjectiveBounds { lower, upper });
        }

        self.objective = ObjectiveProofState::Bounds { lower, upper };
        Ok(())
    }

    /// Records an infeasible optimization conclusion.
    pub fn mark_objective_infeasible(&mut self) -> ProofContextResult<()> {
        self.ensure_open()?;
        self.objective = ObjectiveProofState::Infeasible;
        Ok(())
    }

    /// Returns the current terminal proof state.
    pub const fn conclusion_state(&self) -> ProofConclusionState {
        self.conclusion
    }

    /// Records the final proof conclusion.
    pub fn conclude(&mut self, kind: ProofConclusionKind) -> ProofContextResult<()> {
        self.ensure_open()?;
        self.conclusion = ProofConclusionState::Concluded(kind);
        Ok(())
    }

    /// Records a fail-closed reason, preserving the first reason observed.
    pub fn fail_closed(&mut self, reason: FailClosedReason) {
        if self.fail_closed_reason.is_none() {
            self.fail_closed_reason = Some(reason);
        }
    }

    /// Returns the fail-closed reason, if proof mode has failed closed.
    pub fn fail_closed_reason(&self) -> Option<&FailClosedReason> {
        self.fail_closed_reason.as_ref()
    }

    /// Returns true if proof mode has failed closed.
    pub const fn is_fail_closed(&self) -> bool {
        self.fail_closed_reason.is_some()
    }

    fn ensure_open(&self) -> ProofContextResult<()> {
        if let Some(reason) = &self.fail_closed_reason {
            return Err(ProofContextError::FailedClosed(reason.clone()));
        }

        match self.conclusion {
            ProofConclusionState::Open => Ok(()),
            ProofConclusionState::Concluded(kind) => Err(ProofContextError::AlreadyConcluded(kind)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        FailClosedReason, InputRowIds, ObjectiveProofState, ProofConclusionState, ProofContext,
        ProofContextError, SourceRelation, SourceRelationProofMarker, SourceRelationProofSupport,
    };
    use crate::proof::{ConstraintId, ProofConclusionKind};

    fn id(value: u64) -> ConstraintId {
        ConstraintId::new(value).expect("test IDs are non-zero")
    }

    #[test]
    fn test_input_rows_keep_single_and_split_import_ids() {
        let single = InputRowIds::single(id(1));
        let split = InputRowIds::split(id(2), id(3));

        assert_eq!(single.primary(), id(1));
        assert_eq!(single.split_row(), None);
        assert_eq!(single.len(), 1);
        assert_eq!(single.ids().collect::<Vec<_>>(), vec![id(1)]);

        assert_eq!(split.primary(), id(2));
        assert_eq!(split.split_row(), Some(id(3)));
        assert_eq!(split.len(), 2);
        assert_eq!(split.ids().collect::<Vec<_>>(), vec![id(2), id(3)]);
    }

    #[test]
    fn test_context_from_input_count_assigns_contiguous_rows() {
        let mut context =
            ProofContext::from_input_row_count(3).expect("contiguous input rows are valid");

        assert_eq!(
            context.input_rows(),
            &[
                InputRowIds::single(id(1)),
                InputRowIds::single(id(2)),
                InputRowIds::single(id(3)),
            ]
        );
        assert_eq!(context.next_derived_row_id(), Some(id(4)));

        let derived = context
            .allocate_derived_row()
            .expect("next derived row is available");

        assert_eq!(derived, id(4));
        assert_eq!(context.derived_rows(), &[id(4)]);
        assert_eq!(context.next_derived_row_id(), Some(id(5)));
    }

    #[test]
    fn test_context_starts_derived_ids_after_split_input_rows() {
        let mut context = ProofContext::new(vec![
            InputRowIds::single(id(1)),
            InputRowIds::split(id(2), id(3)),
        ])
        .expect("distinct input row IDs are valid");

        assert_eq!(context.input_row(1), Some(InputRowIds::split(id(2), id(3))));
        assert_eq!(context.next_derived_row_id(), Some(id(4)));
        assert_eq!(
            context
                .allocate_derived_row()
                .expect("next derived row is available"),
            id(4)
        );
    }

    #[test]
    fn test_duplicate_input_row_ids_are_rejected() {
        let err = ProofContext::new(vec![
            InputRowIds::single(id(1)),
            InputRowIds::split(id(1), id(2)),
        ])
        .expect_err("input proof row IDs must be unique");

        assert!(matches!(err, ProofContextError::DuplicateInputRowId(row) if row == id(1)));
    }

    #[test]
    fn test_source_relation_marker_tracks_proof_support() {
        let greater_equal = SourceRelationProofMarker::new(SourceRelation::GreaterEqual);
        let equal = SourceRelationProofMarker::new(SourceRelation::Equal);
        let less_equal = SourceRelationProofMarker::new(SourceRelation::LessEqual);

        assert_eq!(SourceRelation::LessEqual.symbol(), "<=");
        assert_eq!(SourceRelation::LessEqual.to_string(), "<=");

        assert_eq!(greater_equal.relation(), SourceRelation::GreaterEqual);
        assert_eq!(
            greater_equal.proof_support(),
            SourceRelationProofSupport::Supported
        );
        assert!(greater_equal.is_proof_supported());
        assert!(equal.is_proof_supported());
        assert_eq!(
            less_equal.proof_support(),
            SourceRelationProofSupport::Supported
        );
        assert!(less_equal.is_proof_supported());
        assert_eq!(less_equal.unsupported_fail_closed_reason(), None);
    }

    #[test]
    fn test_source_relation_marker_preserves_explicit_unsupported_cases() {
        let unsupported_source = SourceRelationProofMarker::with_proof_support(
            SourceRelation::GreaterEqual,
            SourceRelationProofSupport::UnsupportedSourceRelation,
        );
        let unsupported_projection = SourceRelationProofMarker::with_proof_support(
            SourceRelation::LessEqual,
            SourceRelationProofSupport::UnsupportedProjection,
        );

        assert!(!unsupported_source.is_proof_supported());
        assert_eq!(
            unsupported_source.unsupported_fail_closed_reason(),
            Some(FailClosedReason::UnsupportedSourceRelation(
                SourceRelation::GreaterEqual
            ))
        );

        assert!(!unsupported_projection.is_proof_supported());
        assert_eq!(
            unsupported_projection.unsupported_fail_closed_reason(),
            Some(FailClosedReason::UnsupportedProjection(
                SourceRelation::LessEqual
            ))
        );
    }

    #[test]
    fn test_source_relation_state_records_supported_input_rows() {
        let mut context =
            ProofContext::from_input_row_count(3).expect("contiguous input rows are valid");

        assert_eq!(context.input_source_relation_markers().len(), 3);
        assert!(context
            .input_source_relation_markers()
            .iter()
            .all(Option::is_none));

        let first = context
            .mark_input_source_relation(0, SourceRelation::GreaterEqual)
            .expect(">= source relation is proof-supported");
        let second = context
            .mark_input_source_relation(1, SourceRelation::Equal)
            .expect("= source relation is proof-supported");
        let third = context
            .mark_input_source_relation(2, SourceRelation::LessEqual)
            .expect("<= source relation is proof-supported");

        assert_eq!(
            first,
            SourceRelationProofMarker::new(SourceRelation::GreaterEqual)
        );
        assert_eq!(
            second,
            SourceRelationProofMarker::new(SourceRelation::Equal)
        );
        assert_eq!(
            third,
            SourceRelationProofMarker::new(SourceRelation::LessEqual)
        );
        assert_eq!(
            context.input_source_relation_marker(0),
            Some(SourceRelationProofMarker::new(SourceRelation::GreaterEqual))
        );
        assert_eq!(
            context.input_source_relation_marker(1),
            Some(SourceRelationProofMarker::new(SourceRelation::Equal))
        );
        assert_eq!(
            context.input_source_relation_marker(2),
            Some(SourceRelationProofMarker::new(SourceRelation::LessEqual))
        );
        assert_eq!(context.input_source_relation_marker(3), None);
        assert!(!context.is_fail_closed());
    }

    #[test]
    fn test_explicit_unsupported_source_relation_fails_closed() {
        let mut context =
            ProofContext::from_input_row_count(1).expect("contiguous input rows are valid");

        let err = context
            .mark_input_source_relation_with_support(
                0,
                SourceRelation::LessEqual,
                SourceRelationProofSupport::UnsupportedSourceRelation,
            )
            .expect_err("explicit unsupported source relation fails closed");

        assert!(matches!(
            err,
            ProofContextError::FailedClosed(FailClosedReason::UnsupportedSourceRelation(
                SourceRelation::LessEqual
            ))
        ));
        assert_eq!(
            context.input_source_relation_marker(0),
            Some(SourceRelationProofMarker::with_proof_support(
                SourceRelation::LessEqual,
                SourceRelationProofSupport::UnsupportedSourceRelation
            ))
        );
        assert_eq!(
            context.fail_closed_reason(),
            Some(&FailClosedReason::UnsupportedSourceRelation(
                SourceRelation::LessEqual
            ))
        );

        let err = context
            .allocate_derived_row()
            .expect_err("failed-closed contexts cannot allocate rows");
        assert!(matches!(
            err,
            ProofContextError::FailedClosed(FailClosedReason::UnsupportedSourceRelation(
                SourceRelation::LessEqual
            ))
        ));
    }

    #[test]
    fn test_explicit_unsupported_projection_fails_closed() {
        let mut context =
            ProofContext::from_input_row_count(1).expect("contiguous input rows are valid");

        let err = context
            .mark_input_source_relation_with_support(
                0,
                SourceRelation::LessEqual,
                SourceRelationProofSupport::UnsupportedProjection,
            )
            .expect_err("explicit unsupported projection fails closed");

        assert!(matches!(
            err,
            ProofContextError::FailedClosed(FailClosedReason::UnsupportedProjection(
                SourceRelation::LessEqual
            ))
        ));
        assert_eq!(
            context.input_source_relation_marker(0),
            Some(SourceRelationProofMarker::with_proof_support(
                SourceRelation::LessEqual,
                SourceRelationProofSupport::UnsupportedProjection
            ))
        );
        assert_eq!(
            context.fail_closed_reason(),
            Some(&FailClosedReason::UnsupportedProjection(
                SourceRelation::LessEqual
            ))
        );
    }

    #[test]
    fn test_source_relation_row_index_must_exist() {
        let mut context =
            ProofContext::from_input_row_count(1).expect("contiguous input rows are valid");

        let err = context
            .mark_input_source_relation(1, SourceRelation::GreaterEqual)
            .expect_err("source relation rows must match input rows");

        assert!(matches!(
            err,
            ProofContextError::InvalidState(detail)
                if detail == "source relation row index 1 is outside input row count 1"
        ));
        assert!(!context.is_fail_closed());
    }

    #[test]
    fn test_objective_state_tracks_active_row_bounds_and_infeasible() {
        let mut context =
            ProofContext::from_input_row_count(1).expect("contiguous input rows are valid");

        assert_eq!(context.objective_state(), &ObjectiveProofState::None);

        context
            .mark_objective_active()
            .expect("open context can mark an objective");
        assert_eq!(
            context.objective_state(),
            &ObjectiveProofState::Active { row_id: None }
        );

        context
            .set_objective_row(id(2))
            .expect("open context can record an objective row");
        assert_eq!(
            context.objective_state(),
            &ObjectiveProofState::Active {
                row_id: Some(id(2))
            }
        );

        let err = context
            .set_objective_bounds(5, 4)
            .expect_err("lower bound cannot exceed upper bound");
        assert!(matches!(
            err,
            ProofContextError::InvalidObjectiveBounds { lower: 5, upper: 4 }
        ));

        context
            .set_objective_bounds(4, 4)
            .expect("equal lower and upper bounds are valid");
        assert_eq!(
            context.objective_state(),
            &ObjectiveProofState::Bounds { lower: 4, upper: 4 }
        );

        context
            .mark_objective_infeasible()
            .expect("open context can record infeasible objective state");
        assert_eq!(context.objective_state(), &ObjectiveProofState::Infeasible);
    }

    #[test]
    fn test_conclusion_state_is_terminal() {
        let mut context =
            ProofContext::from_input_row_count(0).expect("empty input rows are valid");

        assert_eq!(context.conclusion_state(), ProofConclusionState::Open);

        context
            .conclude(ProofConclusionKind::Sat)
            .expect("open context can be concluded");
        assert_eq!(
            context.conclusion_state(),
            ProofConclusionState::Concluded(ProofConclusionKind::Sat)
        );

        let err = context
            .allocate_derived_row()
            .expect_err("concluded contexts cannot allocate rows");
        assert!(matches!(
            err,
            ProofContextError::AlreadyConcluded(ProofConclusionKind::Sat)
        ));
    }

    #[test]
    fn test_fail_closed_reason_is_preserved_and_blocks_mutation() {
        let mut context =
            ProofContext::from_input_row_count(0).expect("empty input rows are valid");

        context.fail_closed(FailClosedReason::UnsupportedFeature(String::from(
            "unchecked cutting-plane transform",
        )));
        context.fail_closed(FailClosedReason::ProofEmissionFailed(String::from(
            "late error",
        )));

        assert!(context.is_fail_closed());
        assert_eq!(
            context.fail_closed_reason(),
            Some(&FailClosedReason::UnsupportedFeature(String::from(
                "unchecked cutting-plane transform"
            )))
        );

        let err = context
            .allocate_derived_row()
            .expect_err("failed-closed contexts cannot allocate rows");
        assert!(matches!(
            err,
            ProofContextError::FailedClosed(FailClosedReason::UnsupportedFeature(reason))
                if reason == "unchecked cutting-plane transform"
        ));
    }

    #[test]
    fn test_row_id_overflow_blocks_derived_allocation() {
        let mut context = ProofContext::new(vec![InputRowIds::single(id(u64::MAX))])
            .expect("u64::MAX is still a valid existing row ID");

        assert_eq!(context.next_derived_row_id(), None);

        let err = context
            .allocate_derived_row()
            .expect_err("no row exists after u64::MAX");
        assert!(matches!(err, ProofContextError::ConstraintIdOverflow));
    }
}
