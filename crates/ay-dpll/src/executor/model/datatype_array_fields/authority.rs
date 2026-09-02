// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Typed, result-local evidence produced by exact array-field reconstruction.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermEntryStamp;
use ay_core::{Sort, TermId};
use ay_model_check::ModelValue;

/// One exact datatype carrier reconstructed during the current model pass.
///
/// This inventory is evidence to revalidate, not SAT authority by possession.
#[derive(Debug, Clone)]
pub(in crate::executor::model) struct ExactDatatypeArrayClassAuthority {
    pub(in crate::executor::model) cell_sort: Sort,
    pub(in crate::executor::model) carrier: String,
    pub(in crate::executor::model) members: HashMap<TermId, TermEntryStamp>,
    /// Field indices with no authored selector observation. Their value may be
    /// free completion slack or an exact constructor argument; reauthentication
    /// must prove the selector-app set remains empty and recheck any source.
    pub(in crate::executor::model) unobserved_fields: HashSet<usize>,
}

pub(in crate::executor::model) type ArrayFieldClasses = Vec<ExactDatatypeArrayClassAuthority>;

/// Atomic successful result for every array field of one datatype class.
pub(in crate::executor::model) struct ExactDatatypeArrayFieldCompletion {
    pub(in crate::executor::model) fields: HashMap<usize, ModelValue>,
    pub(in crate::executor::model) authority: ExactDatatypeArrayClassAuthority,
}

/// One exact, current datatype-valued array cell allowed to keep total-DT
/// construction active when the e-graph/lazy lane would ordinarily own all
/// datatype values.
#[derive(Debug, Clone)]
pub(in crate::executor::model) struct AuthorizedDatatypeArrayCell {
    pub(in crate::executor::model) term: TermId,
    pub(in crate::executor::model) stamp: TermEntryStamp,
    pub(in crate::executor::model) cell_sort: Sort,
}

/// Provenance carried from model completion into total-DT construction.
///
/// The variants keep authored and generation-site-authenticated cells distinct;
/// an arbitrary completion root cannot mint the W6 e-graph override merely by
/// having a recursively hazardous sort.
#[derive(Debug, Clone)]
pub(in crate::executor::model) enum DatatypeArrayConstructionAuthorization {
    Ordinary,
    AuthoredCells(Vec<AuthorizedDatatypeArrayCell>),
    ExtensionalityCells(Vec<AuthorizedDatatypeArrayCell>),
    AuthoredAndExtensionalityCells(Vec<AuthorizedDatatypeArrayCell>),
}

/// Generation-site-authenticated extensionality roots together with the exact
/// current datatype-cell operands that justify their W6 construction slice.
pub(in crate::executor::model) struct AuthenticatedDatatypeArrayExtensionality {
    pub(in crate::executor::model) roots: Vec<TermId>,
    pub(in crate::executor::model) cells: Vec<AuthorizedDatatypeArrayCell>,
}

impl DatatypeArrayConstructionAuthorization {
    pub(in crate::executor::model) fn from_cells(
        mut authored: Vec<AuthorizedDatatypeArrayCell>,
        mut extensionality: Vec<AuthorizedDatatypeArrayCell>,
    ) -> Self {
        let has_authored = !authored.is_empty();
        let has_extensionality = !extensionality.is_empty();
        authored.append(&mut extensionality);
        authored.sort_by_key(|cell| cell.term.index());
        authored.dedup_by_key(|cell| cell.term);
        match (has_authored, has_extensionality) {
            (false, false) => Self::Ordinary,
            (true, false) => Self::AuthoredCells(authored),
            (false, true) => Self::ExtensionalityCells(authored),
            (true, true) => Self::AuthoredAndExtensionalityCells(authored),
        }
    }

    pub(in crate::executor::model) fn cells(&self) -> &[AuthorizedDatatypeArrayCell] {
        match self {
            Self::Ordinary => &[],
            Self::AuthoredCells(cells)
            | Self::ExtensionalityCells(cells)
            | Self::AuthoredAndExtensionalityCells(cells) => cells,
        }
    }
}

/// One inventory entry after every typed field and current observation has
/// been revalidated against the immutable model consumed by a gate.
pub(in crate::executor::model) struct AuthenticatedDatatypeArrayClass {
    pub(in crate::executor::model) cell_sort: Sort,
    pub(in crate::executor::model) carrier: String,
    pub(in crate::executor::model) members: HashMap<TermId, TermEntryStamp>,
    pub(in crate::executor::model) unobserved_fields: HashSet<usize>,
    pub(in crate::executor::model) value: ModelValue,
}

/// Exact current datatype-cell terms admitted while building one already-
/// authenticated outer-array completion candidate.
///
/// Possession is intentionally scoped to that candidate call. A generic
/// completion/output path cannot mint this set from the raw result inventory.
pub(in crate::executor::model) struct AuthenticatedDatatypeArrayMembers {
    members: HashSet<TermId>,
}

impl AuthenticatedDatatypeArrayMembers {
    pub(in crate::executor::model) fn contains(&self, term: TermId) -> bool {
        self.members.contains(&term)
    }

    pub(in crate::executor::model) fn is_empty(&self) -> bool {
        self.members.is_empty()
    }

    pub(super) fn from_members(members: HashSet<TermId>) -> Self {
        Self { members }
    }
}
