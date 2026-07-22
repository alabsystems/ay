// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Internal types used by the PDR solver.
//!
//! These types are used for internal algorithm state and are not part of the public API.

use crate::smt::SmtValue;
use crate::{ChcExpr, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::counterexample::Counterexample;
use super::derivation::DerivationId;
use super::frame::Lemma;

/// Represents possible offsets for a variable (accounting for OR branches in constraints)
#[derive(Debug)]
pub(super) enum VarOffset {
    /// Single constant offset
    Const(i128),
    /// Multiple possible offsets (one per OR branch)
    Cases(Vec<i128>),
}

/// Result of initial safety check
pub(super) enum InitResult {
    Safe,
    Unsafe,
}

/// Type of bound constraint extracted from bad state
#[derive(Debug, Clone, Copy)]
pub(super) enum BoundType {
    /// x > val
    Gt,
    /// x >= val
    Ge,
    /// x < val
    Lt,
    /// x <= val
    Le,
}

/// Type of relational constraint between two variables
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum RelationType {
    /// x > y
    Gt,
    /// x >= y
    Ge,
    /// x < y
    Lt,
    /// x <= y
    Le,
}

/// Result of strengthening attempt
pub(super) enum StrengthenResult {
    Safe,
    Unsafe(Counterexample),
    Unknown,
    Continue,
}

/// Result of blocking a proof obligation
pub(super) enum BlockResult {
    /// Blocked successfully with a new lemma
    Blocked(Lemma),
    /// Already blocked by existing frame constraint - no new lemma needed
    AlreadyBlocked,
    /// Not blocked - predecessor state exists (boxed to reduce enum size)
    Reachable(Box<PredecessorState>),
    /// Unknown
    Unknown,
}

/// A predecessor state (for counterexample construction)
pub(super) struct PredecessorState {
    pub(super) predicate: PredicateId,
    pub(super) state: ChcExpr,
    pub(super) clause_index: usize,
    /// SMT model that witnesses this predecessor state
    pub(super) smt_model: FxHashMap<String, SmtValue>,
    /// Optional derivation handle for multi-body clause tracking.
    /// When set, this predecessor is part of a derivation that tracks progress
    /// through all premises of a hyperedge.
    /// Scaffolding for #1275; will be used when derivation tracking completes.
    pub(super) derivation_id: Option<DerivationId>,
}
