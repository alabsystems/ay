// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Must-reachability checking, derivation tracking, and must-summary propagation.
//!
//! Implements the Spacer-style must-summary computation where reach facts track
//! concrete reachable states and must-summaries provide under-approximations of
//! reachable state sets. Functions handle:
//!
//! - Reach-fact premise selection for witness chains
//! - Must-reachability checking via transition from level-1
//! - Derivation progress for multi-body clauses
//! - Must-summary forward propagation across frames
//! - Loop-closure enrichment for must-summaries
//! - Symbolic equality propagation to derived predicates

use super::{
    cube, ChcExpr, ChcOp, ChcVar, FxHashMap, HornClause, Lemma, PdrSolver, PredicateId,
    ProofObligation, ReachFact, ReachFactId, SmtResult, SmtValue,
};

mod forward;
mod frame0;
mod loop_closure;
mod reach_facts;
mod symbolic;
