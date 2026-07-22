// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Safety checks based on discovered invariants.

use super::{
    extract_negated_parity_constraint, extract_parity_constraint, ChcExpr, ChcOp, ChcSort, ChcVar,
    FxHashMap, HornClause, InvariantModel, Lemma, PdrSolver, PredicateId, RelationType, SmtResult,
};

mod candidate_repair;
mod classify;
mod houdini_prune;
mod inductive_accept_core;
#[cfg(test)]
mod inductive_accept_core_tests;
mod mod_check;
mod multiplicative;
mod relational;
mod safety_proof;
mod safety_proof_cascade;
mod safety_proof_helpers;
mod safety_proof_inductive;
#[cfg(test)]
mod tests;
