// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

// Lemma clustering for Global Guidance (#716). Wired into PDR lemma learning to
// enable cluster-driven min/max proposals and CC+MBP subsumption.
//! Lemma clustering for pattern-based global generalization.
//!
//! This module implements lemma clustering as described in Z3 Spacer's
//! "Global Guidance for Local Generalization in Model Checking" (CAV 2020).
//!
//! A cluster is defined by a pattern (QF formula with free variables representing
//! abstracted integer constants). Lemmas in the cluster are instances of the pattern,
//! obtained by substituting constants for pattern variables.
//!
//! # Architecture
//!
//! The clustering system has two main components:
//! - `LemmaCluster`: A single cluster with pattern and member lemmas
//! - `ClusterStore`: Per-predicate storage of clusters in the PDR solver
//!
//! # Integration
//!
//! Wire into PDR after local generalization produces a blocking cube:
//! 1. Extract pattern from blocking cube (abstract numerics to vars)
//! 2. Find or create matching cluster
//! 3. If cluster eligible, attempt `try_cluster_subsume` (global_generalizer.rs)
//!
//! # References
//!
//! - Z3: `reference/z3/src/muz/spacer/spacer_cluster.h`
//! - Design: the development design notes
//! - Issue: #1297

use crate::expr_vars::expr_var_names;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::collections::VecDeque;
use std::sync::Arc;

use super::anti_unify::{anti_unify, are_neighbours_int_only};
use super::semantic_match::SemanticMatcher;

mod cluster;
mod filtering;
mod pattern;
mod store;

pub(crate) use cluster::{LemmaCluster, LemmaInstance};
pub(crate) use filtering::{filter_out_lit, filter_out_lit_with_eq_retry};
pub(crate) use pattern::{extract_pattern, match_pattern, normalize_cube};
pub(crate) use store::ClusterStore;

#[cfg(test)]
pub(crate) use cluster::{
    has_nonlinear_var_mul, is_mono_var_lit, DEFAULT_CLUSTER_GAS, MAX_CLUSTER_SIZE,
};
#[cfg(test)]
pub(crate) use store::MAX_CLUSTERS_PER_PREDICATE;

#[cfg(test)]
#[path = "../lemma_cluster_tests/mod.rs"]
mod tests;
