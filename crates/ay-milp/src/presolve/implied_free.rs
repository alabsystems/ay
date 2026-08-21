// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact fixed-column projection and implied-free equality aggregation.
//!
//! A fixed column can always be projected: its box supplies its one possible
//! value.  An equality can project a non-fixed column when the equality's exact
//! affine recovery lies inside that column's declared box for every point in
//! the surviving box.  For an integer column, the recovery must additionally
//! be integer-affine over integer survivors.  These are standard presolve
//! substitutions; each accepted step is a bijection between the old feasible
//! set and the new one.
//!
//! Classification and folding happen entirely in `BigRational`.  The reduced
//! model is emitted only if every changed float is an exact representation of
//! its rational value.  A deadline, rational-size cap, fill cap, and memory
//! preflight all decline the whole speculative transform rather than returning
//! a partial or rounded model.

use std::collections::{BTreeMap, HashSet};
use std::mem::size_of;
use std::sync::Arc;
use std::time::Instant;

use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive, Zero};

use crate::cert::{FarkasCertificate, OptimalityCertificate};
use crate::model::{exact, Col, ColKind, Model, Row};
use crate::outcome::Outcome;
use crate::tree_cert::MilpInfeasibilityCertificate;

pub(crate) const MAX_ELIMINATIONS: usize = 4_096;
pub(crate) const MAX_ROW_TERMS: usize = 4_096;
pub(crate) const MAX_TOTAL_TERMS: usize = 1_000_000;
const MAX_CANDIDATES_PER_ROUND: usize = 8_192;
pub(crate) const MAX_RATIONAL_BITS: u64 = 4_096;
pub(crate) const MAX_RECOVERY_TERMS: usize = 1_000_000;
const ESTIMATED_BYTES_PER_EXACT_TERM: usize = 192;
const ESTIMATED_BYTES_PER_EXACT_VALUE: usize = 160;
const ESTIMATED_MODEL_COL_BYTES: usize = 96;
const ESTIMATED_MODEL_ROW_BYTES: usize = 96;
const ESTIMATED_MODEL_TERM_BYTES: usize = 24;
const ESTIMATED_PROOF_MULTIPLIER_BYTES: usize = 256;
const ESTIMATED_PROOF_TREE_NODE_BYTES: usize = 128;
const DEFAULT_WORKSPACE_BYTES: usize = 512 << 20;
const WORKSPACE_SHARE: usize = 16;
const PROCESS_MEMORY_PERCENT: usize = 90;
const ANALYSIS_VERSION: u32 = 1;
pub(crate) const MAX_ANALYSIS_COLS: usize = 250_000;
pub(crate) const MAX_ANALYSIS_ROWS: usize = 250_000;
const MAX_ANALYSIS_ROUNDS: usize = 64;
const MAX_ANALYSIS_TERM_VISITS: usize = 16_000_000;
pub(crate) const MAX_AFFINE_TREE_NODES: usize = MAX_ELIMINATIONS * 2 + 1;
pub(crate) const MAX_AFFINE_TREE_DEPTH: usize = 1_024;
pub(crate) const MAX_AFFINE_PROOF_MULTIPLIERS: usize = MAX_TOTAL_TERMS;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AffineRecovery {
    Fixed {
        col: usize,
        value: BigRational,
    },
    Equality {
        /// Original row index naming the defining equality at this replay step.
        row: usize,
        col: usize,
        constant: BigRational,
        /// `x[col] = constant + sum(coefficient * x[column])`.
        terms: Vec<(usize, BigRational)>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AffineAggregationCaps {
    pub(crate) version: u32,
    pub(crate) source_cols: usize,
    pub(crate) source_rows: usize,
    pub(crate) input_nnz: usize,
    pub(crate) nnz_cap: usize,
    pub(crate) max_eliminations: usize,
    pub(crate) max_row_terms: usize,
    pub(crate) max_total_terms: usize,
    pub(crate) max_recovery_terms: usize,
    pub(crate) max_rational_bits: u64,
    pub(crate) analysis_rounds: usize,
    pub(crate) analysis_term_visits: usize,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct AnalysisBound {
    pub(crate) lower: Option<BigRational>,
    pub(crate) upper: Option<BigRational>,
}

#[derive(Debug, Clone)]
pub(crate) struct AffineAggregationAnalysis {
    pub(crate) source_digest: String,
    pub(crate) reduced_digest: String,
    pub(crate) bounds: Arc<[AnalysisBound]>,
    pub(crate) steps: Arc<[AffineRecovery]>,
    pub(crate) objective_delta: BigRational,
    pub(crate) caps: AffineAggregationCaps,
}

/// Proof (or honest absence of proof) produced in the rebuilt reduced frame.
#[derive(Debug, Clone)]
pub enum AffineAggregationInnerProof {
    Farkas(FarkasCertificate),
    Optimality(OptimalityCertificate),
    InfeasibilityTree(MilpInfeasibilityCertificate),
    Unsupported,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AffineAggregationClaim {
    Feasible,
    Optimal { value: BigRational },
    Infeasible,
}

/// Independently replayable wrapper around one exact affine aggregation.
#[derive(Debug, Clone)]
pub struct AffineAggregationCertificate {
    pub(crate) analysis: AffineAggregationAnalysis,
    pub(crate) claim: AffineAggregationClaim,
    pub(crate) inner_proof: AffineAggregationInnerProof,
    pub(crate) reduced_primal: Option<Vec<BigRational>>,
    pub(crate) source_primal: Option<Vec<BigRational>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AffineAggregationVerification {
    pub primal_verified: bool,
    pub infeasibility_verified: bool,
    pub optimality_verified: bool,
}

#[derive(Debug, thiserror::Error, PartialEq, Eq)]
pub enum AffineAggregationCertificateError {
    #[error("source model digest does not match the aggregation artifact")]
    SourceDigest,
    #[error("aggregation resource caps are malformed or exceeded")]
    Caps,
    #[error("recorded propagation analysis box is not implied by the source model")]
    AnalysisBox,
    #[error("ordered affine aggregation replay failed")]
    Replay,
    #[error("rebuilt reduced model digest does not match the artifact")]
    ReducedDigest,
    #[error("recorded exact objective constant is not the replayed constant")]
    ObjectiveDelta,
    #[error("inner reduced-frame proof does not verify")]
    InnerProof,
    #[error("recorded primal point or objective does not verify in its claimed frame")]
    Primal,
}

/// Exact point/value postsolve for [`aggregate_implied_free_equalities`].
pub(crate) struct AffineAggregationPostsolve {
    n_orig: usize,
    n_reduced: usize,
    map: Vec<Option<Col>>,
    recover: Arc<[AffineRecovery]>,
    recovery_terms: usize,
    const_delta: BigRational,
    analysis: AffineAggregationAnalysis,
}

mod analysis;
mod apply;
mod certificate;
mod emission;
mod numeric;
mod pending;
mod postsolve;
mod preflight;
mod propagation;
mod replay;
mod transform;
mod work;

use analysis::*;
use apply::*;
use certificate::*;
use emission::*;
use numeric::*;
use preflight::*;
use propagation::*;
use replay::*;
use transform::*;
use work::*;

pub(crate) use certificate::validate_certificate_payload_caps;
pub(crate) use numeric::{enabled, prime_env};
pub(crate) use pending::{
    clear_pending_certificate, set_pending_certificate, take_pending_certificate,
};
pub(crate) use transform::aggregate_implied_free_equalities;

#[cfg(test)]
#[path = "implied_free/tests.rs"]
mod tests;
