// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Feature-gated facade over the crate-private exact univariate / real-algebraic
//! primitives, used ONLY by the dev-only differential oracle
//! (`crates/ay-nra-oracle`).
//!
//! Nothing in the solver depends on this module: it is compiled only when the
//! `oracle-api` feature is on, which no shipping build ever enables. It exists
//! because [`crate::univariate::UniPoly`] and friends are `pub(crate)` — the
//! oracle has to reach them without widening the crate's real public surface.
//!
//! The wrappers are newtypes, not re-exports, so the crate-private types stay
//! crate-private and the facade can be deleted without touching solver code.

use std::cmp::Ordering;

use num_bigint::BigInt;
use num_rational::BigRational;

use crate::algebraic::{sylvester_det_fixed, RealAlgebraic, RealScalar};
use crate::anum;
use crate::explain;
use crate::ialg;
use crate::mpbq;
use crate::mroot;
use crate::polymanager;
use crate::subresultant::{self, MPolyZ, Mono, RPoly};
use crate::univariate::{
    isolate_roots, poly_gcd, rational_sign, square_free_part, sturm_count, sturm_sequence,
    RootMarker, UniPoly,
};
use crate::upoly;

// Rational-polynomial, real-algebraic, and scalar wrappers.
include!("oracle_api/scalar.rs");

// Fraction-free subresultants and bivariate CAD projection wrappers.
include!("oracle_api/subresultant.rs");

// Multivariate root isolation at algebraic sample points.
include!("oracle_api/mroot.rs");

// Sparse multivariate polynomial-manager wrappers.
include!("oracle_api/polymanager.rs");

// Dense integer and finite-field polynomial wrappers.
include!("oracle_api/upoly.rs");

// Dyadic rational and interval wrappers.
include!("oracle_api/mpbq.rs");

// Dyadic algebraic numbers and justified interval-set wrappers.
include!("oracle_api/anum_ialg.rs");

// Conflict-explanation and projection wrappers.
include!("oracle_api/explain.rs");
