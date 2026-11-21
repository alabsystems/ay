// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![forbid(unsafe_code)]
#![warn(missing_docs)]

//! XOR Gauss-Jordan theory solver for AY.
//!
//! This crate provides native handling of XOR constraints using Gauss-Jordan
//! elimination over GF(2). This gives 10-1000x speedup on XOR-heavy instances
//! compared to CNF encoding.
//!
//! # Background
//!
//! XOR constraints are parity constraints: `x1 XOR x2 XOR ... XOR xn = rhs`.
//! These form a system of linear equations over GF(2) (the field with two
//! elements, 0 and 1). Gauss-Jordan elimination solves such systems efficiently.
//!
//! # Module Structure
//!
//! - `constraint`: XOR constraint representation
//! - `packed_row`: Packed bit matrix row for GF(2) operations
//! - `gaussian`: Gauss-Jordan elimination solver
//! - `extension`: SAT solver extension trait implementation
//! - `finder`: XOR pattern detection from CNF clauses
//! - `preprocess`: Preprocessing and convenience solve functions
//! - `ext_dimacs`: Extended DIMACS format parser/writer
//!
//! # Reference
//!
//! Based on CryptoMiniSat's approach:
//! - Paper: "When Boolean Satisfiability Meets Gaussian Elimination in a Simplex Way"
//!   (Han & Jiang, CAV 2012)
//! - Source: <https://github.com/msoos/cryptominisat>

// --- Modules ---

mod component;
mod constraint;
mod ext_dimacs;
mod extension;
mod finder;
mod gaussian;
pub(crate) mod packed_row;
mod parity_space;
mod pcgf2;
mod preprocess;

// --- Re-exports ---

/// Variable ID type (matches ay-sat's variable representation).
pub type VarId = u32;

// Internal re-export for tests
#[cfg(test)]
pub(crate) use packed_row::PackedRow;

// Constraint types
pub use constraint::XorConstraint;

// Gaussian solver types
pub use gaussian::{GaussResult, GaussianSolver};

// Extension type
pub use extension::XorExtension;

// Finder type
pub use finder::XorFinder;

// Polynomial Calculus / GF(2) certificate export
pub use pcgf2::{
    pc_gf2_certificate_json, write_pc_gf2_certificate, PcGf2CertificateError, PcGf2CertificateStats,
};

// Parity-space walk (AY-SAT-2)
pub use parity_space::{
    solve_parity_space, ParitySpaceDecline, ParitySpaceOutcome, ParitySpaceStats,
    FILTERED_SCAN_MAX_DIMENSION, FULL_SCAN_MAX_DIMENSION,
};

// Preprocessing functions and types
pub use preprocess::{
    preprocess_clauses, preprocess_clauses_with_stats, should_enable_gauss_elimination,
    solve_with_xor_detection, solve_with_xor_detection_stats, XorPreprocessStats, XorSatResult,
};

// Extended DIMACS support
pub use ext_dimacs::{
    parse_ext_dimacs, parse_ext_dimacs_str, solve_ext_dimacs, solve_ext_dimacs_str,
    write_ext_dimacs, ExtDimacsError, ExtDimacsFormula,
};

// --- Test and verification modules ---

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
