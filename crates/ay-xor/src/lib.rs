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
mod pcgf2;
mod preprocess;

// --- Re-exports ---

/// Variable ID type (matches ay-sat's variable representation).
pub type VarId = u32;

// Internal re-export for tests and Kani proofs
#[cfg(any(test, kani))]
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

/// Kani formal verification proofs for XOR solver correctness
#[cfg(kani)]
mod kani_proofs {
    use super::*;

    /// Proof: XorConstraint deduplication removes pairs (a XOR a = 0)
    #[kani::proof]
    #[kani::unwind(5)]
    fn proof_xor_duplicate_removal() {
        // Create small variable IDs to keep proof tractable
        let a: VarId = kani::any();
        let b: VarId = kani::any();
        kani::assume(a < 3 && b < 3);

        // (a, a) should reduce to empty
        let xor = XorConstraint::new(vec![a, a], false);
        assert!(xor.is_empty(), "Duplicate variables should cancel");

        // (a, a) with rhs=true should be conflict (0 = 1)
        let xor = XorConstraint::new(vec![a, a], true);
        assert!(xor.is_conflict(), "0 = 1 should be conflict");
    }

    /// Proof: XorConstraint with distinct variables preserves them
    #[kani::proof]
    #[kani::unwind(5)]
    fn proof_xor_distinct_preserved() {
        let a: VarId = kani::any();
        let b: VarId = kani::any();
        kani::assume(a < 3 && b < 3 && a != b);

        let rhs: bool = kani::any();
        let xor = XorConstraint::new(vec![a, b], rhs);

        // Both variables should be preserved
        assert_eq!(xor.vars.len(), 2);
        assert!(xor.vars.contains(&a));
        assert!(xor.vars.contains(&b));
        assert_eq!(xor.rhs, rhs);
    }

    /// Proof: XorConstraint variables are always sorted
    #[kani::proof]
    #[kani::unwind(6)]
    fn proof_xor_vars_sorted() {
        let a: VarId = kani::any();
        let b: VarId = kani::any();
        let c: VarId = kani::any();
        kani::assume(a < 4 && b < 4 && c < 4);
        kani::assume(a != b && b != c && a != c);

        let xor = XorConstraint::new(vec![c, a, b], false);

        // Variables should be sorted
        for i in 1..xor.vars.len() {
            assert!(xor.vars[i - 1] < xor.vars[i], "Variables must be sorted");
        }
    }

    /// Proof: Empty XorConstraint classification is correct
    #[kani::proof]
    #[kani::unwind(2)]
    fn proof_xor_empty_classification() {
        let rhs: bool = kani::any();
        let xor = XorConstraint::new(vec![], rhs);

        // Empty + rhs=false is tautology, empty + rhs=true is conflict
        assert_eq!(xor.is_tautology(), !rhs);
        assert_eq!(xor.is_conflict(), rhs);
    }

    /// Proof: Unit XorConstraint produces correct literal polarity
    #[kani::proof]
    #[kani::unwind(4)]
    fn proof_xor_unit_literal_polarity() {
        let var: VarId = kani::any();
        kani::assume(var < 10);
        let rhs: bool = kani::any();

        let xor = XorConstraint::new(vec![var], rhs);
        assert!(xor.is_unit());

        let lit = xor.unit_lit().unwrap();
        assert_eq!(lit.variable().id(), var);

        // rhs=true means var=1 (positive), rhs=false means var=0 (negative)
        assert_eq!(lit.is_positive(), rhs);
    }

    /// Proof: PackedRow get/set are consistent
    #[kani::proof]
    #[kani::unwind(4)]
    fn proof_packed_row_get_set_consistency() {
        let col: usize = kani::any();
        kani::assume(col < 64); // Keep bounded to single word

        let mut row = PackedRow::new(64);
        let value: bool = kani::any();

        row.set(col, value);
        assert_eq!(row.get(col), value, "Get should return what was set");
    }

    /// Proof: PackedRow XOR is self-inverse
    #[kani::proof]
    #[kani::unwind(4)]
    fn proof_packed_row_xor_inverse() {
        let col: usize = kani::any();
        kani::assume(col < 64);

        let mut row = PackedRow::new(64);
        let rhs: bool = kani::any();
        row.set(col, true);
        row.rhs = rhs;

        // XOR with itself
        let row_copy = row.clone();
        row.xor_in(&row_copy);

        // Should now be all zeros
        assert!(row.is_zero(), "XOR with self should give zero");
        assert!(!row.rhs, "RHS XOR with itself should be false");
    }

    /// Proof: PackedRow iter_set_bits is correct for single set bit
    #[kani::proof]
    #[kani::unwind(4)]
    fn proof_packed_row_single_set_bit() {
        let col: usize = kani::any();
        kani::assume(col < 64);

        let mut row = PackedRow::new(64);
        row.set(col, true);

        let bits: Vec<usize> = row.iter_set_bits().collect();
        assert_eq!(bits.len(), 1, "Single bit should have count 1");
        assert_eq!(bits[0], col, "Set bit should be at the set column");
    }
}
