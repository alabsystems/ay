// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Common SMT-LIB2 logic constants.

// =========================================================================
// Quantifier-free logics
// =========================================================================

/// Quantifier-free uninterpreted functions.
pub const QF_UF: &str = "QF_UF";

/// Quantifier-free linear integer arithmetic.
pub const QF_LIA: &str = "QF_LIA";

/// Quantifier-free linear real arithmetic.
pub const QF_LRA: &str = "QF_LRA";

/// Quantifier-free nonlinear integer arithmetic.
pub const QF_NIA: &str = "QF_NIA";

/// Quantifier-free integer arithmetic with exponentiation.
pub const QF_EIA: &str = "QF_EIA";

/// Quantifier-free nonlinear real arithmetic.
pub const QF_NRA: &str = "QF_NRA";

/// Quantifier-free uninterpreted functions with linear integer arithmetic.
pub const QF_UFLIA: &str = "QF_UFLIA";

/// Quantifier-free uninterpreted functions with linear real arithmetic.
pub const QF_UFLRA: &str = "QF_UFLRA";

/// Quantifier-free arrays with uninterpreted functions and linear integer arithmetic.
pub const QF_AUFLIA: &str = "QF_AUFLIA";

/// Quantifier-free arrays with uninterpreted functions and linear real arithmetic.
pub const QF_AUFLRA: &str = "QF_AUFLRA";

/// Quantifier-free arrays with uninterpreted functions and mixed integer/real arithmetic.
pub const QF_AUFLIRA: &str = "QF_AUFLIRA";

/// Quantifier-free bitvectors.
pub const QF_BV: &str = "QF_BV";

/// Quantifier-free arrays with bitvectors.
pub const QF_ABV: &str = "QF_ABV";

/// Quantifier-free arrays with uninterpreted functions and bitvectors.
pub const QF_AUFBV: &str = "QF_AUFBV";

/// Quantifier-free IEEE 754 floating-point arithmetic.
pub const QF_FP: &str = "QF_FP";

/// Quantifier-free bitvectors and floating-point.
pub const QF_BVFP: &str = "QF_BVFP";

/// Quantifier-free floating-point with arrays and bitvectors.
pub const QF_ABVFP: &str = "QF_ABVFP";

/// Quantifier-free strings.
pub const QF_S: &str = "QF_S";

/// Quantifier-free strings with linear integer arithmetic.
pub const QF_SLIA: &str = "QF_SLIA";

/// Quantifier-free sequences.
pub const QF_SEQ: &str = "QF_SEQ";

/// Quantifier-free sequences with linear integer arithmetic.
pub const QF_SEQLIA: &str = "QF_SEQLIA";

/// Quantifier-free arrays with extensionality (no arithmetic).
pub const QF_AX: &str = "QF_AX";

/// Quantifier-free algebraic datatypes.
pub const QF_DT: &str = "QF_DT";

/// Quantifier-free strings + non-linear integer arithmetic.
pub const QF_SNIA: &str = "QF_SNIA";

/// Quantifier-free mixed linear integer and real arithmetic.
pub const QF_LIRA: &str = "QF_LIRA";

/// Quantifier-free non-linear mixed integer/real arithmetic.
pub const QF_NIRA: &str = "QF_NIRA";

/// Quantifier-free uninterpreted functions with bitvectors.
pub const QF_UFBV: &str = "QF_UFBV";

/// Quantifier-free uninterpreted functions with non-linear integer arithmetic.
pub const QF_UFNIA: &str = "QF_UFNIA";

/// Quantifier-free uninterpreted functions with non-linear real arithmetic.
pub const QF_UFNRA: &str = "QF_UFNRA";

/// Quantifier-free uninterpreted functions with non-linear mixed int/real arithmetic.
pub const QF_UFNIRA: &str = "QF_UFNIRA";

// =========================================================================
// Quantified logics
// =========================================================================

/// Uninterpreted functions with quantifiers.
pub const UF: &str = "UF";

/// Linear integer arithmetic with quantifiers.
pub const LIA: &str = "LIA";

/// Linear real arithmetic with quantifiers.
pub const LRA: &str = "LRA";

/// Non-linear integer arithmetic with quantifiers.
pub const NIA: &str = "NIA";

/// Non-linear real arithmetic with quantifiers.
pub const NRA: &str = "NRA";

/// Non-linear mixed integer/real arithmetic with quantifiers.
pub const NIRA: &str = "NIRA";

/// Uninterpreted functions with linear integer arithmetic and quantifiers.
pub const UFLIA: &str = "UFLIA";

/// Uninterpreted functions with linear real arithmetic and quantifiers.
pub const UFLRA: &str = "UFLRA";

/// Uninterpreted functions with non-linear integer arithmetic and quantifiers.
pub const UFNIA: &str = "UFNIA";

/// Uninterpreted functions with non-linear real arithmetic and quantifiers.
pub const UFNRA: &str = "UFNRA";

/// Uninterpreted functions with non-linear mixed int/real arithmetic and quantifiers.
pub const UFNIRA: &str = "UFNIRA";

/// Bitvectors with quantifiers.
pub const BV: &str = "BV";

/// Uninterpreted functions with bitvectors and quantifiers.
pub const UFBV: &str = "UFBV";

/// Arrays with uninterpreted functions and bitvectors (with quantifiers).
pub const AUFBV: &str = "AUFBV";

/// Arrays with uninterpreted functions and linear integer arithmetic (with quantifiers).
pub const AUFLIA: &str = "AUFLIA";

/// Arrays with uninterpreted functions and linear real arithmetic (with quantifiers).
pub const AUFLRA: &str = "AUFLRA";

/// Mixed integer/real arithmetic with quantifiers.
pub const LIRA: &str = "LIRA";

/// Arrays with uninterpreted functions and mixed integer/real arithmetic (with quantifiers).
pub const AUFLIRA: &str = "AUFLIRA";

// =========================================================================
// Special logics
// =========================================================================

/// Constrained Horn Clauses over linear integer arithmetic.
pub const HORN: &str = "HORN";

/// All theories (Z3 extension).
pub const ALL: &str = "ALL";
