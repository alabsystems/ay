// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Portable data for a bounded source-bound rational SOS theorem.
//! These types confer no proof authority. The independent ay-proof checker
//! authenticates source polarity, coefficient normalization, PSD and identity.

use crate::term::TermId;
use num_bigint::{BigInt, Sign};
use serde::{Deserialize, Serialize};

mod wire;
pub(super) use wire::deserialize_clause;
#[cfg(test)]
mod tests;

/// A rational in exact raw integer form. Structural equality does not perform
/// rational arithmetic or equate differently encoded fractions.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NraSosRational {
    /// Signed numerator in the raw fraction encoding.
    #[serde(with = "wire::integer")]
    pub numerator: BigInt,
    /// Denominator, required to be positive by shape validation.
    #[serde(with = "wire::integer")]
    pub denominator: BigInt,
}

impl NraSosRational {
    /// Hard bound on EACH integer, including during streaming decoding.
    pub const MAX_BITS: u64 = 1_024;

    /// Allocation-free numeric shape check; coprimality is checked with the
    /// proof caller's work/cancellation meter before arithmetic.
    pub fn validate_shape(&self) -> Result<(), NraSosShapeError> {
        if self.numerator.bits() > Self::MAX_BITS || self.denominator.bits() > Self::MAX_BITS {
            return Err(NraSosShapeError::Limit);
        }
        if self.denominator.sign() != Sign::Plus {
            return Err(NraSosShapeError::Malformed);
        }
        Ok(())
    }
}

/// Source factors are positions in the exact conclusion clause. The checker
/// derives the NEGATION of each selected literal; no source array is supplied.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub enum NraSosOrigin {
    /// The negation of one selected conclusion-clause literal.
    ClauseLiteral {
        /// Zero-based position in the exact conclusion clause.
        position: u32,
    },
    /// Product of two source factors selected from the conclusion clause.
    Product {
        /// Position of the first source factor.
        left: u32,
        /// Position of the second source factor.
        right: u32,
    },
}

/// One constant multiplier times a source factor (or two-factor product).
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NraSosTerm {
    /// Selected source factor or pair of factors.
    pub origin: NraSosOrigin,
    /// Exact rational coefficient multiplying the selected source factor.
    pub multiplier: NraSosRational,
}

/// Identity `basisᵀ gram basis + Σ multiplier·factor = rhs`.
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct NraSosCertificate {
    /// Constant monomial first, then unique sorted monomials of degree ≤2.
    #[serde(with = "wire::basis")]
    pub basis: Vec<Vec<TermId>>,
    /// Full square matrix; symmetry and PSD are independent checker duties.
    #[serde(with = "wire::gram")]
    pub gram: Vec<Vec<NraSosRational>>,
    /// Weighted source factors in the claimed polynomial identity.
    #[serde(with = "wire::terms")]
    pub terms: Vec<NraSosTerm>,
    /// Exact constant on the right-hand side of the claimed identity.
    pub rhs: NraSosRational,
}

/// A dimension/encoding refusal, not a theorem verdict.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub enum NraSosShapeError {
    /// A dimension or integer exceeds the fixed decoding envelope.
    #[error("SOS certificate exceeds its fixed envelope")]
    Limit,
    /// A payload violates its required structural encoding.
    #[error("SOS certificate has a malformed shape")]
    Malformed,
}

impl NraSosCertificate {
    /// Maximum number of selectable conclusion-clause positions.
    pub const MAX_CLAUSE_SLOTS: usize = 1_024;
    /// Maximum number of basis monomials and Gram matrix rows or columns.
    pub const MAX_BASIS: usize = 45;
    /// Maximum number of weighted source factors.
    pub const MAX_TERMS: usize = 400;
    /// Maximum distinct variables admitted by the bounded SOS checker.
    pub const MAX_VARS: usize = 8;

    /// Source-independent, allocation-free preflight. Input vectors are checked
    /// before their contents, so programmatically forged payloads are bounded
    /// as well as deserialized ones. This is NOT certificate verification.
    pub fn validate_shape(&self) -> Result<(), NraSosShapeError> {
        let n = self.basis.len();
        if n > Self::MAX_BASIS
            || self.gram.len() > Self::MAX_BASIS
            || self.terms.len() > Self::MAX_TERMS
        {
            return Err(NraSosShapeError::Limit);
        }
        if n == 0 || !self.basis[0].is_empty() || self.gram.len() != n {
            return Err(NraSosShapeError::Malformed);
        }
        for (index, monomial) in self.basis.iter().enumerate() {
            if monomial.len() > 2 {
                return Err(NraSosShapeError::Limit);
            }
            if monomial.windows(2).any(|pair| pair[0] > pair[1])
                || self.basis[..index].contains(monomial)
            {
                return Err(NraSosShapeError::Malformed);
            }
        }
        for row in &self.gram {
            if row.len() > Self::MAX_BASIS {
                return Err(NraSosShapeError::Limit);
            }
            if row.len() != n {
                return Err(NraSosShapeError::Malformed);
            }
            for coefficient in row {
                coefficient.validate_shape()?;
            }
        }
        for term in &self.terms {
            let (left, right) = match term.origin {
                NraSosOrigin::ClauseLiteral { position } => (position, position),
                NraSosOrigin::Product { left, right } => (left, right),
            };
            if left as usize >= Self::MAX_CLAUSE_SLOTS || right as usize >= Self::MAX_CLAUSE_SLOTS {
                return Err(NraSosShapeError::Limit);
            }
            term.multiplier.validate_shape()?;
        }
        self.rhs.validate_shape()
    }
}
