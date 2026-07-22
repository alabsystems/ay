// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interpolant types for the AY Solver API.
//!
//! Provides Craig interpolation at the SMT level. Given two groups of assertions
//! A and B such that A /\ B is UNSAT, an interpolant I satisfies:
//! - A |= I
//! - I /\ B is UNSAT
//! - I mentions only variables shared between A and B
//!
//! Three interpolation strengths are supported, corresponding to the classical
//! Pudlak (1997) and McMillan (2003) algorithms applied at resolution proof nodes:
//!
//! - **Weakest** (McMillan'): produces the most general interpolant
//! - **Default** (Pudlak): balanced, proof-structure-sensitive
//! - **Strongest** (McMillan): produces the most specific interpolant
//!
//! # References
//!
//! - McMillan, "Interpolation and SAT-based Model Checking", CAV 2003.
//! - Pudlak, "Lower bounds for resolution and cutting plane proofs", JSL 1997.

use super::handles::Term;

/// Strength/specificity of the interpolant to extract from an UNSAT proof.
///
/// All three strengths produce valid Craig interpolants. They differ in how
/// shared-variable pivot literals are handled at resolution steps in the proof:
///
/// - `Weakest`: treats shared pivots as B-local (conjunction), producing a
///   more general interpolant closer to B. Corresponds to McMillan' (dual).
/// - `Default`: symmetric Pudlak treatment of shared pivots, producing a
///   balanced interpolant sensitive to the proof structure.
/// - `Strongest`: treats shared pivots as A-local (disjunction), producing a
///   more specific interpolant closer to A. Corresponds to McMillan (2003).
///
/// For PDR/CEGAR-style lemma learning, weaker interpolants often converge
/// faster because they generalize more aggressively.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
pub enum InterpolantStrength {
    /// McMillan' (dual): weakest (most general), B-complement projection.
    /// Shared pivots treated as B-local: I = I1 /\ I2.
    Weakest,
    /// Pudlak (1997): proof-structure-sensitive, balanced.
    /// Shared pivots: I = (I1 \/ p) /\ (I2 \/ ~p).
    #[default]
    Default,
    /// McMillan (2003): strongest (most specific), A-local projection.
    /// Shared pivots treated as A-local: I = I1 \/ I2.
    Strongest,
}

impl std::fmt::Display for InterpolantStrength {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Weakest => write!(f, "weakest (McMillan')"),
            Self::Default => write!(f, "default (Pudlak)"),
            Self::Strongest => write!(f, "strongest (McMillan)"),
        }
    }
}

/// Result of a successful interpolant computation.
///
/// Contains the interpolant term and metadata about how it was produced.
#[derive(Debug, Clone)]
pub struct InterpolantResult {
    /// The interpolant term I such that A |= I and I /\ B is UNSAT.
    /// Mentions only variables shared between the A and B groups.
    interpolant: Term,
    /// The strength/algorithm used to produce this interpolant.
    strength: InterpolantStrength,
}

impl InterpolantResult {
    /// Create a new interpolant result.
    pub(crate) fn new(interpolant: Term, strength: InterpolantStrength) -> Self {
        Self {
            interpolant,
            strength,
        }
    }

    /// The interpolant term.
    #[must_use]
    pub fn interpolant(&self) -> Term {
        self.interpolant
    }

    /// The strength/algorithm used.
    #[must_use]
    pub fn strength(&self) -> InterpolantStrength {
        self.strength
    }
}

/// Result of a successful path interpolant computation.
///
/// Given a sequence of formula groups (A1, A2, ..., An) whose conjunction is
/// UNSAT, path interpolants I1, I2, ..., I(n-1) satisfy:
/// - A1 |= I1
/// - Ii /\ A(i+1) |= I(i+1)  for each i in 1..n-2
/// - I(n-1) /\ An is UNSAT
/// - Each Ii uses only symbols shared between {A1..Ai} and {A(i+1)..An}
///
/// Path interpolants generalize binary Craig interpolation to sequences and
/// are essential for CHC solving (DAR engine's `globalStrengthen`) and
/// CEGAR refinement loops.
///
/// # References
///
/// - Ermis, Hoenicke, Podelski, "Splitting via Interpolants", VMCAI 2012.
/// - McMillan, "Applications of Craig Interpolation to Model Checking", ICATPN 2005.
#[derive(Debug, Clone)]
pub struct PathInterpolantResult {
    /// The sequence of interpolants I1, ..., I(n-1) for n partitions.
    interpolants: Vec<Term>,
    /// The strength/algorithm used to produce these interpolants.
    strength: InterpolantStrength,
}

impl PathInterpolantResult {
    /// Create a new path interpolant result.
    pub(crate) fn new(interpolants: Vec<Term>, strength: InterpolantStrength) -> Self {
        Self {
            interpolants,
            strength,
        }
    }

    /// The sequence of path interpolants.
    ///
    /// For n partitions, returns n-1 interpolants.
    #[must_use]
    pub fn interpolants(&self) -> &[Term] {
        &self.interpolants
    }

    /// The number of interpolants in the sequence.
    #[must_use]
    pub fn len(&self) -> usize {
        self.interpolants.len()
    }

    /// Whether the interpolant sequence is empty (degenerate: 0 or 1 partitions).
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.interpolants.is_empty()
    }

    /// The strength/algorithm used.
    #[must_use]
    pub fn strength(&self) -> InterpolantStrength {
        self.strength
    }
}
