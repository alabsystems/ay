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

/// How strictly proof-based interpolant extraction treats the proof.
///
/// Workstream D, Rung 1 (CHC-COMP 2026; the development design notes
/// DESIGN_lra_interp_tpa.md` at `9598c4206`, §4.1). Owner: WP-D1-P (proof substrate).
///
/// - `Legacy` is the historical traversal, byte-identical to
///   [`crate::api::Solver::get_interpolant_with_strength`]: a missing premise
///   defaults to `true`, theory-lemma fallbacks are on, and locality is a
///   `debug_assert`.
/// - `Explicit` fails closed: a Trust step, a missing premise, an
///   unclassified literal or pivot, an uncertified or undecodable theory leaf,
///   or a non-local variable is an [`InterpolantFailure`], never a degraded
///   `true`/`false`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[non_exhaustive]
pub enum InterpolantMode {
    /// Historical traversal (default); unchanged behaviour.
    #[default]
    Legacy,
    /// Fail-closed traversal (INV-4 of the Workstream D design).
    Explicit,
}

/// Why fail-closed (`InterpolantMode::Explicit`) extraction refused a proof.
///
/// `step` is the index of the offending proof step in the proof's step list.
/// Owner: WP-D1-P. `NoProof` and `InvalidGroups` cover the method's own
/// preconditions (no UNSAT proof available; an empty/oversized group list or
/// a mask outside it) so that the entry point never needs `Option`.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum InterpolantFailure {
    /// A `Trust`-rule step (an unjustified hole) was reached.
    TrustStep {
        /// Proof step index.
        step: usize,
    },
    /// A theory leaf whose Farkas certificate was rejected on re-verification.
    UncertifiedLeaf {
        /// Proof step index.
        step: usize,
    },
    /// A theory leaf whose rows could not be decoded into linear constraints.
    UndecodableLeaf {
        /// Proof step index.
        step: usize,
    },
    /// A literal or pivot that no A/B occurrence classifies.
    UnclassifiedLiteral {
        /// Proof step index.
        step: usize,
    },
    /// A resolution step whose premise is absent.
    MissingPremise {
        /// Proof step index.
        step: usize,
    },
    /// A reachable step the fail-closed extractor has no interpolation rule
    /// for (a subproof anchor, a DRUP step, a resolution chain whose pivots
    /// cannot be recovered, or an inference rule outside the supported
    /// Boolean/arithmetic set).
    UnsupportedStep {
        /// Proof step index.
        step: usize,
    },
    /// The produced interpolant mentions a variable outside the shared set.
    NonLocal {
        /// Name of the offending variable.
        var: String,
    },
    /// The last check did not produce an UNSAT proof (proofs off, not UNSAT,
    /// or an empty proof).
    NoProof,
    /// The group/mask arguments are malformed (no groups, more than 128
    /// groups, a mask selecting a group that does not exist, or a mask that
    /// selects all or none of the groups).
    InvalidGroups,
}

impl InterpolantFailure {
    /// Stable snake-case name of the failure kind (for counters and logs).
    #[must_use]
    pub fn kind_name(&self) -> &'static str {
        match self {
            Self::TrustStep { .. } => "trust_step",
            Self::UncertifiedLeaf { .. } => "uncertified_leaf",
            Self::UndecodableLeaf { .. } => "undecodable_leaf",
            Self::UnclassifiedLiteral { .. } => "unclassified_literal",
            Self::MissingPremise { .. } => "missing_premise",
            Self::UnsupportedStep { .. } => "unsupported_step",
            Self::NonLocal { .. } => "non_local",
            Self::NoProof => "no_proof",
            Self::InvalidGroups => "invalid_groups",
        }
    }

    /// Proof step index the failure is attributed to, when it has one.
    #[must_use]
    pub fn step(&self) -> Option<usize> {
        match self {
            Self::TrustStep { step }
            | Self::UncertifiedLeaf { step }
            | Self::UndecodableLeaf { step }
            | Self::UnclassifiedLiteral { step }
            | Self::MissingPremise { step }
            | Self::UnsupportedStep { step } => Some(*step),
            Self::NonLocal { .. } | Self::NoProof | Self::InvalidGroups => None,
        }
    }
}

impl std::fmt::Display for InterpolantFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::TrustStep { step } => write!(f, "trust step at proof step {step}"),
            Self::UncertifiedLeaf { step } => {
                write!(f, "uncertified theory leaf at proof step {step}")
            }
            Self::UndecodableLeaf { step } => {
                write!(f, "undecodable theory leaf at proof step {step}")
            }
            Self::UnclassifiedLiteral { step } => {
                write!(f, "unclassified literal at proof step {step}")
            }
            Self::MissingPremise { step } => write!(f, "missing premise at proof step {step}"),
            Self::UnsupportedStep { step } => write!(f, "unsupported proof step {step}"),
            Self::NonLocal { var } => write!(f, "non-local variable {var}"),
            Self::NoProof => write!(f, "no UNSAT proof available"),
            Self::InvalidGroups => write!(f, "invalid interpolation groups or masks"),
        }
    }
}

impl std::error::Error for InterpolantFailure {}
