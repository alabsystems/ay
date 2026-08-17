// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound provenance, intervals, and simplex variable state.

use super::{BigRational, HashSet, One, Rational, SmallVec, TermId};

/// Bound type for a variable
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BoundType {
    /// Lower bound: x >= c
    Lower,
    /// Upper bound: x <= c
    Upper,
}

/// Heap key for greatest-error pivot selection (#4919 Phase 1).
///
/// Keyed by (violation_magnitude_f64, var_id). Rust's BinaryHeap is a max-heap,
/// so the variable with the largest bound violation is extracted first.
/// Uses `f64::total_cmp` for deterministic total ordering (NaN sorts last).
///
/// Reference: Z3 `select_greatest_error_var()` in `theory_arith_core.h:2270-2300`.
#[derive(Clone, Copy, Debug)]
pub(crate) struct ErrorKey(pub(crate) f64, pub(crate) u32);

impl PartialEq for ErrorKey {
    fn eq(&self, other: &Self) -> bool {
        self.0.total_cmp(&other.0) == std::cmp::Ordering::Equal && self.1 == other.1
    }
}
impl Eq for ErrorKey {}

impl PartialOrd for ErrorKey {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for ErrorKey {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // Primary: largest error first (max-heap naturally returns this)
        // Secondary: smallest var index first (determinism tiebreaker)
        self.0
            .total_cmp(&other.0)
            .then_with(|| other.1.cmp(&self.1))
    }
}

/// Eager explanation data captured at bound derivation time (#6617).
///
/// Equivalent to Z3's `m_explain_bound` closure in `implied_bound.h:36`.
/// When called to produce reasons, iterates over `contributing_vars` and
/// fetches each variable's current direct bound reason. Never recurses
/// into the depth-limited `collect_row_reasons_recursive` walker.
///
/// Reference: Z3 `limit_j` (bound_analyzer_on_row.h:298-321) captures
/// the row by value and fetches bound witnesses at explanation time.
#[derive(Debug, Clone)]
pub(crate) struct BoundExplanation {
    /// Variables whose bounds contributed to this derivation, with the
    /// direction of bound used (true = upper, false = lower).
    /// Excludes the target variable itself.
    /// Z3 equivalent: the loop body in `limit_j` (bound_analyzer_on_row.h:308-316).
    pub(crate) contributing_vars: SmallVec<[(u32, bool); 8]>,
}

/// An implied bound derived from a tableau row during `compute_implied_bounds`.
///
/// Stores the bound value, strictness flag, and eagerly-captured explanation
/// data for flat (non-recursive) reason collection (#6617).
///
/// Reference: Z3 stores a lazy explanation closure on `implied_bound`
/// (`reference/z3/src/math/lp/implied_bound.h:36`). AY captures the same
/// data eagerly in `BoundExplanation` at derivation time.
#[derive(Debug, Clone)]
pub(crate) struct ImpliedBound {
    /// The bound value
    pub(crate) value: Rational,
    /// Whether the bound is strict
    pub(crate) strict: bool,
    /// The tableau row index from which this bound was derived.
    /// Used for lazy reason collection in `collect_row_reasons_recursive`.
    /// `usize::MAX` is the sentinel for direct bounds (which use `Bound.reason_pairs()`).
    pub(crate) row_idx: usize,
    /// Eager explanation data captured at derivation time (#6617).
    /// `None` for direct bounds (sentinel row_idx = usize::MAX) and for
    /// legacy implied bounds created before this field was added.
    /// When present, `collect_reasons_from_explanation` uses this instead
    /// of the depth-limited recursive walker.
    pub(crate) explanation: Option<BoundExplanation>,
}

/// One finite endpoint of an expression interval.
///
/// The numeric value alone is insufficient for strict propagation because an
/// open endpoint at zero proves a strict sign while a closed endpoint at zero
/// does not (`#6582`).
///
/// #8406: Changed from `BigRational` to `Rational` to eliminate heap allocation
/// in `compute_expr_interval` hot path. Most interval arithmetic involves small
/// coefficients and bounds that fit in i64, so the inline `Small(n, d)` path
/// avoids all allocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct IntervalEndpoint {
    /// Endpoint value.
    pub(crate) value: Rational,
    /// Whether the endpoint is open.
    pub(crate) strict: bool,
}

impl IntervalEndpoint {
    pub(crate) fn new(value: Rational, strict: bool) -> Self {
        Self { value, strict }
    }
}

/// Finite lower/upper bounds for a linear expression.
///
/// `None` means the corresponding side is unbounded.
pub(crate) type ExprInterval = (Option<IntervalEndpoint>, Option<IntervalEndpoint>);

/// Tracks the complete justification for a bound (#8151).
///
/// Mirrors Z3's `u_dependency*` pattern (`reference/z3/src/util/dependency.h`,
/// `reference/z3/src/math/lp/column.h:41-53`). Each bound carries a provenance
/// that traces back to ALL original constraints that contributed to establishing
/// it. When bounds are derived through tableau rows or combined from multiple
/// assertions, provenances are joined via `BoundProvenance::Join`.
///
/// The existing `Bound::reasons` / `reason_values` / `reason_scales` fields
/// remain for the Farkas certificate path (hot path for direct bounds).
/// `BoundProvenance` provides the complete dependency chain needed for
/// soundness when bounds are derived through multiple levels of implication.
///
/// Reference: Z3 `u_dependency` (`reference/z3/src/util/dependency.h`),
/// `column.h:41-53` (per-column bound witnesses),
/// `lar_solver.cpp:175-191` (`get_infeasibility_explanation_for_inf_sign`).
#[derive(Debug, Clone)]
pub enum BoundProvenance {
    /// Bound from a single atom assertion.
    Atom {
        /// The atom term that justified this bound.
        term: TermId,
        /// The Boolean value of the atom in the current assignment.
        value: bool,
    },
    /// Bound from a shared equality (Nelson-Oppen) or Diophantine analysis
    /// with multiple reason literals.
    SharedEquality {
        /// All reason literals that justify this bound.
        reasons: SmallVec<[(TermId, bool); 4]>,
    },
    /// Bound derived from multiple contributing bounds (Z3's `mk_join`).
    /// Used when a bound is tightened or derived through a tableau row.
    Join {
        /// The contributing provenances.
        parts: SmallVec<[Box<Self>; 2]>,
    },
    /// Axiom or internal constraint (no external reason needed).
    Axiom,
}

impl BoundProvenance {
    /// Flatten the provenance DAG to collect all atom reasons.
    ///
    /// Equivalent to Z3's `dependency_manager::linearize` which walks the
    /// `u_dependency` tree and collects all leaf values.
    pub fn collect_reasons(&self, out: &mut Vec<(TermId, bool)>) {
        match self {
            Self::Atom { term, value } => {
                if !term.is_sentinel() {
                    out.push((*term, *value));
                }
            }
            Self::SharedEquality { reasons } => {
                for &(term, value) in reasons {
                    if !term.is_sentinel() {
                        out.push((term, value));
                    }
                }
            }
            Self::Join { parts } => {
                for part in parts {
                    part.collect_reasons(out);
                }
            }
            Self::Axiom => {}
        }
    }

    /// Merge two provenances (Z3's `mk_join` equivalent).
    ///
    /// Creates a `Join` node combining both provenances. Axiom nodes are
    /// identity elements. Nested Joins are flattened to avoid deep trees.
    pub fn join(self, other: Self) -> Self {
        match (self, other) {
            // Axiom joined with anything is the other side
            (Self::Axiom, other) => other,
            (this, Self::Axiom) => this,
            // Flatten nested joins
            (Self::Join { mut parts }, Self::Join { parts: other_parts }) => {
                parts.extend(other_parts);
                Self::Join { parts }
            }
            (Self::Join { mut parts }, other) => {
                parts.push(Box::new(other));
                Self::Join { parts }
            }
            (this, Self::Join { mut parts }) => {
                parts.insert(0, Box::new(this));
                Self::Join { parts }
            }
            // Two non-Join, non-Axiom nodes
            (a, b) => Self::Join {
                parts: SmallVec::from_buf([Box::new(a), Box::new(b)]),
            },
        }
    }

    /// Collect all reasons into a deduplicated vector.
    ///
    /// Convenience method for conflict explanation. Uses a `HashSet` to
    /// deduplicate (same term+value pair may appear from multiple join branches).
    pub(crate) fn collect_reasons_dedup(&self) -> Vec<(TermId, bool)> {
        let mut raw = Vec::new();
        self.collect_reasons(&mut raw);
        // Deduplicate while preserving order
        let mut seen = HashSet::default();
        raw.retain(|pair| seen.insert(*pair));
        raw
    }
}

/// A bound with its value and the atoms that established it
#[derive(Debug, Clone)]
pub struct Bound {
    /// The bound value (fast-path i64 with BigRational fallback).
    pub value: Rational,
    /// The atom terms that established this bound.
    /// Multiple reasons can exist when bounds are derived from the LIA solver's
    /// Diophantine analysis, which combines information from multiple constraints.
    pub reasons: Vec<TermId>,
    /// The Boolean values of each reason in the current assignment.
    ///
    /// When the SAT layer assigns an atom `t` to `false`, the theory asserts the
    /// negation of `t` (e.g. `!(x <= 5)` becomes `x > 5`). For conflict clauses
    /// to be sound, we must preserve that polarity.
    pub reason_values: Vec<bool>,
    /// Farkas scaling factors for each reason atom.
    ///
    /// When an atom like `5x <= c` is normalized to a per-variable bound `x <= c/5`,
    /// the Farkas coefficient must account for this normalization. The scale factor
    /// is `1/|coeff|` where `coeff` is the original variable coefficient in the atom.
    /// For atoms that directly constrain a single variable with coefficient 1,
    /// the scale is 1. Parallel to `reasons` — one entry per reason.
    ///
    /// #8406: Changed from `Vec<BigRational>` to `Vec<Rational>` to eliminate heap
    /// allocation on every bound assertion. Most scales are 1 (Rational::Small(1,1)),
    /// which is zero-allocation inline storage.
    pub reason_scales: Vec<Rational>,
    /// Whether the bound is strict (< or >) vs non-strict (<= or >=)
    pub strict: bool,
    /// Complete justification chain for this bound (#8151).
    ///
    /// Tracks ALL original constraints that contributed to establishing this
    /// bound, including transitive dependencies through the tableau.
    /// Used by conflict explanation to ensure completeness when the
    /// `reasons`/`reason_values` fields are insufficient (e.g., derived bounds).
    ///
    /// When `None`, falls back to the `reasons`/`reason_values` fields
    /// (backward compatible with pre-#8151 code paths).
    pub provenance: Option<BoundProvenance>,
}

impl Bound {
    /// Create a bound with reason tracking and debug invariant checks.
    pub fn new(
        value: Rational,
        reasons: Vec<TermId>,
        reason_values: Vec<bool>,
        reason_scales: Vec<Rational>,
        strict: bool,
    ) -> Self {
        debug_assert_eq!(
            reasons.len(),
            reason_values.len(),
            "reasons/values mismatch"
        );
        debug_assert!(
            reason_scales.len() <= reasons.len(),
            "more scales than reasons"
        );
        // Build provenance from direct reasons (#8151).
        let provenance = Self::build_provenance_from_reasons(&reasons, &reason_values);
        Self {
            value,
            reasons,
            reason_values,
            reason_scales,
            strict,
            provenance,
        }
    }

    /// Build a `BoundProvenance` from the parallel reasons/values vectors.
    ///
    /// Single-atom bounds get `Atom` provenance. Multi-reason bounds get
    /// `SharedEquality` provenance. Empty reasons get `Axiom`.
    fn build_provenance_from_reasons(
        reasons: &[TermId],
        reason_values: &[bool],
    ) -> Option<BoundProvenance> {
        let non_sentinel: SmallVec<[(TermId, bool); 4]> = reasons
            .iter()
            .zip(reason_values.iter())
            .filter(|(t, _)| !t.is_sentinel())
            .map(|(&t, &v)| (t, v))
            .collect();
        match non_sentinel.len() {
            0 => Some(BoundProvenance::Axiom),
            1 => Some(BoundProvenance::Atom {
                term: non_sentinel[0].0,
                value: non_sentinel[0].1,
            }),
            _ => Some(BoundProvenance::SharedEquality {
                reasons: non_sentinel,
            }),
        }
    }

    /// Create a bound with no reason tracking (tests only).
    ///
    /// Production code must always provide reasons to prevent sentinel-only
    /// bounds that degrade to Unknown or produce unsound conflicts (#4919).
    #[cfg(test)]
    pub fn without_reasons(value: Rational, strict: bool) -> Self {
        Self {
            value,
            reasons: Vec::new(),
            reason_values: Vec::new(),
            reason_scales: Vec::new(),
            strict,
            provenance: None,
        }
    }

    /// Iterate over `(term, value)` pairs for reason atoms.
    ///
    /// Convenience accessor that zips the parallel `reasons` and
    /// `reason_values` vectors.
    pub fn reason_pairs(&self) -> impl Iterator<Item = (TermId, bool)> + '_ {
        self.reasons
            .iter()
            .copied()
            .zip(self.reason_values.iter().copied())
    }

    /// Collect the complete reason set justifying this bound.
    ///
    /// Prefers the provenance chain (#8151) when present, which traces ALL
    /// contributing atoms including transitive dependencies through the
    /// tableau; falls back to the direct `reasons`/`reason_values` fields.
    /// Sentinel reasons are filtered out. Conflict builders that cite a
    /// bound's justification MUST use this (not `reason_pairs`) so learned
    /// clauses are not stronger than the theory lemma they encode.
    pub fn complete_reason_pairs(&self) -> Vec<(TermId, bool)> {
        if let Some(provenance) = &self.provenance {
            let pairs = provenance.collect_reasons_dedup();
            if !pairs.is_empty() {
                return pairs;
            }
        }
        self.reason_pairs()
            .filter(|(term, _)| !term.is_sentinel())
            .collect()
    }

    /// Convert to InfRational target for simplex assignment.
    pub(crate) fn as_inf(&self, bound_type: BoundType) -> InfRational {
        // value is already Rational -- no conversion needed.
        let x = self.value.clone();
        if self.strict {
            let eps = match bound_type {
                BoundType::Lower => Rational::one(),
                BoundType::Upper => -Rational::one(),
            };
            InfRational::new_rat(x, eps)
        } else {
            InfRational::from_rat(x)
        }
    }

    /// Approximate the bound value as f64, avoiding BigRational allocation.
    /// Used for heuristic heap keys (#6617).
    #[inline]
    pub(crate) fn value_approx_f64(&self) -> f64 {
        self.value.approx_f64()
    }

    /// Convert bound value to BigRational (for cold-path arithmetic).
    /// Hot-path comparisons should use `self.value` directly (Rational).
    #[inline]
    pub fn value_big(&self) -> BigRational {
        self.value.to_big()
    }
}

pub(crate) use crate::infrational::InfRational;

/// Status of a variable in the simplex tableau
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VarStatus {
    /// Non-basic variable: can be pivoted with a basic variable
    NonBasic,
    /// Basic variable: defined by a row in the tableau
    Basic(usize), // row index
}

// TableauRow is defined in crate::tableau (extracted for code health, #5970).
// Re-exported here so existing `use types::TableauRow` imports continue to work.
pub(crate) use crate::tableau::RowPrecision;
pub(crate) use crate::tableau::TableauRow;

/// Information about an LRA variable
#[derive(Debug, Clone, Default)]
pub(crate) struct VarInfo {
    /// Current value assignment
    /// Current value assignment (infinitesimal-extended for strict bounds)
    pub(crate) value: InfRational,
    /// Lower bound (if any)
    pub(crate) lower: Option<Bound>,
    /// Upper bound (if any)
    pub(crate) upper: Option<Bound>,
    /// Status in tableau
    pub(crate) status: Option<VarStatus>,
}
