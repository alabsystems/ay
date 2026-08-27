// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked data carried from ITE-lift recognition to proof emission.

use ay_core::{FarkasAnnotation, TermId};

/// A preprocessed `(cl (ite c A B))` derived from an authored
/// `P(ite c u v)`, together with every checked term needed to replace the
/// trusted leaf by an `ite_intro`/linear-arithmetic derivation.
pub(super) struct IteLiftPlan {
    /// `false`: the goal is the packed `(ite c A B)` (the historical shape).
    /// `true`: the goal is the GUARDED THEN-PROJECTION `(or (not c) A)` that
    /// arithmetic-ITE clausification leaves when the else branch is trivially
    /// true; only the then-side transfer is emitted, packed by `or_neg`.
    pub(super) guarded_then_or: bool,
    pub(super) orig: TermId,
    /// Canonical source whose parsed surface spells `orig`.
    pub(super) defining_source: Option<TermId>,
    /// Optional second authored assertion used by bound substitution.
    pub(super) bound: Option<TermId>,
    /// Exact coefficients accepted by the independent Farkas checker.
    pub(super) then_coeffs: FarkasAnnotation,
    pub(super) else_coeffs: FarkasAnnotation,
    pub(super) cond: TermId,
    pub(super) lifted_then: TermId,
    pub(super) lifted_else: TermId,
    pub(super) goal: TermId,
    pub(super) ite_term: TermId,
    pub(super) eq_then: TermId,
    pub(super) eq_else: TermId,
    pub(super) ite_def: TermId,
    pub(super) and_term: TermId,
    pub(super) intro_eq: TermId,
}
