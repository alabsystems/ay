// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// ===========================================================================
// Conflict explanation (`crate::explain`)
// ===========================================================================

/// One trail literal in a conflict: `p cond 0`, asserted TRUE.
///
/// `roots` is supplied by the CALLER, so the oracle can drive every entry point
/// below on z3's own root list rather than only through a consumer. AY verifies
/// it in both directions and declines a list that is wrong either way.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OExplainLit {
    /// The trail literal's signed id. Never `0`.
    pub lit: i32,
    /// Integer coefficients, low-to-high.
    pub p: Vec<BigInt>,
    /// The sign condition asserted TRUE.
    pub cond: OISignCond,
    /// Every real root of `p`, ascending.
    pub roots: Vec<ODyadicAnum>,
}

impl OExplainLit {
    fn inner(&self) -> explain::ConflictLit {
        explain::ConflictLit {
            lit: self.lit,
            p: self.p.clone(),
            cond: self.cond.inner(),
            roots: self.roots.iter().map(|r| r.0.clone()).collect(),
        }
    }
}

fn explain_lits(ls: &[OExplainLit]) -> Vec<explain::ConflictLit> {
    ls.iter().map(OExplainLit::inner).collect()
}

/// A learned clause.
///
/// Carries NO validity flag: the campaign's third blind-spot pattern is a stored
/// flag the headline metric is read off, and this type is deliberately shaped so
/// that the only way to learn whether the clause is implied is to call
/// [`oexplain_clause_is_valid`] on the cited literals.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OExplanation {
    /// The clause literals: the negation of each cited trail literal.
    pub lits: Vec<i32>,
    /// The trail literals cited.
    pub cited: Vec<i32>,
}

/// **The defining property.** Is `\/_j !L_j` a theory consequence — equivalently,
/// is `/\_j L_j` unsatisfiable over the reals?
///
/// `Some(true)` is a proof, `Some(false)` a refutation with a witness available
/// from [`oexplain_countermodel`], `None` a decline.
#[must_use]
pub fn oexplain_clause_is_valid(lits: &[OExplainLit]) -> Option<bool> {
    explain::clause_is_valid(&explain_lits(lits))
}

/// The real number witnessing that the clause is NOT valid, when there is one.
///
/// Exposed separately so the oracle can adjudicate the WITNESS rather than the
/// verdict: an unwitnessed witness is a blind spot, and z3 re-evaluates this
/// point against every cited literal.
#[must_use]
pub fn oexplain_countermodel(lits: &[OExplainLit]) -> Option<Option<ODyadicAnum>> {
    explain::clause_countermodel(&explain_lits(lits)).map(|o| o.map(ODyadicAnum))
}

/// Is the clause FALSE under the trail — every literal the negation of an
/// asserted one? Total: it cannot decline.
#[must_use]
pub fn oexplain_clause_is_falsified(clause: &[i32], trail: &[i32]) -> bool {
    explain::clause_is_falsified(clause, trail)
}

/// Explain a univariate conflict. `None` when there is no conflict, when a step
/// declines, or when the clause cannot be PROVED implied.
#[must_use]
pub fn oexplain_univariate(lits: &[OExplainLit]) -> Option<OExplanation> {
    explain::explain_univariate(&explain_lits(lits)).map(|e| OExplanation {
        lits: e.lits().to_vec(),
        cited: e.cited().to_vec(),
    })
}

/// The pairs whose root ordering matters at the sample point — the restriction
/// that keeps the projection from taking all `O(m^2)` resultants.
#[must_use]
pub fn oexplain_relevant_pairs(lits: &[OExplainLit]) -> Option<Vec<(usize, usize)>> {
    explain::relevant_pairs(&explain_lits(lits))
}

/// Which projection factor a polynomial came from.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OProjKind {
    /// Leading coefficient of input `i` in the projected variable.
    LeadingCoeff(usize),
    /// Discriminant of input `i`.
    Discriminant(usize),
    /// Resultant of inputs `i` and `j`.
    Resultant(usize, usize),
}

/// The CAD projection, with the degree report.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OProjection {
    /// Each factor and where it came from.
    pub factors: Vec<(OProjKind, OYPoly)>,
    /// Largest total degree among the inputs.
    pub in_max_total_degree: u32,
    /// Largest total degree among the outputs.
    pub out_max_total_degree: u32,
    /// Outputs that are non-zero constants: no roots, so no cell boundary.
    pub constant_factors: usize,
}

/// [`crate::explain::project`] — leading coefficients, discriminants and the
/// resultants of `pairs`.
#[must_use]
pub fn oexplain_project(polys: &[OBiPoly], pairs: &[(usize, usize)]) -> Option<OProjection> {
    let inner: Vec<RPoly<MPolyZ>> = polys.iter().map(|p| p.0.clone()).collect();
    let p = explain::project(&inner, pairs)?;
    Some(OProjection {
        factors: p
            .factors
            .iter()
            .map(|f| {
                let k = match f.kind {
                    explain::ProjKind::LeadingCoeff(i) => OProjKind::LeadingCoeff(i),
                    explain::ProjKind::Discriminant(i) => OProjKind::Discriminant(i),
                    explain::ProjKind::Resultant(i, j) => OProjKind::Resultant(i, j),
                };
                (k, OYPoly(f.poly.clone()))
            })
            .collect(),
        in_max_total_degree: p.in_max_total_degree,
        out_max_total_degree: p.out_max_total_degree,
        constant_factors: p.constant_factors,
    })
}

/// The declared ceiling on literals per conflict.
#[must_use]
pub fn oexplain_max_conflict_lits() -> usize {
    explain::MAX_CONFLICT_LITS
}

/// The declared ceiling on distinct roots in the merged decomposition.
#[must_use]
pub fn oexplain_max_conflict_roots() -> usize {
    explain::MAX_CONFLICT_ROOTS
}
