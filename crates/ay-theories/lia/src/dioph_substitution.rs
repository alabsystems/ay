// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Diophantine substitution bound feasibility checking.
//!
//! Composes cached Diophantine substitutions and checks whether the composed
//! expressions are feasible given variable bounds. Detects cross-substitution
//! infeasibility in carry-chain / modular patterns.
//! Extracted from `dioph_bridge.rs` to keep each file under 500 lines.

use super::*;

pub(crate) type BoundPair = (Option<BigInt>, Option<BigInt>);

impl LiaSolver<'_> {
    /// Check if Dioph substitutions are infeasible given variable bounds.
    ///
    /// Composes substitutions to detect cross-substitution infeasibility.
    /// When one substitution's LHS appears as an RHS variable in another,
    /// we substitute it in to reveal tighter constraints. For example:
    ///   c1 = 2 - c2 - c3 - c4
    ///   m1 = 1 + 21845*(c1+c2+c3+c4) - (m2+m3+m4+m5)
    /// After substituting c1 → 2 - c2 - c3 - c4:
    ///   m1 = 43691 - (m2+m3+m4+m5)
    /// So M = m1+...+m5 = 43691, which may violate bounds.
    pub(crate) fn check_substitution_bound_feasibility(&self) -> Option<Vec<TheoryLit>> {
        // Build a map of LHS → (coeffs, constant) for substitution composition
        let sub_map: SubstitutionMap<'_> = self
            .dioph_cached_substitutions
            .iter()
            .map(|(tid, cs, c)| (*tid, (cs.as_slice(), c)))
            .collect();

        for (term_id, coeffs, constant) in &self.dioph_cached_substitutions {
            let (composed_coeffs, composed_constant) =
                match Self::compose_substitution(term_id, coeffs, constant, &sub_map) {
                    Some(r) => r,
                    None => continue,
                };

            if let Some(bound_reasons) =
                self.composed_sub_violates_bounds(term_id, &composed_coeffs, &composed_constant)
            {
                return Some(self.build_sub_bound_conflict_all(&bound_reasons));
            }
        }

        self.check_substitution_joint_case_split()
    }

    /// Compose a substitution by replacing RHS variables that are themselves
    /// LHS of other substitutions. Returns (composed_coeffs, composed_constant)
    /// or None if composition yields a degenerate or unhandled self-reference.
    pub(crate) fn compose_substitution(
        term_id: &TermId,
        coeffs: &[(TermId, BigInt)],
        constant: &BigInt,
        sub_map: &SubstitutionMap<'_>,
    ) -> Option<(HashMap<TermId, BigInt>, BigInt)> {
        let mut composed_coeffs: HashMap<TermId, BigInt> = HashMap::default();
        let mut composed_constant = constant.clone();

        for (dep_term, coeff) in coeffs {
            if let Some((sub_coeffs, sub_const)) = sub_map.get(dep_term) {
                composed_constant += coeff * *sub_const;
                for (sub_dep, sub_coeff) in *sub_coeffs {
                    *composed_coeffs.entry(*sub_dep).or_insert_with(BigInt::zero) +=
                        coeff * sub_coeff;
                }
            } else {
                *composed_coeffs
                    .entry(*dep_term)
                    .or_insert_with(BigInt::zero) += coeff;
            }
        }

        composed_coeffs.retain(|_, c| !c.is_zero());

        // Handle self-reference: term_id appears on both sides after composition
        if let Some(sc) = composed_coeffs.remove(term_id) {
            let divisor = BigInt::one() - &sc;
            if divisor.is_zero() {
                return None;
            } else if divisor == BigInt::one() {
                // No change needed
            } else if divisor == -BigInt::one() {
                composed_constant = -composed_constant;
                for v in composed_coeffs.values_mut() {
                    *v = -v.clone();
                }
            } else {
                return None; // Complex divisor: skip
            }
        }

        Some((composed_coeffs, composed_constant))
    }

    /// Check if a composed substitution's implied bounds violate the variable's actual bounds.
    ///
    /// Returns `Some(reasons)` when a violation is detected, where `reasons`
    /// are the asserted literals justifying every bound consulted during the
    /// check. Any conflict built from this violation MUST include these
    /// literals (seed-236 false UNSAT: omitting them produced a theory-invalid
    /// two-literal conflict clause from the substitution equalities alone).
    pub(crate) fn composed_sub_violates_bounds(
        &self,
        term_id: &TermId,
        composed_coeffs: &HashMap<TermId, BigInt>,
        composed_constant: &BigInt,
    ) -> Option<Vec<TheoryLit>> {
        let mut reasons: Vec<TheoryLit> = Vec::new();
        let violated = self.violates_bounds_with_lookup(
            term_id,
            composed_coeffs,
            composed_constant,
            |dep_term| {
                let (pair, lits) = self.get_current_integer_bounds_with_reasons(dep_term);
                reasons.extend(lits);
                pair
            },
        );
        violated.then_some(reasons)
    }

    /// Current integer bounds for a term plus the asserted literals that
    /// justify them.
    ///
    /// Bounds come from three sources, each with its reasons collected:
    /// 1. direct `x OP c` atoms,
    /// 2. linear `a*x OP c` atoms (extended scan),
    /// 3. the LRA tableau's per-variable bounds.
    ///
    /// SOUNDNESS: an LRA bound whose justification cannot be named (no
    /// provenance and no recorded reason atoms) is SKIPPED rather than used,
    /// because an infeasibility proof built on it could not produce a valid
    /// conflict clause. This only weakens the bounds (fewer Diophantine
    /// infeasibility detections), never the soundness.
    pub(crate) fn get_current_integer_bounds_with_reasons(
        &self,
        term_id: TermId,
    ) -> (BoundPair, Vec<TheoryLit>) {
        let (mut lower, mut upper, mut reasons) =
            self.get_integer_bounds_for_term_extended_with_reasons(Some(term_id));
        if let Some((lower_bound, upper_bound)) = self.lra.get_bounds(term_id) {
            if let Some(bound) = lower_bound.as_ref() {
                if let Some(lits) = Self::nameable_lra_bound_reasons(bound) {
                    let candidate = Self::effective_int_lower(bound);
                    lower = Some(lower.map_or(candidate.clone(), |current| current.max(candidate)));
                    reasons.extend(lits);
                }
            }
            if let Some(bound) = upper_bound.as_ref() {
                if let Some(lits) = Self::nameable_lra_bound_reasons(bound) {
                    let candidate = Self::effective_int_upper(bound);
                    upper = Some(upper.map_or(candidate.clone(), |current| current.min(candidate)));
                    reasons.extend(lits);
                }
            }
        }
        ((lower, upper), reasons)
    }

    /// The reason literals justifying an LRA bound, or `None` when the bound
    /// has no nameable justification and must not be used for conflicts.
    ///
    /// Prefers the complete provenance chain (#8151) when present; falls back
    /// to the direct `reasons`/`reason_values` pairs. A bound with no
    /// nameable reason atoms at all is rejected: sentinel-only / reason-free
    /// bounds are a known source of unsound conflicts (#4919), so we refuse
    /// to base an infeasibility proof on them even when their provenance
    /// claims axiom status.
    pub(crate) fn nameable_lra_bound_reasons(bound: &Bound) -> Option<Vec<TheoryLit>> {
        let pairs: Vec<(TermId, bool)> = match bound.provenance.as_ref() {
            Some(provenance) => {
                let mut out = Vec::new();
                provenance.collect_reasons(&mut out);
                out
            }
            None => bound
                .reason_pairs()
                .filter(|(term, _)| !term.is_sentinel())
                .collect(),
        };
        if pairs.is_empty() {
            return None;
        }
        Some(
            pairs
                .into_iter()
                .map(|(term, value)| TheoryLit::new(term, value))
                .collect(),
        )
    }

    pub(crate) fn violates_bounds_with_lookup<F>(
        &self,
        term_id: &TermId,
        composed_coeffs: &HashMap<TermId, BigInt>,
        composed_constant: &BigInt,
        mut get_bounds: F,
    ) -> bool
    where
        F: FnMut(TermId) -> BoundPair,
    {
        let (term_lo, term_hi) = get_bounds(*term_id);
        let mut implied_lo = Some(composed_constant.clone());
        let mut implied_hi = Some(composed_constant.clone());
        for (dep_term, coeff) in composed_coeffs {
            let (dep_lo, dep_hi) = get_bounds(*dep_term);
            let (Some(dl), Some(dh)) = (dep_lo, dep_hi) else {
                return false; // Unbounded dep → can't conclude infeasible
            };
            if coeff.is_positive() {
                if let Some(lo) = implied_lo.as_mut() {
                    *lo += coeff * &dl;
                }
                if let Some(hi) = implied_hi.as_mut() {
                    *hi += coeff * &dh;
                }
            } else {
                if let Some(lo) = implied_lo.as_mut() {
                    *lo += coeff * &dh;
                }
                if let Some(hi) = implied_hi.as_mut() {
                    *hi += coeff * &dl;
                }
            }
        }

        let (Some(il), Some(ih)) = (implied_lo, implied_hi) else {
            return false;
        };
        // Empty implied range
        if il > ih {
            return true;
        }
        // Implied range entirely below lower bound
        if let Some(ref tl) = term_lo {
            if ih < *tl {
                return true;
            }
        }
        // Implied range entirely above upper bound
        if let Some(ref tu) = term_hi {
            if il > *tu {
                return true;
            }
        }
        false
    }

    /// Build a conflict clause from ALL substitution equalities, ALL variable bounds,
    /// and the bound reason literals collected during the infeasibility analysis.
    ///
    /// Used when composed substitution analysis detects infeasibility that involves
    /// multiple substitutions and multiple variable bounds simultaneously.
    ///
    /// SOUNDNESS (seed-236 false UNSAT): `bound_reasons` must contain the
    /// justification literals for every bound the analysis consulted (from
    /// `get_current_integer_bounds_with_reasons`). The legacy
    /// `get_bound_reasons_for_term` loop below only sees direct `x OP c`
    /// atoms and misses `a*x OP c` atoms and LRA-derived bounds; relying on
    /// it alone produced theory-invalid conflicts.
    pub(crate) fn build_sub_bound_conflict_all(
        &self,
        bound_reasons: &[TheoryLit],
    ) -> Vec<TheoryLit> {
        let mut conflict: Vec<TheoryLit> = self
            .dioph_cached_reasons
            .iter()
            .map(|&(lit, val)| TheoryLit::new(lit, val))
            .collect();
        let mut seen: HashSet<TheoryLit> = conflict.iter().copied().collect();
        for &reason in bound_reasons {
            if seen.insert(reason) {
                conflict.push(reason);
            }
        }

        // Add bound reasons for ALL variables in ALL substitutions.
        // Use HashSet for O(1) dedup instead of Vec::contains().
        for (term_id, coeffs, _) in &self.dioph_cached_substitutions {
            for reason in self.get_bound_reasons_for_term(Some(*term_id)) {
                if seen.insert(reason) {
                    conflict.push(reason);
                }
            }
            for (dep_term, _) in coeffs {
                for reason in self.get_bound_reasons_for_term(Some(*dep_term)) {
                    if seen.insert(reason) {
                        conflict.push(reason);
                    }
                }
            }
        }
        conflict
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_joint_case_split_handles_infeasible_and_feasible_paths() {
        let mut terms = TermStore::new();
        let c = terms.mk_var("c", Sort::Int);
        let m = terms.mk_var("m", Sort::Int);
        let s1 = terms.mk_var("s1", Sort::Int);
        let s2 = terms.mk_var("s2", Sort::Int);
        let minus_one = terms.mk_int(BigInt::from(-1));
        let zero = terms.mk_int(BigInt::zero());
        let one = terms.mk_int(BigInt::one());
        let five = terms.mk_int(BigInt::from(5));
        let eq1 = terms.mk_eq(s1, c);
        let eq2 = terms.mk_eq(s2, m);
        let infeasible_lits = [
            terms.mk_ge(c, zero),
            terms.mk_le(c, one),
            terms.mk_ge(m, one),
            terms.mk_le(m, five),
            terms.mk_ge(s1, zero),
            terms.mk_le(s1, zero),
            terms.mk_ge(s2, zero),
            terms.mk_le(s2, zero),
        ];
        let feasible_lits = [
            terms.mk_ge(c, zero),
            terms.mk_le(c, one),
            terms.mk_ge(m, one),
            terms.mk_le(m, five),
            terms.mk_ge(s1, zero),
            terms.mk_le(s1, zero),
            terms.mk_ge(s2, minus_one),
            terms.mk_le(s2, minus_one),
        ];
        let substitutions = vec![
            (
                s1,
                vec![(c, BigInt::one()), (m, -BigInt::one())],
                BigInt::zero(),
            ),
            (
                s2,
                vec![(c, -BigInt::one()), (m, -BigInt::one())],
                BigInt::one(),
            ),
        ];
        let reasons = vec![(eq1, true), (eq2, true)];

        let mut infeasible = LiaSolver::new(&terms);
        for lit in infeasible_lits {
            infeasible.assert_literal(lit, true);
        }
        infeasible.dioph_cached_substitutions = substitutions.clone();
        infeasible.dioph_cached_reasons = reasons.clone();
        let conflict = infeasible
            .check_substitution_bound_feasibility()
            .expect("joint case split should prove infeasible");
        assert!(conflict.contains(&TheoryLit::new(eq1, true)));
        assert!(conflict.contains(&TheoryLit::new(eq2, true)));

        let mut feasible = LiaSolver::new(&terms);
        for lit in feasible_lits {
            feasible.assert_literal(lit, true);
        }
        feasible.dioph_cached_substitutions = substitutions;
        feasible.dioph_cached_reasons = reasons;
        assert!(feasible.check_substitution_bound_feasibility().is_none());
    }
}
