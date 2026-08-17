// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact linearization for monomials whose factors are assertion-pinned.
//!
//! McCormick envelopes require a finite box, while tangent planes are only
//! model-point approximations. Neither limitation applies when the assertions
//! already pin every factor but one: `m = x*y` and `x = c` entail `m = c*y`
//! for every real `y`. A zero-pinned factor similarly entails `m = 0` even
//! when several other factors remain free.
//!
//! [`NraSolver::fixed_factor_values`] is captured before any tentative scope
//! exists, so every emitted equality is implied by asserted atoms. These
//! identities therefore remain valid on the exact-lemma UNSAT recheck.

use ay_core::term::TermId;
use ay_lra::GomoryCut;
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::monomial::Monomial;
use crate::NraSolver;

/// Saturation passes for pins through nested monomial definitions.
const FIXED_SATURATION_PASSES: usize = 8;

/// An internal inconsistency in the free-factor count. Declining the identity
/// on this error is fail-closed: subsequent exact paths can only lose a lemma.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FixedFactorLinearizationError {
    MissingFreeVariable,
}

fn require_free_variable(free: Option<TermId>) -> Result<TermId, FixedFactorLinearizationError> {
    free.ok_or(FixedFactorLinearizationError::MissingFreeVariable)
}

impl NraSolver<'_> {
    /// Pins read directly from asserted affine atoms.
    ///
    /// This is the primary source because LRA fixed-term substitution can make
    /// `get_bounds` return no pair for a variable that an equality pins.
    fn asserted_pins(&self) -> Vec<(TermId, BigRational)> {
        use crate::univariate::{MultiAtom, Rel};
        let mut lower: Vec<(TermId, BigRational)> = Vec::new();
        let mut upper: Vec<(TermId, BigRational)> = Vec::new();
        let mut pins: Vec<(TermId, BigRational)> = Vec::new();

        for &(atom, value) in &self.asserted {
            let Some(MultiAtom::Constraint(c)) = self.atom_to_multi(atom, value) else {
                continue;
            };
            let mut var: Option<(TermId, BigRational)> = None;
            let mut constant = BigRational::zero();
            let mut in_fragment = true;
            for (mono, coeff) in &c.poly.terms {
                match mono.len() {
                    0 => constant = coeff.clone(),
                    1 if var.is_none() => var = Some((mono[0], coeff.clone())),
                    _ => {
                        in_fragment = false;
                        break;
                    }
                }
            }
            if !in_fragment {
                continue;
            }
            let Some((v, a)) = var else { continue };
            if a.is_zero() {
                continue;
            }
            let value = -(&constant) / &a;
            let flip = a < BigRational::zero();
            match c.rel {
                Rel::Eq => pins.push((v, value)),
                Rel::Le | Rel::Ge => {
                    let is_upper = matches!(c.rel, Rel::Le) != flip;
                    if is_upper {
                        upper.push((v, value));
                    } else {
                        lower.push((v, value));
                    }
                }
                Rel::Lt | Rel::Gt | Rel::Ne => {}
            }
        }

        for (v, lo) in &lower {
            if upper.iter().any(|(u, hi)| u == v && hi == lo) {
                pins.push((*v, lo.clone()));
            }
        }
        pins
    }

    /// Recompute assertion-derived factor pins before any tentative scope.
    ///
    /// Seeds only from asserted affine atoms, then saturates through nested
    /// monomial definitions. Reading arbitrary LRA bounds here would admit
    /// shared-equality or implied premises that are absent from `asserted` and
    /// could not authenticate a later NRA conflict. An all-pinned monomial has
    /// the product value; any zero-pinned factor makes its monomial zero. A
    /// call inside a tentative scope clears the authority and declines closed.
    pub(crate) fn refresh_fixed_factor_values(&mut self) {
        self.fixed_factor_values.clear();
        self.fixed_lin_emitted.clear();
        if self.tentative_depth != 0 {
            tracing::error!(
                tentative_depth = self.tentative_depth,
                "declining fixed-factor snapshot inside a tentative scope"
            );
            return;
        }
        if self.monomials.is_empty() && self.scaled_aliases.is_empty() {
            return;
        }

        let defs: Vec<(Vec<TermId>, TermId, BigRational)> = {
            let mut d: Vec<_> = self
                .products()
                .map(|m| (m.vars.clone(), m.aux_var, m.coeff.clone()))
                .collect();
            d.sort_unstable();
            d
        };

        let mut candidates: Vec<TermId> = Vec::new();
        for (vars, aux, _) in &defs {
            candidates.extend_from_slice(vars);
            candidates.push(*aux);
        }
        candidates.sort_unstable_by_key(|t| t.0);
        candidates.dedup();
        for (v, c) in self.asserted_pins() {
            if candidates.binary_search_by_key(&v.0, |t| t.0).is_ok() {
                self.fixed_factor_values.insert(v, c);
            }
        }

        for _ in 0..FIXED_SATURATION_PASSES {
            let mut changed = false;
            for (vars, aux, coeff) in &defs {
                if self.fixed_factor_values.contains_key(aux) {
                    continue;
                }
                let mut product = BigRational::one();
                let mut all_pinned = true;
                for v in vars {
                    match self.fixed_factor_values.get(v) {
                        Some(c) => product *= c,
                        None => all_pinned = false,
                    }
                }
                if !all_pinned && !product.is_zero() {
                    continue;
                }
                let value = if all_pinned {
                    coeff * product
                } else {
                    BigRational::zero()
                };
                self.fixed_factor_values.insert(*aux, value);
                changed = true;
            }
            if !changed {
                break;
            }
        }

        if self.debug {
            let linearizable = defs
                .iter()
                .filter(|(vars, _, _)| {
                    vars.iter()
                        .filter(|v| !self.fixed_factor_values.contains_key(*v))
                        .count()
                        <= 1
                })
                .count();
            tracing::debug!(
                "[NRA] fixed-factor pins: {} pinned; {}/{} monomials become exactly linear",
                self.fixed_factor_values.len(),
                linearizable,
                defs.len()
            );
        }
    }

    /// Emit an exact equality when pins leave at most one free factor.
    ///
    /// A zero pin yields `aux = 0`; all factors pinned yields a constant; one
    /// free occurrence yields `aux = c * free`. Multiple free occurrences are
    /// still nonlinear and are declined.
    pub(crate) fn add_fixed_factor_linearization(&mut self, mon: &Monomial) -> usize {
        self.add_fixed_factor_linearization_with_reasons(mon, &[])
    }

    /// Emit the same identity with asserted literals authenticating a global
    /// recheck. Tentative callers use the reasonless wrapper above.
    pub(crate) fn add_fixed_factor_linearization_with_reasons(
        &mut self,
        mon: &Monomial,
        reasons: &[(TermId, bool)],
    ) -> usize {
        if self.fixed_factor_values.is_empty() || mon.vars.is_empty() {
            return 0;
        }
        if self.fixed_lin_emitted.contains(&mon.aux_var) {
            return 0;
        }

        let mut pinned_product = BigRational::one();
        let mut free: Option<TermId> = None;
        let mut free_occurrences = 0usize;
        for &v in &mon.vars {
            match self.fixed_factor_values.get(&v) {
                Some(c) => pinned_product *= c,
                None => {
                    free_occurrences += 1;
                    free = Some(v);
                }
            }
        }
        if free_occurrences == mon.vars.len() {
            return 0;
        }

        let m_var = self.lra.ensure_var_registered(mon.aux_var);
        let scaled_product = &mon.coeff * &pinned_product;
        let (coeffs, bound) = if scaled_product.is_zero() {
            (vec![(m_var, BigRational::one())], BigRational::zero())
        } else if free_occurrences == 0 {
            (vec![(m_var, BigRational::one())], scaled_product)
        } else if free_occurrences == 1 {
            let free = match require_free_variable(free) {
                Ok(free) => free,
                Err(error) => {
                    tracing::error!(?error, "declining inconsistent fixed-factor identity");
                    return 0;
                }
            };
            let f_var = self.lra.ensure_var_registered(free);
            (
                vec![(m_var, BigRational::one()), (f_var, -scaled_product)],
                BigRational::zero(),
            )
        } else {
            return 0;
        };

        for is_lower in [true, false] {
            self.lra.add_gomory_cut(
                &GomoryCut {
                    coeffs: coeffs.clone(),
                    bound: bound.clone(),
                    is_lower,
                    reasons: reasons.to_vec(),
                    source_term: None,
                },
                mon.aux_var,
            );
        }
        self.fixed_lin_emitted.insert(mon.aux_var);

        if self.debug {
            tracing::debug!(
                "[NRA] fixed-factor linearization: exact equality for m={:?} ({} free of {})",
                mon.aux_var,
                free_occurrences,
                mon.vars.len()
            );
        }
        2
    }
}

#[cfg(test)]
#[path = "fixed_factor_tests.rs"]
mod tests;
