// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Atom-indexed linear parse cache (#C2, lia-hot-loop-plan §C2).
//!
//! `TermStore` is append-only: a `TermId`'s denotation never changes within
//! a solver lifetime, so the linear form of `lhs - rhs` — and every
//! assignment-independent fact derived from it (GCD divisibility of an
//! equality, unit-coefficient modular candidates) — can be parsed once per
//! atom and reused by every subsequent check. Before #C2 the BCP-time
//! cascade (`check_during_propagate_inner`) re-walked the term DAG with
//! fresh `BigInt` maps for every positive equality on every call.
//!
//! Exactness: all cached values are exact `BigInt`/`BigRational` results of
//! the same parse routines that previously ran per check; nothing here is
//! approximated (plan §3.1).

use std::cell::RefCell;
use std::rc::Rc;

use super::*;

/// Assignment-independent linear form and derived facts for an equality
/// `lhs = rhs`, normalized to `Σ(coeff·var) = constant`.
pub(crate) struct CachedLinear {
    /// Coefficients sorted by raw TermId. Zero coefficients (from
    /// cancellation) are preserved to match the uncached parse exactly.
    pub(crate) coeffs: Vec<(TermId, BigInt)>,
    /// Equation constant (right-hand side).
    pub(crate) constant: BigInt,
    /// `gcd(|coeffs|)`; zero when `coeffs` is empty or all-zero.
    pub(crate) gcd: BigInt,
    /// Whether the GCD feasibility test passes (`gcd == 0` counts as a pass,
    /// matching `gcd_test`'s historical skip of all-zero rows).
    pub(crate) gcd_divides: bool,
    /// `(var, other_gcd, residue)` for every variable with `|coeff| == 1`
    /// whose remaining coefficients share `other_gcd > 1`:
    /// `var ≡ residue (mod other_gcd)`.
    pub(crate) modular_candidates: Vec<(TermId, BigInt, BigInt)>,
    /// Some coefficient has `|coeff| == 1`. Reserved as the §C3
    /// modular-pass gate flag (sequencing row 4); the #C2 checks gate on
    /// `modular_candidates.is_empty()` directly.
    #[allow(dead_code)]
    pub(crate) has_unit_coeff_candidate: bool,
    /// `modular_candidates` is non-empty (plan §C2/§C3 gate flag).
    #[allow(dead_code)]
    pub(crate) other_gcd_gt1: bool,
}

/// `(lhs, rhs) → cached linear form` for integer equality/atom parses.
pub(crate) type LinearCacheMap = RefCell<HashMap<(TermId, TermId), Rc<CachedLinear>>>;

/// `term → sorted (var, coeff) affine form` for `term_to_linear_coeffs`.
pub(crate) type AffineCacheMap =
    RefCell<HashMap<TermId, Rc<(Vec<(TermId, BigRational)>, BigRational)>>>;

/// `(lhs, rhs) → (var_index_epoch, parsed dioph row)`. Entries are valid
/// only while the epoch matches: the row stores *indices* into the
/// `build_var_index` bijection, which changes whenever `integer_vars` does.
pub(crate) type DiophParseCacheMap =
    RefCell<HashMap<(TermId, TermId), (u64, Option<Rc<(Vec<(usize, BigInt)>, BigInt)>>)>>;

impl LiaSolver<'_> {
    /// Cached exact linear form of `lhs - rhs` plus derived
    /// assignment-independent facts. Parses on first access only.
    pub(crate) fn cached_linear(&self, lhs: TermId, rhs: TermId) -> Rc<CachedLinear> {
        if let Some(hit) = self.linear_cache.borrow().get(&(lhs, rhs)) {
            return Rc::clone(hit);
        }
        let entry = Rc::new(self.build_cached_linear(lhs, rhs));
        self.linear_cache
            .borrow_mut()
            .insert((lhs, rhs), Rc::clone(&entry));
        entry
    }

    fn build_cached_linear(&self, lhs: TermId, rhs: TermId) -> CachedLinear {
        let (var_coeffs, constant) = self.parse_linear_expr_with_vars_uncached(lhs, rhs);
        let mut coeffs: Vec<(TermId, BigInt)> = var_coeffs.into_iter().collect();
        coeffs.sort_by_key(|(term, _)| term.0);

        // GCD feasibility (assignment-independent, plan §C2): for
        // `Σ(coeff·var) = constant` over integers, gcd(|coeffs|) must divide
        // the constant. `gcd == 0` (no vars / all-zero) is treated as a pass
        // exactly like the historical per-check `gcd_test` skip.
        let gcd = gcd_of_abs(coeffs.iter().map(|(_, c)| c.clone()));
        let gcd_divides = gcd.is_zero() || (&constant % &gcd).is_zero();

        // Modular candidates (assignment-independent): for a variable with
        // coefficient ±1 whose other coefficients share other_gcd > 1,
        // `var ≡ ±constant (mod other_gcd)` (sign per the var's coefficient).
        let mut modular_candidates: Vec<(TermId, BigInt, BigInt)> = Vec::new();
        let mut has_unit_coeff_candidate = false;
        for (var, coeff) in &coeffs {
            if coeff.abs() != BigInt::one() {
                continue;
            }
            has_unit_coeff_candidate = true;
            let other_gcd = gcd_of_abs(
                coeffs
                    .iter()
                    .filter(|(term, _)| term != var)
                    .map(|(_, c)| c.clone()),
            );
            if other_gcd > BigInt::one() {
                let adj_const = if coeff.is_negative() {
                    -&constant
                } else {
                    constant.clone()
                };
                let residue = positive_mod(&adj_const, &other_gcd);
                modular_candidates.push((*var, other_gcd, residue));
            }
        }

        CachedLinear {
            other_gcd_gt1: !modular_candidates.is_empty(),
            has_unit_coeff_candidate,
            modular_candidates,
            gcd,
            gcd_divides,
            coeffs,
            constant,
        }
    }
}
