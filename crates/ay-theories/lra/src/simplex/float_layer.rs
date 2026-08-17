// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Float-pivot layer (`AY_LRA_FLOAT_LAYER`, default OFF) — increment 1.
//!
//! The f64 shadow simplex (`float_find_basis`) proposes a candidate basis `B*`.
//! This module CERTIFIES that basis exactly in `O(one basis solve)`, not
//! `O(pivots)`:
//!
//! 1. Reconstruct the immutable slack-definition system `A x = b` from
//!    `expr_to_slack` (the original small SMT coefficients; pivot-stable).
//! 2. Solve `A_{B*} x_{B*} = b - A_{N*} ν_{N*}` in ONE exact dense elimination
//!    (`basis_solve::solve_dense`), where non-basic values `ν` are their resting
//!    bounds (±ε for strict, handled via a twin eps-part solve). This is the
//!    lean win: cost is decoupled from the pivot count `P`.
//! 3. **Soundness anchor** — independently re-verify the produced assignment
//!    against EVERY current reduced tableau row equation and EVERY variable
//!    bound in exact `InfRational` arithmetic. Only if all hold do we emit Sat.
//!
//! Because step 3 re-derives the exact `all_bounds_satisfied` certificate that
//! the pure-exact simplex itself uses, the verdict is sound REGARDLESS of any
//! error in the f64 search, in the reconstructed `A`, or in `solve_dense`: a bad
//! candidate simply fails step 3 and the caller falls back to the untouched
//! exact simplex. 0-WRONG is structural, not statistical.

use ay_core::{FarkasAnnotation, TheoryConflict, TheoryLit, TheoryResult};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::float_simplex::{float_solve, FloatOutcome, NbPos};
use crate::rational::Rational;
use crate::types::{self, BoundType, InfRational};
use crate::LraSolver;

/// `AY_LRA_FLOAT_LAYER` gate — DEFAULT OFF (opt in with any non-empty, non-"0").
pub(crate) fn float_layer_enabled() -> bool {
    static V: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *V.get_or_init(|| std::env::var("AY_LRA_FLOAT_LAYER").is_ok_and(|v| v != "0" && !v.is_empty()))
}

/// Minimum tableau row count for the float layer to engage. Below this the f64
/// search + `O(m^3)` exact solve is pure overhead versus a handful of exact
/// pivots. (B9: compiled constant; the env override nothing set is retired.)
fn min_rows() -> usize {
    64
}

/// Diagnostic counters for the float layer (accept vs fallback), reported in
/// tests to characterise the accept rate. Process-global, best-effort.
pub(crate) mod stats {
    use std::sync::atomic::{AtomicU64, Ordering};
    pub(crate) static ATTEMPTS: AtomicU64 = AtomicU64::new(0);
    pub(crate) static CERTIFIED: AtomicU64 = AtomicU64::new(0);
    pub(crate) static FALLBACKS: AtomicU64 = AtomicU64::new(0);
    /// UNSAT-cert path (Increment 2): shadow reached an infeasible terminal.
    pub(crate) static UNSAT_ATTEMPTS: AtomicU64 = AtomicU64::new(0);
    pub(crate) static UNSAT_CERTIFIED: AtomicU64 = AtomicU64::new(0);
    pub(crate) static UNSAT_FALLBACKS: AtomicU64 = AtomicU64::new(0);

    #[inline]
    pub(crate) fn attempt() {
        ATTEMPTS.fetch_add(1, Ordering::Relaxed);
    }
    #[inline]
    pub(crate) fn certified() {
        CERTIFIED.fetch_add(1, Ordering::Relaxed);
    }
    #[inline]
    pub(crate) fn fallback() {
        FALLBACKS.fetch_add(1, Ordering::Relaxed);
    }
    #[inline]
    pub(crate) fn unsat_attempt() {
        UNSAT_ATTEMPTS.fetch_add(1, Ordering::Relaxed);
    }
    #[inline]
    pub(crate) fn unsat_certified() {
        UNSAT_CERTIFIED.fetch_add(1, Ordering::Relaxed);
    }
    #[inline]
    pub(crate) fn unsat_fallback() {
        UNSAT_FALLBACKS.fetch_add(1, Ordering::Relaxed);
    }
    #[cfg(test)]
    #[allow(dead_code)]
    pub(crate) fn snapshot() -> (u64, u64, u64) {
        (
            ATTEMPTS.load(Ordering::Relaxed),
            CERTIFIED.load(Ordering::Relaxed),
            FALLBACKS.load(Ordering::Relaxed),
        )
    }
    #[cfg(test)]
    pub(crate) fn unsat_snapshot() -> (u64, u64, u64) {
        (
            UNSAT_ATTEMPTS.load(Ordering::Relaxed),
            UNSAT_CERTIFIED.load(Ordering::Relaxed),
            UNSAT_FALLBACKS.load(Ordering::Relaxed),
        )
    }
}

impl LraSolver {
    /// Attempt an exactly-certified verdict (SAT **or** UNSAT) via the
    /// float-pivot layer.
    ///
    /// The f64 shadow search proposes a candidate basis `B*` and reports whether
    /// its terminal is feasible or a dual-infeasibility proof. Either terminal is
    /// then independently EXACT-certified:
    /// - Feasible → `Some(Sat)` only if the exact-solved assignment satisfies
    ///   every row equation and every bound (Increment 1).
    /// - Infeasible → `Some(UnsatWithFarkas)` only if the exact reduced conflict
    ///   row is a genuine tableau identity AND its nonbasic bound box forces
    ///   `bstar` past its bound (Increment 2).
    ///
    /// Returns `None` on any imprecision or non-genuine terminal, in which case
    /// the caller MUST run the unchanged exact simplex. The exact tableau
    /// (`rows`/status/`col_index`) is never mutated; SAT installs variable values
    /// on success, UNSAT mutates nothing.
    pub(crate) fn try_float_certified_sat(&mut self) -> Option<TheoryResult> {
        self.try_float_certified_with_min_rows(min_rows())
    }

    /// Testable implementation of the public float-layer attempt. Passing the
    /// row threshold explicitly keeps tests deterministic: they do not mutate a
    /// process-global environment variable racing with `min_rows()`'s OnceLock.
    fn try_float_certified_with_min_rows(&mut self, minimum_rows: usize) -> Option<TheoryResult> {
        let m = self.rows.len();
        if m < minimum_rows {
            return None;
        }
        // The reconstructed system must have exactly one equation per row; else
        // `expr_to_slack` is not a faithful mirror of the current tableau
        // (e.g. an optimization objective row was appended) → bail.
        if self.expr_to_slack.len() != m {
            return None;
        }

        stats::attempt();
        let iter_cap = (self.rows.len() + self.vars.len())
            .saturating_mul(40)
            .min(200_000);
        let outcome = match float_solve(&self.rows, &self.vars, iter_cap) {
            Some(o) => o,
            None => {
                stats::fallback();
                return None;
            }
        };
        match outcome {
            FloatOutcome::Feasible(candidate) => match self.certify_candidate_basis(&candidate) {
                Some(result) => {
                    stats::certified();
                    Some(result)
                }
                None => {
                    stats::fallback();
                    None
                }
            },
            FloatOutcome::Infeasible {
                basis,
                bstar,
                violated,
            } => {
                stats::unsat_attempt();
                match self.certify_infeasible_basis(&basis, bstar, violated) {
                    Some(result) => {
                        stats::unsat_certified();
                        Some(result)
                    }
                    None => {
                        stats::unsat_fallback();
                        None
                    }
                }
            }
        }
    }

    /// Build the exact certificate for `candidate` and, if it verifies, install
    /// it and return `Sat`. Returns `None` (no state change) otherwise.
    fn certify_candidate_basis(
        &mut self,
        candidate: &super::float_simplex::FloatBasis,
    ) -> Option<TheoryResult> {
        let n = self.vars.len();
        let m = self.rows.len();
        if candidate.basic.len() != m
            || candidate.is_basic.len() != n
            || candidate.nb_pos.len() != n
        {
            return None;
        }

        // Map each candidate basic var to its column index; reject duplicates or
        // out-of-range ids.
        let mut col_of = vec![usize::MAX; n];
        for (k, &bv) in candidate.basic.iter().enumerate() {
            let bi = bv as usize;
            if bi >= n || col_of[bi] != usize::MAX {
                return None;
            }
            col_of[bi] = k;
        }
        if candidate
            .is_basic
            .iter()
            .enumerate()
            .any(|(v, &flag)| flag != (col_of[v] != usize::MAX))
        {
            return None;
        }

        // --- ν: exact resting value of every non-basic variable. ---
        // Returns (x_part, y_part) as BigRational, or None if the recorded
        // resting position references an absent bound (inconsistent → bail).
        let nu = |v: usize| -> Option<InfRational> {
            if candidate.is_basic[v] {
                return None; // caller must not ask for basic vars
            }
            match candidate.nb_pos[v] {
                NbPos::Lower => Some(self.vars[v].lower.as_ref()?.as_inf(BoundType::Lower)),
                NbPos::Upper => Some(self.vars[v].upper.as_ref()?.as_inf(BoundType::Upper)),
                NbPos::Free => Some(InfRational::default()),
            }
        };

        // --- Assemble M (m x m over B*) and the two RHS vectors (x, y parts). ---
        let mut mat: Vec<Vec<BigRational>> = vec![vec![BigRational::zero(); m]; m];
        let mut rhs_x: Vec<BigRational> = vec![BigRational::zero(); m];
        let mut rhs_y: Vec<BigRational> = vec![BigRational::zero(); m];

        // Precompute ν for non-basic vars once (used both in RHS and assignment).
        let mut nu_cache: Vec<Option<InfRational>> = vec![None; n];
        for (v, slot) in nu_cache.iter_mut().enumerate() {
            if !candidate.is_basic[v] {
                *slot = Some(nu(v)?);
            }
        }

        // One equation per expr_to_slack entry: slack - Σ c·v = orig_constant,
        // i.e. (+1)·slack + Σ(-c)·v = orig_constant.
        for (e, (key, (slack, orig_constant))) in self.expr_to_slack.iter().enumerate() {
            rhs_x[e] = orig_constant.to_big();
            // rhs_y[e] starts at 0 (the constant has no infinitesimal part).

            // Contribution list: (var, coefficient).
            let contribute = |var: u32,
                              coeff: BigRational,
                              row: &mut [BigRational],
                              rx: &mut BigRational,
                              ry: &mut BigRational|
             -> Option<()> {
                let vi = var as usize;
                if vi >= n {
                    return None;
                }
                if candidate.is_basic[vi] {
                    let c = col_of[vi];
                    if c == usize::MAX {
                        return None;
                    }
                    row[c] = &row[c] + &coeff;
                } else {
                    let val = nu_cache[vi].as_ref()?;
                    *rx = &*rx - &(&coeff * &val.rational());
                    let ey = val.epsilon();
                    if !ey.is_zero() {
                        *ry = &*ry - &(&coeff * &ey);
                    }
                }
                Some(())
            };

            // Slack column: +1.
            contribute(
                *slack,
                BigRational::one(),
                &mut mat[e],
                &mut rhs_x[e],
                &mut rhs_y[e],
            )?;
            // Original expression variables: −c.
            for (v, c) in key {
                let neg = BigRational::from(BigInt::from(-1)) * c.to_big();
                contribute(*v, neg, &mut mat[e], &mut rhs_x[e], &mut rhs_y[e])?;
            }
        }

        // --- Solve the (up to two) exact systems. ---
        let sol_x = super::basis_solve::solve_dense(mat.clone(), rhs_x)?;
        let any_eps = rhs_y.iter().any(|r| !r.is_zero());
        let sol_y = if any_eps {
            super::basis_solve::solve_dense(mat, rhs_y)?
        } else {
            vec![BigRational::zero(); m]
        };

        // --- Build the full exact assignment. ---
        let mut assign: Vec<InfRational> = Vec::with_capacity(n);
        for v in 0..n {
            if candidate.is_basic[v] {
                let c = col_of[v];
                assign.push(InfRational::new(sol_x[c].clone(), sol_y[c].clone()));
            } else {
                // nu_cache[v] is Some for all non-basic v (filled above).
                assign.push(nu_cache[v].clone()?);
            }
        }

        // --- SOUNDNESS ANCHOR 1: every current reduced row equation holds. ---
        // basic_var == constant + Σ coeff·nonbasic (exact InfRational).
        for row in &self.rows {
            let bvar = row.basic_var as usize;
            if bvar >= n {
                return None;
            }
            let mut acc = InfRational::from_rat(row.constant.clone());
            for (v, c) in &row.coeffs {
                let vi = *v as usize;
                if vi >= n {
                    return None;
                }
                acc += &assign[vi].mul_rat(c);
            }
            if acc != assign[bvar] {
                return None;
            }
        }

        // --- SOUNDNESS ANCHOR 2: every bound is satisfied (exact). ---
        for (value, info) in assign.iter().zip(&self.vars) {
            if let Some(lower) = &info.lower {
                if value.lt_bound(&lower.value, lower.strict, BoundType::Lower) {
                    return None;
                }
            }
            if let Some(upper) = &info.upper {
                if value.gt_bound(&upper.value, upper.strict, BoundType::Upper) {
                    return None;
                }
            }
        }

        // --- Certified feasible. Install the assignment. ---
        // The tableau (rows/status/col_index) is intentionally left at the old
        // basis B0; only variable VALUES are updated. This is sound because the
        // assignment satisfies every B0 row equation (anchor 1), so the tableau
        // stays value-consistent; the only lapsed invariant is "B0 non-basics at
        // bounds", which the next check's non-basic repair round self-heals.
        for (v, value) in assign.into_iter().enumerate() {
            self.vars[v].value = value;
        }
        // Values changed out from under the incremental guards → invalidate.
        self.guard_clean_valid = false;
        self.heap_stale = true;
        // #warm-simplex: wholesale value install bypassed the delta log and
        // the dirty-set tracking — invalidate; the next full scan re-arms.
        self.warm_invalidate();
        self.vars_tightened_since_simplex.clear();
        // This exit verified EVERY bound and EVERY row equation — a full
        // verification, matching the exact simplex's `all_bounds_satisfied`
        // Sat contract (solve.rs:766-772).
        self.last_simplex_verified = true;
        self.guard_tracked_only = true;

        Some(TheoryResult::Sat)
    }

    /// Increment 2 — exactly-certified UNSAT from a shadow dual-infeasibility
    /// proof. `basis` is the candidate `B*`; `bstar` is a basic variable that
    /// violates its `violated` bound with no entering pivot in the shadow.
    ///
    /// Steps (all exact; any failure → `None` → untouched exact fallback):
    /// 1. Reassemble `A_{B*}` from `expr_to_slack` (as the SAT path does).
    /// 2. Solve `A_{B*}^T y = e_k` (k = column of `bstar`) for exact rational
    ///    Farkas multipliers `y`.
    /// 3. Form the exact reduced conflict row over the `B*` non-basics:
    ///    `x_{bstar} = C + Σ_v coeff_v · x_v`, `coeff_v = -(y^T A)_v`, `C = y^T b`.
    /// 4. **Soundness anchor** — verify this row is a genuine identity of the
    ///    CURRENT exact tableau (`self.rows`) by reducing
    ///    `x_{bstar} - C - Σ coeff_v x_v` through the tableau to the zero form.
    ///    This trusts only `self.rows`, so a mis-reconstructed `A` or a bad `y`
    ///    is caught here, never certified.
    /// 5. **Genuine-conflict check** — push every non-basic to the bound extreme
    ///    that best relieves `bstar`'s violation; if `bstar` is STILL forced past
    ///    its bound (exact `InfRational`), the bound box is a real conflict.
    /// 6. Emit the exact Farkas conflict via `build_conflict_from_row`.
    ///
    /// Mutates NO solver state on any path (values, rows, status untouched).
    fn certify_infeasible_basis(
        &mut self,
        basis: &super::float_simplex::FloatBasis,
        bstar: u32,
        violated: BoundType,
    ) -> Option<TheoryResult> {
        let n = self.vars.len();
        let m = self.rows.len();
        if basis.basic.len() != m
            || basis.is_basic.len() != n
            || basis.nb_pos.len() != n
            || self.expr_to_slack.len() != m
        {
            return None;
        }
        if (bstar as usize) >= n || !basis.is_basic[bstar as usize] {
            return None;
        }

        // Column index of each basic var; reject duplicates / out-of-range.
        let mut col_of = vec![usize::MAX; n];
        for (k, &bv) in basis.basic.iter().enumerate() {
            let bi = bv as usize;
            if bi >= n || col_of[bi] != usize::MAX {
                return None;
            }
            col_of[bi] = k;
        }
        if basis
            .is_basic
            .iter()
            .enumerate()
            .any(|(v, &flag)| flag != (col_of[v] != usize::MAX))
        {
            return None;
        }
        let k = col_of[bstar as usize];
        if k == usize::MAX {
            return None;
        }

        // --- (1) Reassemble A_{B*} (m x m over the basic columns). ---
        // Equation e: (+1)·slack + Σ(-c)·v = orig_constant.
        let mut mat: Vec<Vec<BigRational>> = vec![vec![BigRational::zero(); m]; m];
        for (e, (key, (slack, _orig_constant))) in self.expr_to_slack.iter().enumerate() {
            let si = *slack as usize;
            if si >= n {
                return None;
            }
            if basis.is_basic[si] {
                let c = col_of[si];
                if c == usize::MAX {
                    return None;
                }
                mat[e][c] = &mat[e][c] + &BigRational::one();
            }
            for (v, cc) in key {
                let vi = *v as usize;
                if vi >= n {
                    return None;
                }
                if basis.is_basic[vi] {
                    let c = col_of[vi];
                    if c == usize::MAX {
                        return None;
                    }
                    mat[e][c] = &mat[e][c] - &cc.to_big();
                }
            }
        }

        // --- (2) Solve A_{B*}^T y = e_k. ---
        let mut mat_t: Vec<Vec<BigRational>> = vec![vec![BigRational::zero(); m]; m];
        for (i, row) in mat.iter().enumerate() {
            for (j, entry) in row.iter().enumerate() {
                mat_t[j][i] = entry.clone();
            }
        }
        let mut ek = vec![BigRational::zero(); m];
        ek[k] = BigRational::one();
        let y = super::basis_solve::solve_dense(mat_t, ek)?;

        // --- (3) agg[v] = (y^T A)_v over ALL vars; C = y^T b. ---
        let mut agg: Vec<BigRational> = vec![BigRational::zero(); n];
        let mut c_const = BigRational::zero();
        for (e, (key, (slack, orig_constant))) in self.expr_to_slack.iter().enumerate() {
            let ye = &y[e];
            if ye.is_zero() {
                continue;
            }
            let si = *slack as usize;
            agg[si] = &agg[si] + ye; // A[e][slack] = +1
            for (v, cc) in key {
                let vi = *v as usize;
                agg[vi] = &agg[vi] - &(&cc.to_big() * ye); // A[e][v] = -c
            }
            c_const = &c_const + &(ye * &orig_constant.to_big());
        }

        // Solve sanity: (y^T A) restricted to basic columns must equal e_k, i.e.
        // agg[bstar] == 1 and every other basic var's agg == 0. A failure means
        // `mat` did not faithfully represent A_{B*}; bail (the tableau identity
        // anchor below would reject it anyway, this is just an early-out).
        if agg[bstar as usize] != BigRational::one() {
            return None;
        }
        for (v, coeff) in agg.iter().enumerate() {
            if basis.is_basic[v] && v != bstar as usize && !coeff.is_zero() {
                return None;
            }
        }

        // Reduced conflict row over the non-basics: coeff_v = -agg[v].
        let mut row_coeffs: Vec<(u32, Rational)> = Vec::new();
        for (v, coeff) in agg.iter().enumerate() {
            if basis.is_basic[v] || coeff.is_zero() {
                continue;
            }
            row_coeffs.push((v as u32, Rational::from(-coeff.clone())));
        }
        let c_const_rat = Rational::from(c_const);

        // --- (4) SOUNDNESS ANCHOR: reduced row is a genuine tableau identity. ---
        if !self.reduced_row_is_valid_identity(bstar, &row_coeffs, &c_const_rat) {
            return None;
        }

        // --- (5) Genuine-conflict check via the exact bound box. ---
        let binfo = &self.vars[bstar as usize];
        let (bound_value, bound_strict) = match violated {
            BoundType::Lower => {
                let b = binfo.lower.as_ref()?;
                (b.value.clone(), b.strict)
            }
            BoundType::Upper => {
                let b = binfo.upper.as_ref()?;
                (b.value.clone(), b.strict)
            }
        };
        // Push each non-basic to the bound that most relieves the violation.
        // Lower violation (bstar too small → maximize RHS):
        //   coeff>0 → nonbasic at upper; coeff<0 → nonbasic at lower.
        // Upper violation (bstar too large → minimize RHS): the mirror image.
        // A missing required bound ⇒ bstar is unbounded in that direction ⇒
        // NOT a genuine conflict ⇒ None.
        let mut extreme = InfRational::from_rat(c_const_rat.clone());
        for (v, coeff) in &row_coeffs {
            let info = &self.vars[*v as usize];
            let use_upper = match violated {
                BoundType::Lower => coeff.is_positive(),
                BoundType::Upper => !coeff.is_positive(),
            };
            let (bnd, bt) = if use_upper {
                (info.upper.as_ref()?, BoundType::Upper)
            } else {
                (info.lower.as_ref()?, BoundType::Lower)
            };
            extreme += &bnd.as_inf(bt).mul_rat(coeff);
        }
        let genuine = match violated {
            BoundType::Lower => extreme.lt_bound(&bound_value, bound_strict, BoundType::Lower),
            BoundType::Upper => extreme.gt_bound(&bound_value, bound_strict, BoundType::Upper),
        };
        if !genuine {
            return None;
        }

        // --- (6) Build the exact Farkas conflict. ---
        let conflict = self.build_conflict_from_row(bstar, &row_coeffs, violated);
        if conflict.literals.is_empty() {
            // Incomplete explanation (reasonless/sentinel/stale) — fall back to
            // the exact simplex, which owns the degradation policy.
            return None;
        }
        Some(TheoryResult::UnsatWithFarkas(conflict))
    }

    /// SOUNDNESS ANCHOR for the UNSAT path. Verify that the reduced conflict row
    /// `x_{bstar} = constant + Σ coeff_v · x_v` is a genuine linear consequence
    /// of the CURRENT exact tableau `self.rows` (the source of truth), by
    /// reducing the linear form `x_{bstar} - constant - Σ coeff_v x_v` through
    /// every tableau row (each `basic = const + Σ nonbasic`) and checking it
    /// collapses to the identically-zero form.
    ///
    /// Because the tableau equations hold unconditionally in every model, a row
    /// that passes this check is an unconditional identity — so a conflict built
    /// from it is sound regardless of how `A`/`y` were computed.
    fn reduced_row_is_valid_identity(
        &self,
        bstar: u32,
        coeffs: &[(u32, Rational)],
        constant: &Rational,
    ) -> bool {
        use ay_core::kani_compat::DetHashMap as HashMap;

        // basic_var → row index (current B0 basis).
        let mut basic_row: HashMap<u32, usize> = HashMap::default();
        for (ri, row) in self.rows.iter().enumerate() {
            if basic_row.insert(row.basic_var, ri).is_some() {
                // Two rows share a basic var → tableau is malformed; reject.
                return false;
            }
        }

        // Linear form accumulator: var → coefficient, plus a scalar constant.
        let mut acc: HashMap<u32, Rational> = HashMap::default();
        let add_var = |acc: &mut HashMap<u32, Rational>, v: u32, c: Rational| {
            let e = acc.entry(v).or_insert_with(Rational::zero);
            *e = &*e + &c;
        };
        // P = x_bstar - constant - Σ coeff_v x_v
        add_var(&mut acc, bstar, Rational::one());
        for (v, c) in coeffs {
            add_var(&mut acc, *v, -c.clone());
        }
        let mut acc_const = -constant.clone();

        // Substitute each basic var by its row until only non-basics remain.
        // Rows are in reduced form (RHS references only non-basics), so each
        // basic var is substituted at most once; cap passes as a safety net.
        for _ in 0..(self.rows.len() + 2) {
            let target = acc
                .iter()
                .find(|(v, c)| !c.is_zero() && basic_row.contains_key(*v))
                .map(|(v, _)| *v);
            let Some(bv) = target else { break };
            let c = acc.remove(&bv).unwrap_or_else(Rational::zero);
            let row = &self.rows[basic_row[&bv]];
            acc_const = &acc_const + &(&row.constant * &c);
            for (nv, nc) in &row.coeffs {
                add_var(&mut acc, *nv, &c * nc);
            }
        }

        // Any surviving basic var means we failed to converge → reject.
        // Every remaining coefficient must be zero and the constant must vanish.
        for (v, c) in &acc {
            if !c.is_zero() {
                if basic_row.contains_key(v) {
                    return false;
                }
                return false;
            }
        }
        acc_const.is_zero()
    }

    /// Build a Farkas conflict from an EXPLICIT reduced row + a KNOWN violated
    /// bound, without consulting `self.rows` or `self.vars[bstar].value`.
    ///
    /// Used only by the float-pivot UNSAT path (`AY_LRA_FLOAT_LAYER`). Every
    /// variable in `coeffs` is non-basic in the candidate basis `B*` by
    /// construction, so — unlike `build_conflict_with_farkas`, which filters on
    /// the B0 `VarStatus` — no status filtering is applied. The genuineness of
    /// the conflict is established by the caller BEFORE this runs.
    ///
    /// The clause negates `bstar`'s violated-bound atom plus each non-basic's
    /// active-bound atom, with matching Farkas coefficients (`1` for `bstar`,
    /// `|coeff_v|·scale` for each non-basic). Returns an **empty** conflict when
    /// any participating bound is reasonless or sentinel-only (the caller then
    /// falls back to the exact simplex), and applies the same live-reason guard
    /// as `build_conflict_with_farkas`.
    fn build_conflict_from_row(
        &mut self,
        bstar: u32,
        coeffs: &[(u32, Rational)],
        violated: BoundType,
    ) -> TheoryConflict {
        use num_rational::Rational64;

        let mut literals: Vec<TheoryLit> = Vec::new();
        let mut coefficients: Option<Vec<Rational64>> = Some(Vec::new());
        let mut incomplete = false;

        // Collect the non-sentinel reasons of a bound with a per-reason Farkas
        // coefficient `base · scale`. Sets `incomplete` if the bound contributes
        // no real reason.
        let push_bound = |literals: &mut Vec<TheoryLit>,
                          coefficients: &mut Option<Vec<Rational64>>,
                          incomplete: &mut bool,
                          bound: &crate::Bound,
                          base: &Rational| {
            let mut pushed = false;
            for ((reason, reason_value), scale) in
                bound.reasons.iter().zip(&bound.reason_values).zip(
                    bound
                        .reason_scales
                        .iter()
                        .chain(std::iter::repeat(types::rational_one())),
                )
            {
                if reason.is_sentinel() {
                    continue;
                }
                pushed = true;
                literals.push(TheoryLit::new(*reason, *reason_value));
                if let Some(cs) = coefficients.as_mut() {
                    let scaled = base * scale;
                    match LraSolver::rational_to_rational64(&scaled) {
                        Some(c) => cs.push(c),
                        None => *coefficients = None,
                    }
                }
            }
            if !pushed {
                *incomplete = true;
            }
        };

        // bstar's violated bound gets coefficient 1.
        let one = Rational::one();
        {
            let binfo = &self.vars[bstar as usize];
            let basic_bound = match violated {
                BoundType::Lower => binfo.lower.as_ref(),
                BoundType::Upper => binfo.upper.as_ref(),
            };
            match basic_bound {
                Some(b) => push_bound(&mut literals, &mut coefficients, &mut incomplete, b, &one),
                None => incomplete = true,
            }
        }

        // Each non-basic's active bound gets coefficient |coeff_v|.
        for (v, coeff) in coeffs {
            if coeff.is_zero() {
                continue;
            }
            let info = &self.vars[*v as usize];
            let active_bound = match violated {
                BoundType::Lower => {
                    if coeff.is_positive() {
                        info.upper.as_ref()
                    } else {
                        info.lower.as_ref()
                    }
                }
                BoundType::Upper => {
                    if coeff.is_positive() {
                        info.lower.as_ref()
                    } else {
                        info.upper.as_ref()
                    }
                }
            };
            match active_bound {
                Some(b) => {
                    let abs_coeff = coeff.abs();
                    push_bound(
                        &mut literals,
                        &mut coefficients,
                        &mut incomplete,
                        b,
                        &abs_coeff,
                    );
                }
                None => incomplete = true,
            }
        }

        if incomplete || literals.is_empty() {
            return TheoryConflict::new(vec![]);
        }

        let farkas = coefficients
            .filter(|c| !c.is_empty())
            .map(FarkasAnnotation::new);
        let (dedup_literals, dedup_coeffs) =
            LraSolver::deduplicate_conflict(literals, farkas.as_ref());
        if dedup_literals.is_empty() {
            return TheoryConflict::new(vec![]);
        }
        let dedup_farkas = if !dedup_coeffs.is_empty() {
            Some(FarkasAnnotation::new(dedup_coeffs))
        } else {
            farkas
        };
        if !self.conflict_literals_all_asserted(&dedup_literals) {
            self.stats.stale_conflict_rejected_count += 1;
            return TheoryConflict::new(vec![]);
        }
        match dedup_farkas {
            Some(f) => TheoryConflict::with_farkas(dedup_literals, f),
            None => TheoryConflict::new(dedup_literals),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::float_simplex::{
        float_find_basis, float_solve, FloatBasis, FloatOutcome, NbPos,
    };
    use super::*;
    use crate::linear_expr::LinearExpr;
    use crate::rational::Rational;
    use crate::{Bound, VarInfo, VarStatus};
    use ay_core::term::{TermId, TermStore};

    fn rat(n: i64) -> Rational {
        Rational::from(n)
    }
    fn bnd(v: i64, strict: bool) -> Bound {
        Bound::without_reasons(rat(v), strict)
    }
    fn nb(lo: Option<i64>, hi: Option<i64>) -> VarInfo {
        VarInfo {
            value: InfRational::default(),
            lower: lo.map(|v| bnd(v, false)),
            upper: hi.map(|v| bnd(v, false)),
            status: Some(VarStatus::NonBasic),
        }
    }

    /// x0,x1 in [0,10]; slack s2 = x0 + x1 fixed at `s_fixed`.
    fn setup(s_fixed: i64) -> (LraSolver, u32) {
        let terms = TermStore::new();
        let mut s = LraSolver::new(&terms);
        s.vars.push(nb(Some(0), Some(10)));
        s.vars.push(nb(Some(0), Some(10)));
        s.next_var = 2;
        let expr = LinearExpr {
            coeffs: vec![(0, rat(1)), (1, rat(1))],
            constant: rat(0),
        };
        let (slack, _) = s.get_or_create_slack(&expr);
        s.vars[slack as usize].lower = Some(bnd(s_fixed, false));
        s.vars[slack as usize].upper = Some(bnd(s_fixed, false));
        (s, slack)
    }

    #[test]
    fn test_certifies_feasible() {
        let (mut s, slack) = setup(5);
        let basis = float_find_basis(&s.rows, &s.vars, 10_000).expect("shadow basis");
        let res = s.certify_candidate_basis(&basis);
        assert!(
            matches!(res, Some(TheoryResult::Sat)),
            "expected certified Sat"
        );
        // Installed values must satisfy x0 + x1 == 5 and s2 == 5.
        let v0 = s.vars[0].value.x_approx_f64();
        let v1 = s.vars[1].value.x_approx_f64();
        let vs = s.vars[slack as usize].value.x_approx_f64();
        assert!((v0 + v1 - 5.0).abs() < 1e-9, "x0+x1={}", v0 + v1);
        assert!((vs - 5.0).abs() < 1e-9, "s2={vs}");
        assert!(s.last_simplex_verified);
    }

    #[test]
    fn test_shadow_infeasible_returns_none() {
        // s2 fixed at 25 but x0+x1 <= 20: infeasible → shadow finds no basis.
        let (s, _) = setup(25);
        assert!(float_find_basis(&s.rows, &s.vars, 10_000).is_none());
    }

    #[test]
    fn test_soundness_anchor_rejects_bad_basis() {
        // Feasible problem, but hand a basis {s2 basic, x0/x1 at lower} whose
        // exact solve gives s2 = 0, violating s2's [5,5] bound. The soundness
        // anchor must reject it (None) and NOT mutate solver state.
        let (mut s, slack) = setup(5);
        let n = s.vars.len();
        let mut is_basic = vec![false; n];
        is_basic[slack as usize] = true;
        let mut nb_pos = vec![NbPos::Free; n];
        nb_pos[0] = NbPos::Lower;
        nb_pos[1] = NbPos::Lower;
        let bad = FloatBasis {
            basic: vec![slack],
            is_basic,
            nb_pos,
        };
        let before = s.vars[0].value.x_approx_f64();
        assert!(s.certify_candidate_basis(&bad).is_none());
        // No mutation on the reject path.
        assert_eq!(s.vars[0].value.x_approx_f64(), before);
        assert!(!s.last_simplex_verified);
    }

    #[test]
    fn test_malformed_candidate_vector_lengths_fail_closed() {
        let (mut s, slack) = setup(5);
        let malformed = FloatBasis {
            basic: vec![slack],
            is_basic: Vec::new(),
            nb_pos: Vec::new(),
        };
        assert!(s.certify_candidate_basis(&malformed).is_none());
        assert!(!s.last_simplex_verified);
    }

    #[test]
    fn test_min_rows_gate_blocks_small_problems() {
        // try_float_certified_sat must decline problems with fewer rows than
        // the configured threshold. (Skipped when the env override lowers the
        // threshold to <= 1, which the stress-test configuration does.)
        if min_rows() > 1 {
            let (mut s, _) = setup(5);
            assert!(s.try_float_certified_sat().is_none());
        }
    }

    #[test]
    fn test_pending_trivial_conflict_preempts_float_certified_sat() {
        // This is the adversarial regression for the wrapper ordering in
        // `dual_simplex`: with the float path forced on for one-row systems,
        // the feasible row below is certifiable, but a pending constant
        // conflict must still win and be consumed as UNSAT.
        if !float_layer_enabled() || min_rows() > 1 {
            return;
        }
        let (mut s, _) = setup(5);
        s.trivial_conflict = Some(Vec::new());
        assert!(matches!(s.dual_simplex(), TheoryResult::Unsat(lits) if lits.is_empty()));
        assert!(
            s.trivial_conflict.is_none(),
            "the exact pre-loop path must consume the pending conflict"
        );
    }

    /// Independently re-verify an installed assignment satisfies every row
    /// equation and bound (mirrors the anchors; catches an install/verify skew).
    fn assignment_is_feasible(s: &LraSolver) -> bool {
        let n = s.vars.len();
        for row in &s.rows {
            let mut acc = InfRational::from_rat(row.constant.clone());
            for (v, c) in &row.coeffs {
                acc += &s.vars[*v as usize].value.mul_rat(c);
            }
            if acc != s.vars[row.basic_var as usize].value {
                return false;
            }
        }
        for v in 0..n {
            let info = &s.vars[v];
            if let Some(l) = &info.lower {
                if info.value.lt_bound(&l.value, l.strict, BoundType::Lower) {
                    return false;
                }
            }
            if let Some(u) = &info.upper {
                if info.value.gt_bound(&u.value, u.strict, BoundType::Upper) {
                    return false;
                }
            }
        }
        true
    }

    /// Randomized accept-rate + soundness sweep. Generates guaranteed-feasible
    /// multi-slack systems, runs the shadow search + exact certification, and
    /// asserts every certified Sat is genuinely feasible (0-wrong). Reports the
    /// accept rate (visible under `--nocapture`).
    #[test]
    fn test_random_accept_rate_and_soundness() {
        let mut state: u64 = 0x00C0_FFEE_1234_5678;
        let mut rng = || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (state >> 33) as i64
        };

        let (mut attempts, mut certified) = (0u64, 0u64);
        for _ in 0..300 {
            let terms = TermStore::new();
            let mut s = LraSolver::new(&terms);
            let nstruct = 3 + (rng().unsigned_abs() as usize % 4); // 3..=6
                                                                   // Structural vars with wide bounds and a chosen feasible point.
            let mut point = Vec::with_capacity(nstruct);
            for _ in 0..nstruct {
                s.vars.push(nb(Some(-100), Some(100)));
                point.push(rng() % 11 - 5); // in [-5, 5]
            }
            s.next_var = nstruct as u32;

            let nslack = 2 + (rng().unsigned_abs() as usize % 3); // 2..=4
            for _ in 0..nslack {
                let mut coeffs = Vec::new();
                let mut sum = 0i64;
                for (v, &pv) in point.iter().enumerate() {
                    if rng() % 2 == 0 {
                        let c = if rng() % 2 == 0 { 1 } else { -1 };
                        coeffs.push((v as u32, rat(c)));
                        sum += c * pv;
                    }
                }
                if coeffs.is_empty() {
                    coeffs.push((0, rat(1)));
                    sum = point[0];
                }
                let expr = LinearExpr {
                    coeffs,
                    constant: rat(0),
                };
                let (slack, _) = s.get_or_create_slack(&expr);
                // Fix the slack at the feasible point's value → problem is SAT.
                s.vars[slack as usize].lower = Some(bnd(sum, false));
                s.vars[slack as usize].upper = Some(bnd(sum, false));
            }

            attempts += 1;
            if let Some(basis) = float_find_basis(&s.rows, &s.vars, 50_000) {
                if let Some(TheoryResult::Sat) = s.certify_candidate_basis(&basis) {
                    certified += 1;
                    assert!(
                        assignment_is_feasible(&s),
                        "certified Sat must be genuinely feasible"
                    );
                }
            }
        }
        eprintln!(
            "[float-layer] random feasible sweep: {certified}/{attempts} certified ({:.0}%)",
            100.0 * certified as f64 / attempts as f64
        );
        assert!(
            certified > 0,
            "expected some certifications on feasible corpus"
        );
    }

    /// A variable bound carrying exactly one asserted reason atom (scale 1).
    fn bnd_r(v: i64, strict: bool, reason: u32, value: bool) -> Bound {
        Bound::new(
            rat(v),
            vec![TermId::new(reason)],
            vec![value],
            vec![],
            strict,
        )
    }

    /// Build the canonical infeasible instance: x0,x1 ∈ [0,10] (upper bounds
    /// carry reasons), s2 = x0 + x1 fixed at 25. Max x0+x1 = 20 < 25 ⇒ UNSAT.
    /// Returns the solver and the slack id. All cited reasons are asserted.
    fn setup_unsat() -> (LraSolver, u32) {
        let terms = TermStore::new();
        let mut s = LraSolver::new(&terms);
        let mkvar = |lo_r: u32, up_r: u32| VarInfo {
            value: InfRational::default(),
            lower: Some(bnd_r(0, false, lo_r, true)),
            upper: Some(bnd_r(10, false, up_r, false)),
            status: Some(VarStatus::NonBasic),
        };
        s.vars.push(mkvar(200, 100));
        s.vars.push(mkvar(201, 101));
        s.next_var = 2;
        let expr = LinearExpr {
            coeffs: vec![(0, rat(1)), (1, rat(1))],
            constant: rat(0),
        };
        let (slack, _) = s.get_or_create_slack(&expr);
        s.vars[slack as usize].lower = Some(bnd_r(25, false, 102, true));
        s.vars[slack as usize].upper = Some(bnd_r(25, false, 103, true));
        // Assert every reason with the polarity the bound records, so the
        // live-reason guard in build_conflict_from_row accepts the conflict.
        for (r, v) in [
            (100u32, false),
            (101, false),
            (102, true),
            (103, true),
            (200, true),
            (201, true),
        ] {
            s.asserted.insert(TermId::new(r), v);
        }
        (s, slack)
    }

    #[test]
    fn test_certifies_infeasible_unsat() {
        let (mut s, slack) = setup_unsat();
        let outcome = float_solve(&s.rows, &s.vars, 10_000).expect("shadow outcome");
        let FloatOutcome::Infeasible {
            basis,
            bstar,
            violated,
        } = outcome
        else {
            panic!("expected an Infeasible shadow terminal");
        };
        let _ = slack;
        match s.certify_infeasible_basis(&basis, bstar, violated) {
            Some(TheoryResult::UnsatWithFarkas(conflict)) => {
                assert!(
                    !conflict.literals.is_empty(),
                    "certified UNSAT must cite real reason literals"
                );
                // Whatever basis the shadow lands on, the structural equality
                // s2 = x0 + x1 makes the minimal conflict cite s2.lower (102)
                // and both structural uppers (100, 101).
                let terms: Vec<u32> = conflict.literals.iter().map(|l| l.term.0).collect();
                assert!(
                    terms.contains(&102),
                    "must cite s2.lower reason, got {terms:?}"
                );
                assert!(
                    terms.contains(&100) && terms.contains(&101),
                    "must cite x0/x1 uppers, got {terms:?}"
                );
                // Soundness: every cited literal is a currently-asserted atom.
                for l in &conflict.literals {
                    assert_eq!(s.asserted.get(&l.term), Some(&l.value));
                }
            }
            other => panic!("expected UnsatWithFarkas, got {other:?}"),
        }
    }

    #[test]
    fn test_infeasible_cert_malformed_basis_fails_closed() {
        let (mut s, slack) = setup_unsat();
        let n = s.vars.len();

        let wrong_lengths = FloatBasis {
            basic: vec![slack],
            is_basic: Vec::new(),
            nb_pos: Vec::new(),
        };
        assert!(s
            .certify_infeasible_basis(&wrong_lengths, slack, BoundType::Lower)
            .is_none());

        let inconsistent_flags = FloatBasis {
            basic: vec![slack],
            is_basic: vec![false; n],
            nb_pos: vec![NbPos::Free; n],
        };
        assert!(s
            .certify_infeasible_basis(&inconsistent_flags, slack, BoundType::Lower)
            .is_none());
    }

    #[test]
    fn test_infeasible_cert_rejects_reasonless_and_stale_explanations() {
        let (mut reasonless, _) = setup_unsat();
        let FloatOutcome::Infeasible {
            basis,
            bstar,
            violated,
        } = float_solve(&reasonless.rows, &reasonless.vars, 10_000).expect("shadow terminal")
        else {
            panic!("expected infeasible terminal");
        };
        reasonless.vars[0].upper = Some(bnd(10, false));
        assert!(reasonless
            .certify_infeasible_basis(&basis, bstar, violated)
            .is_none());

        let (mut stale, _) = setup_unsat();
        let FloatOutcome::Infeasible {
            basis,
            bstar,
            violated,
        } = float_solve(&stale.rows, &stale.vars, 10_000).expect("shadow terminal")
        else {
            panic!("expected infeasible terminal");
        };
        stale.asserted.remove(&TermId::new(100));
        let rejected_before = stale.stats.stale_conflict_rejected_count;
        assert!(stale
            .certify_infeasible_basis(&basis, bstar, violated)
            .is_none());
        assert!(stale.stats.stale_conflict_rejected_count > rejected_before);
    }

    #[test]
    fn test_infeasible_cert_upper_strict_negative_coefficient() {
        // s = -x, x <= 10, and s < -10 is impossible. This exercises an upper
        // violation, a negative reduced-row coefficient, and epsilon-strictness.
        let terms = TermStore::new();
        let mut s = LraSolver::new(&terms);
        s.vars.push(VarInfo {
            value: InfRational::default(),
            lower: Some(bnd_r(0, false, 410, true)),
            upper: Some(bnd_r(10, false, 411, true)),
            status: Some(VarStatus::NonBasic),
        });
        s.next_var = 1;
        let expr = LinearExpr {
            coeffs: vec![(0, rat(-1))],
            constant: rat(0),
        };
        let (slack, _) = s.get_or_create_slack(&expr);
        s.vars[slack as usize].lower = Some(bnd_r(-20, false, 412, true));
        s.vars[slack as usize].upper = Some(bnd_r(-10, true, 413, true));
        for reason in 410..=413 {
            s.asserted.insert(TermId::new(reason), true);
        }
        let n = s.vars.len();
        let mut is_basic = vec![false; n];
        is_basic[slack as usize] = true;
        let mut nb_pos = vec![NbPos::Free; n];
        nb_pos[0] = NbPos::Upper;
        let basis = FloatBasis {
            basic: vec![slack],
            is_basic,
            nb_pos,
        };
        let result = s.certify_infeasible_basis(&basis, slack, BoundType::Upper);
        assert!(matches!(result, Some(TheoryResult::UnsatWithFarkas(_))));
    }

    #[test]
    fn test_infeasible_cert_multirow_pivoted_basis() {
        // Two independent rows, with candidate basic columns deliberately
        // ordered [t, x]. The exact A_B solve must row-pivot at column zero.
        // Row one forces x = sx = 11 while x <= 10, so the result is UNSAT.
        let terms = TermStore::new();
        let mut s = LraSolver::new(&terms);
        for (lo, hi, lr, ur) in [(0, 10, 500, 501), (0, 10, 502, 503)] {
            s.vars.push(VarInfo {
                value: InfRational::default(),
                lower: Some(bnd_r(lo, false, lr, true)),
                upper: Some(bnd_r(hi, false, ur, true)),
                status: Some(VarStatus::NonBasic),
            });
        }
        s.next_var = 2;
        let (sx, _) = s.get_or_create_slack(&LinearExpr {
            coeffs: vec![(0, rat(1))],
            constant: rat(0),
        });
        let (t, _) = s.get_or_create_slack(&LinearExpr {
            coeffs: vec![(1, rat(1))],
            constant: rat(0),
        });
        s.vars[sx as usize].lower = Some(bnd_r(11, false, 504, true));
        s.vars[sx as usize].upper = Some(bnd_r(11, false, 505, true));
        s.vars[t as usize].lower = Some(bnd_r(5, false, 506, true));
        s.vars[t as usize].upper = Some(bnd_r(5, false, 507, true));
        for reason in 500..=507 {
            s.asserted.insert(TermId::new(reason), true);
        }

        let n = s.vars.len();
        let mut is_basic = vec![false; n];
        is_basic[t as usize] = true;
        is_basic[0] = true;
        let basis = FloatBasis {
            basic: vec![t, 0],
            is_basic,
            nb_pos: vec![NbPos::Free; n],
        };
        let result = s.certify_infeasible_basis(&basis, 0, BoundType::Upper);
        assert!(matches!(result, Some(TheoryResult::UnsatWithFarkas(_))));
    }

    #[test]
    fn test_infeasible_cert_rejects_non_conflict_basis() {
        // Feasible instance (s2 fixed at 5, reachable), but hand the UNSAT
        // certifier a bogus witness claiming s2 violates its lower bound. The
        // exact genuine-conflict check must reject it (None) — the bound box
        // easily reaches 5 — and mutate no state.
        let (mut s, slack) = setup(5);
        let n = s.vars.len();
        let mut is_basic = vec![false; n];
        is_basic[slack as usize] = true;
        let mut nb_pos = vec![NbPos::Free; n];
        nb_pos[0] = NbPos::Lower;
        nb_pos[1] = NbPos::Lower;
        let bogus = FloatBasis {
            basic: vec![slack],
            is_basic,
            nb_pos,
        };
        let before = s.vars[0].value.x_approx_f64();
        assert!(s
            .certify_infeasible_basis(&bogus, slack, BoundType::Lower)
            .is_none());
        assert_eq!(s.vars[0].value.x_approx_f64(), before);
        assert!(!s.last_simplex_verified);
    }

    /// Randomized UNSAT accept-rate + soundness sweep. Generates guaranteed-
    /// infeasible single-slack instances (`s = Σ x_i` fixed strictly above the
    /// reachable maximum), runs the shadow search + exact UNSAT certification,
    /// and asserts every certified conflict is sound: non-empty, all cited
    /// literals asserted. Reports the accept rate (visible under `--nocapture`).
    #[test]
    fn test_random_unsat_accept_rate_and_soundness() {
        let mut state: u64 = 0xDEAD_BEEF_0BAD_F00D;
        let mut rng = || {
            state = state
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (state >> 33) as i64
        };

        let (mut attempts, mut certified) = (0u64, 0u64);
        for _ in 0..300 {
            let terms = TermStore::new();
            let mut s = LraSolver::new(&terms);
            let nstruct = 2 + (rng().unsigned_abs() as usize % 4); // 2..=5
            let mut reachable_max = 0i64;
            let mut rid = 300u32;
            for _ in 0..nstruct {
                let hi = 1 + (rng().unsigned_abs() as i64 % 9); // 1..=9
                reachable_max += hi;
                s.vars.push(VarInfo {
                    value: InfRational::default(),
                    lower: Some(bnd_r(0, false, rid, true)),
                    upper: Some(bnd_r(hi, false, rid + 1, false)),
                    status: Some(VarStatus::NonBasic),
                });
                rid += 2;
            }
            s.next_var = nstruct as u32;
            let coeffs: Vec<(u32, Rational)> = (0..nstruct as u32).map(|v| (v, rat(1))).collect();
            let expr = LinearExpr {
                coeffs,
                constant: rat(0),
            };
            let (slack, _) = s.get_or_create_slack(&expr);
            // Fix the slack strictly above the reachable maximum → UNSAT.
            let target = reachable_max + 1 + (rng().unsigned_abs() as i64 % 5);
            s.vars[slack as usize].lower = Some(bnd_r(target, false, rid, true));
            s.vars[slack as usize].upper = Some(bnd_r(target, false, rid + 1, true));
            // Assert every reason at the polarity its bound records.
            for v in &s.vars {
                for b in [v.lower.as_ref(), v.upper.as_ref()].into_iter().flatten() {
                    for (t, val) in b.reasons.iter().zip(&b.reason_values) {
                        s.asserted.insert(*t, *val);
                    }
                }
            }

            attempts += 1;
            if let Some(FloatOutcome::Infeasible {
                basis,
                bstar,
                violated,
            }) = float_solve(&s.rows, &s.vars, 50_000)
            {
                if let Some(TheoryResult::UnsatWithFarkas(c)) =
                    s.certify_infeasible_basis(&basis, bstar, violated)
                {
                    certified += 1;
                    assert!(!c.literals.is_empty(), "certified UNSAT must be non-empty");
                    for l in &c.literals {
                        assert_eq!(
                            s.asserted.get(&l.term),
                            Some(&l.value),
                            "certified conflict cites a non-asserted literal"
                        );
                    }
                }
            }
        }
        eprintln!(
            "[float-layer] random UNSAT sweep: {certified}/{attempts} certified ({:.0}%)",
            100.0 * certified as f64 / attempts as f64
        );
        assert!(
            certified > 0,
            "expected some UNSAT certifications on infeasible corpus"
        );
    }

    #[test]
    fn test_infeasible_cert_reports_accept_stats() {
        let (mut s, _) = setup_unsat();
        let (a0, c0, _) = stats::unsat_snapshot();
        let res = s.try_float_certified_with_min_rows(1);
        assert!(matches!(res, Some(TheoryResult::UnsatWithFarkas(_))));
        let (a1, c1, _) = stats::unsat_snapshot();
        assert!(
            a1 > a0 && c1 > c0,
            "unsat attempt+certify counters must advance"
        );
    }

    #[test]
    fn test_strict_bounds_certify() {
        // x0,x1 in [0,10]; s2 = x0 + x1 with 4 < s2 (strict lower) and s2 <= 6.
        let terms = TermStore::new();
        let mut s = LraSolver::new(&terms);
        s.vars.push(nb(Some(0), Some(10)));
        s.vars.push(nb(Some(0), Some(10)));
        s.next_var = 2;
        let expr = LinearExpr {
            coeffs: vec![(0, rat(1)), (1, rat(1))],
            constant: rat(0),
        };
        let (slack, _) = s.get_or_create_slack(&expr);
        s.vars[slack as usize].lower = Some(bnd(4, true)); // strict: s2 > 4
        s.vars[slack as usize].upper = Some(bnd(6, false));
        let basis = float_find_basis(&s.rows, &s.vars, 10_000).expect("shadow basis");
        let res = s.certify_candidate_basis(&basis);
        assert!(matches!(res, Some(TheoryResult::Sat)));
        // s2 must be strictly greater than 4 in the delta-rational sense; the
        // installed x0+x1 rational part is >= 4 and feasible under the eps.
        let vs = s.vars[slack as usize].value.x_approx_f64();
        assert!((4.0 - 1e-9..=6.0 + 1e-9).contains(&vs), "s2={vs}");
    }
}
