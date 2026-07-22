// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Port of Z3's `mutate_assignment` final-check heuristic.
//!
//! When the simplex reaches a feasible LP point but multiple shared variables
//! land on the same value, there is no way for the SAT solver to separate them
//! unless we either (a) tell CDCL the candidate equality via
//! `discover_model_value_equalities` (Z3's `assume_eqs`) or (b) nudge the LP
//! off the degenerate all-equal point via a random feasible perturbation. In
//! pure QF_LIA with pairwise `(distinct ...)` constraints the LP tends to
//! latch onto integer points that force infinite disequality splits; Z3
//! breaks the cycle by combining both (a) and (b) inside the final-check
//! loop.
//!
//! This module implements step (b). It follows Z3's implementation closely:
//!
//! - `reference/z3/src/smt/theory_arith_aux.h:1879-1948` —
//!   `get_freedom_interval`: computes the interval `[l, u]` within which a
//!   non-basic variable `v` can be moved without breaking any row's
//!   tightened bounds, plus an integer modulus `m` that respects the LCM
//!   of non-integer coefficients in rows with integer basic variables.
//! - `reference/z3/src/smt/theory_arith_aux.h:2057-2113` —
//!   `random_update`: picks a feasible value for `v` inside the freedom
//!   interval, honoring the integer grid (and `m`) when `v` is an integer
//!   variable.
//! - `reference/z3/src/smt/theory_arith_aux.h:2116-2163` —
//!   `mutate_assignment`: groups shared variables by their LP value,
//!   perturbs one representative per value bucket, and lets the next
//!   `assume_eqs` / disequality round observe a fresh assignment.
//!
//! ay has no enode structure, so "relevant and shared" is approximated by
//! "appears in `var_to_term` and is not an internal slack" — mirroring the
//! filter in `discover_model_value_equalities`.

use std::sync::OnceLock;

use super::*;
use crate::rational::Rational;
use crate::types::InfRational;
use crate::VarStatus;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

/// Range used when a variable has no finite bound on one side. Matches Z3's
/// `#define RANGE 10000` (`theory_arith_aux.h:2050`).
const RANGE: i64 = 10_000;

/// Result of `get_freedom_interval`.
///
/// Semantics mirror Z3's out-parameters: `lower`/`upper` are `None` when
/// the corresponding side is unbounded, and `modulus` is the integer stride
/// required to keep all rows referencing `v` on the integer grid (1 when no
/// constraint applies).
#[derive(Debug, Clone)]
pub(crate) struct FreedomInterval {
    pub(crate) lower: Option<InfRational>,
    pub(crate) upper: Option<InfRational>,
    pub(crate) modulus: Rational,
}

impl LraSolver {
    /// Computes the freedom interval for a non-basic variable `x_j`.
    ///
    /// Returns `None` when the variable is basic or out of range (mirrors
    /// Z3's `return false` on `is_base(x_j)`). The returned interval is the
    /// range of values `x_j` may take without violating any bound on any
    /// basic variable depending on it.
    ///
    /// Reference: `reference/z3/src/smt/theory_arith_aux.h:1879-1948`.
    pub(crate) fn get_freedom_interval(&self, x_j: u32) -> Option<FreedomInterval> {
        let vj = x_j as usize;
        let info = self.vars.get(vj)?;
        if !matches!(info.status, Some(VarStatus::NonBasic)) {
            return None;
        }

        let x_j_is_int = self.var_is_integer(x_j);
        let x_j_val: InfRational = info.value.clone();

        let mut lower: Option<InfRational> = None;
        let mut upper: Option<InfRational> = None;
        let mut modulus = Rational::Small(1, 1);

        // Start from the variable's own bounds.
        if let Some(lb) = info.lower.as_ref() {
            lower = Some(lb.as_inf(BoundType::Lower));
            tighten_if_fixed(&lower, &upper);
        }
        if let Some(ub) = info.upper.as_ref() {
            upper = Some(ub.as_inf(BoundType::Upper));
            if fixed_hit(&lower, &upper) {
                return Some(FreedomInterval {
                    lower,
                    upper,
                    modulus,
                });
            }
        }

        // Walk columns: each row contributes a constraint of the form
        // `x_i + a_ij * x_j + (rest) = 0`, so shifting x_j by delta moves
        // x_i by -a_ij * delta. The row bounds on x_i translate into
        // interval constraints on x_j.
        if vj >= self.col_index.len() {
            return Some(FreedomInterval {
                lower,
                upper,
                modulus,
            });
        }
        for entry in &self.col_index[vj] {
            if entry.row_idx >= self.rows.len() {
                continue;
            }
            let row = &self.rows[entry.row_idx];
            let x_i = row.basic_var;
            let vi = x_i as usize;
            if vi >= self.vars.len() {
                continue;
            }

            // Fetch a_ij from the row. Z3 stores the coefficient on the
            // column entry; we look it up through the row.
            let a_ij = match row.coeff_ref(x_j) {
                Some(c) if !c.is_zero() => c.clone(),
                _ => continue,
            };

            let x_i_is_int = self.var_is_integer(x_i);
            if x_j_is_int && x_i_is_int && !a_ij.is_integer() {
                // Accumulate lcm of denominators (Rational denominators are
                // positive). Z3 uses `lcm(m, denominator(a_ij))`.
                let denom = denom_bigint(&a_ij);
                modulus = lcm_big(&modulus, &denom);
            }

            let x_i_val = &self.vars[vi].value;
            let x_i_lower = self.vars[vi].lower.as_ref();
            let x_i_upper = self.vars[vi].upper.as_ref();
            let a_neg = a_ij.is_negative();

            // Compute candidate new bounds for x_j from each x_i bound.
            // `x_j_val + (x_i_val - x_i_bound)/a_ij`.
            let recip = a_ij.recip();
            let negate = a_neg;

            if let Some(bound) = x_i_lower {
                let bv = bound.as_inf(BoundType::Lower);
                let diff_inf = sub_inf(x_i_val, &bv);
                let shifted = mul_inf(&diff_inf, &recip);
                let candidate = add_inf(&x_j_val, &shifted);
                if negate {
                    // a_neg: updates lower
                    update_lower(&mut lower, candidate);
                } else {
                    update_upper(&mut upper, candidate);
                }
                if fixed_hit(&lower, &upper) {
                    return Some(FreedomInterval {
                        lower,
                        upper,
                        modulus,
                    });
                }
            }
            if let Some(bound) = x_i_upper {
                let bv = bound.as_inf(BoundType::Upper);
                let diff_inf = sub_inf(x_i_val, &bv);
                let shifted = mul_inf(&diff_inf, &recip);
                let candidate = add_inf(&x_j_val, &shifted);
                if negate {
                    // a_neg: updates upper
                    update_upper(&mut upper, candidate);
                } else {
                    update_lower(&mut lower, candidate);
                }
                if fixed_hit(&lower, &upper) {
                    return Some(FreedomInterval {
                        lower,
                        upper,
                        modulus,
                    });
                }
            }
        }
        Some(FreedomInterval {
            lower,
            upper,
            modulus,
        })
    }

    /// Perturb a non-basic variable to a new feasible value if possible.
    ///
    /// Returns `true` when the variable's value was changed.
    ///
    /// Reference: `reference/z3/src/smt/theory_arith_aux.h:2057-2113`.
    pub(crate) fn random_update(&mut self, v: u32) -> bool {
        let vi = v as usize;
        if vi >= self.vars.len() {
            return false;
        }
        // Skip fixed (lower == upper non-strict) and basic variables.
        if self.is_var_fixed_for_offset_eq(v) {
            return false;
        }
        if !matches!(self.vars[vi].status, Some(VarStatus::NonBasic)) {
            return false;
        }

        let fi = match self.get_freedom_interval(v) {
            Some(fi) => fi,
            None => return false,
        };
        let is_int = self.var_is_integer(v);

        // Snap to integer grid when v is an integer variable.
        let mut lower = fi.lower;
        let mut upper = fi.upper;
        let modulus = fi.modulus;

        if is_int {
            if let Some(l) = lower.take() {
                lower = Some(ceil_inf_to_modulus(&l, &modulus));
            }
            if let Some(u) = upper.take() {
                upper = Some(floor_inf_to_modulus(&u, &modulus));
            }
        }

        // If the feasible set collapsed after snapping, give up.
        if let (Some(l), Some(u)) = (lower.as_ref(), upper.as_ref()) {
            if l >= u {
                return false;
            }
        }

        let rnd = next_random(&mut self.pivot_rng) as i64;
        let new_val = match (lower, upper) {
            (None, None) => {
                // Unbounded both sides: pick a random value in [0, RANGE].
                InfRational::from_rat(Rational::from(rnd % (RANGE + 1)))
            }
            (Some(l), None) => {
                let delta = rnd % (RANGE + 1);
                // new = l + m * delta
                let step = mul_rational_by_i64(&modulus, delta);
                add_inf(&l, &InfRational::from_rat(step))
            }
            (None, Some(u)) => {
                let delta = rnd % (RANGE + 1);
                // new = u - m * delta
                let step = mul_rational_by_i64(&modulus, delta);
                sub_inf(&u, &InfRational::from_rat(step))
            }
            (Some(l), Some(u)) => {
                if !is_int {
                    // new = l + (rnd / RANGE) * (u - l)
                    let diff = sub_inf(&u, &l);
                    let scaled = inf_mul_rational(&diff, &Rational::new(rnd, RANGE));
                    add_inf(&l, &scaled)
                } else {
                    // Integer case: new = l + m * (rnd % (range + 1)).
                    // `range` = floor((u - l) / m) so new stays inside [l, u].
                    let u_x = u.x_rational();
                    let l_x = l.x_rational();
                    let diff = &u_x - &l_x;
                    let range_cap = integer_range_cap(&diff, &modulus);
                    if range_cap == 0 {
                        return false;
                    }
                    let delta_i = (rnd.rem_euclid(range_cap + 1)).max(0);
                    let step = mul_rational_by_i64(&modulus, delta_i);
                    let new_x = &l_x + &step;
                    InfRational::from_rat(new_x)
                }
            }
        };

        if new_val == self.vars[vi].value {
            return false;
        }
        self.update_nonbasic(v, new_val);
        true
    }

    /// Final-check heuristic: nudge shared variables off repeated LP values.
    ///
    /// Mirrors Z3's `mutate_assignment` (`theory_arith_aux.h:2116-2163`).
    /// Returns `true` when any variable was actually perturbed, so callers can
    /// decide whether to rerun the downstream fixups (simplex pivot repair,
    /// `discover_model_value_equalities`) or stop.
    ///
    /// This is an allocation-light O(shared_vars + rows_touched) routine; it
    /// is gated by a per-`check_impl` budget in the caller.
    pub(crate) fn mutate_assignment(&mut self) -> bool {
        // Collect (value_key, var_id) for relevant/shared variables. ay
        // approximates Z3's `is_relevant_and_shared` with "has a term and is
        // not a slack" — the same filter used by
        // `discover_model_value_equalities` so the two routines stay in sync.
        let mut entries: Vec<(InfRational, u32, TermId)> = Vec::new();
        for (&var_id, &term_id) in &self.var_to_term {
            if self.slack_var_set.contains(&var_id) {
                continue;
            }
            let vi = var_id as usize;
            if vi >= self.vars.len() {
                continue;
            }
            entries.push((self.vars[vi].value.clone(), var_id, term_id));
        }
        if entries.len() < 2 {
            return false;
        }

        // Deterministic order.
        entries.sort_by(|a, b| a.0.cmp(&b.0).then(a.2 .0.cmp(&b.2 .0)));

        // Find the first variable in each value bucket that is not fixed;
        // mark the rest as candidates for perturbation (matches Z3's
        // `m_var_value_table.insert_if_not_there` semantics, but we already
        // grouped by value via sorting).
        let mut candidates: Vec<u32> = Vec::new();
        let mut seen_anchor: Option<(InfRational, u32)> = None;
        for (val, var, _term) in entries {
            match &seen_anchor {
                Some((prev_val, prev_var)) if prev_val == &val => {
                    if !self.is_var_fixed_for_offset_eq(var) {
                        candidates.push(var);
                    } else if !self.is_var_fixed_for_offset_eq(*prev_var)
                        && !candidates.contains(prev_var)
                    {
                        candidates.push(*prev_var);
                    }
                }
                _ => {
                    seen_anchor = Some((val, var));
                }
            }
        }

        if candidates.is_empty() {
            return false;
        }

        let mut mutated = false;
        for v in candidates {
            let vi = v as usize;
            if vi >= self.vars.len() {
                continue;
            }
            if self.is_var_fixed_for_offset_eq(v) {
                continue;
            }
            let is_basic = matches!(self.vars[vi].status, Some(VarStatus::Basic(_)));
            if is_basic {
                // Find a non-fixed non-basic in v's defining row and perturb
                // it. ay stores the row index directly on the var status.
                let row_idx = match self.vars[vi].status {
                    Some(VarStatus::Basic(idx)) => idx,
                    _ => continue,
                };
                if row_idx >= self.rows.len() {
                    continue;
                }
                let mut nonbasic_candidate: Option<u32> = None;
                for (nb_var, _coeff) in self.rows[row_idx].coeffs.iter() {
                    if *nb_var == v {
                        continue;
                    }
                    if self.is_var_fixed_for_offset_eq(*nb_var) {
                        continue;
                    }
                    nonbasic_candidate = Some(*nb_var);
                    break;
                }
                if let Some(nb) = nonbasic_candidate {
                    if self.random_update(nb) {
                        mutated = true;
                    }
                }
            } else if self.random_update(v) {
                mutated = true;
            }
        }
        mutated
    }

    /// Reports whether the LraSolver should run the mutate_assignment pass at
    /// all for the current check(). Gated identically to
    /// `discover_model_value_equalities`: Nelson-Oppen combined mode, or pure
    /// LIA/LRA with at least one active disequality constraint.
    pub(crate) fn mutate_assignment_enabled(&self) -> bool {
        if self.combined_theory_mode {
            return true;
        }
        !self.disequality_trail.is_empty() || !self.shared_disequality_trail.is_empty()
    }

    /// Best-effort check whether `v` corresponds to an Int-sorted term.
    ///
    /// The LRA solver does not carry per-variable sort metadata; we rely on
    /// the same logic used by `discover_model_value_equalities` to determine
    /// "int-ness": prefer the term's SMT sort, fall back to the solver-wide
    /// integer_mode flag (set by the LIA wrapper).
    pub(crate) fn var_is_integer(&self, v: u32) -> bool {
        if let Some(&term) = self.var_to_term.get(&v) {
            if !term.is_sentinel() {
                let terms_ptr = self.terms_ptr;
                if !terms_ptr.is_null() {
                    // SAFETY: same contract as `terms()` elsewhere in this
                    // crate — valid only while set_terms()/unset_terms()
                    // brackets hold, which callers of check() guarantee.
                    let ts = unsafe { &*terms_ptr };
                    return *ts.sort(term) == ay_core::Sort::Int;
                }
            }
        }
        self.integer_mode
    }
}

// ---------- helpers ----------------------------------------------------------

fn tighten_if_fixed(_lower: &Option<InfRational>, _upper: &Option<InfRational>) {
    // No-op: placeholder mirrors Z3's IS_FIXED macro which is applied after
    // each SET_LOWER/SET_UPPER. We inline equivalent checks at the call site
    // via `fixed_hit`.
}

fn fixed_hit(lower: &Option<InfRational>, upper: &Option<InfRational>) -> bool {
    matches!(
        (lower, upper),
        (Some(l), Some(u)) if l == u
    )
}

fn update_lower(slot: &mut Option<InfRational>, candidate: InfRational) {
    match slot {
        Some(existing) if *existing >= candidate => {}
        _ => {
            *slot = Some(candidate);
        }
    }
}

fn update_upper(slot: &mut Option<InfRational>, candidate: InfRational) {
    match slot {
        Some(existing) if *existing <= candidate => {}
        _ => {
            *slot = Some(candidate);
        }
    }
}

fn add_inf(a: &InfRational, b: &InfRational) -> InfRational {
    a + b
}

fn sub_inf(a: &InfRational, b: &InfRational) -> InfRational {
    a - b
}

fn mul_inf(a: &InfRational, c: &Rational) -> InfRational {
    a.mul_rat(c)
}

fn inf_mul_rational(a: &InfRational, c: &Rational) -> InfRational {
    a.mul_rat(c)
}

fn mul_rational_by_i64(r: &Rational, n: i64) -> Rational {
    r * &Rational::from(n)
}

/// Return the denominator of `a_ij` as a BigInt.
fn denom_bigint(r: &Rational) -> BigInt {
    match r {
        Rational::Small(_, d) => BigInt::from(*d),
        Rational::Big(br) => br.denom().clone(),
    }
}

/// LCM of a Rational (treated as denominator) and a BigInt `d`.
fn lcm_big(modulus: &Rational, d: &BigInt) -> Rational {
    // Current modulus is kept as an integer Rational (denominator 1). If it
    // is a fraction (shouldn't happen here), promote to BigRational via
    // Rational::new_big. For safety we detect the common Small integer path.
    let m_int: BigInt = match modulus {
        Rational::Small(n, 1) => BigInt::from(*n),
        Rational::Small(n, dn) => {
            // Non-integer: promote, but keep lcm over numerator only since
            // denominators are normalized out.
            let g = num_integer::gcd(BigInt::from(*n), BigInt::from(*dn));
            (BigInt::from(*n) / g).abs()
        }
        Rational::Big(br) => br.numer().clone().abs(),
    };
    if m_int.is_zero() || d.is_zero() {
        return modulus.clone();
    }
    let g = m_int.gcd(d);
    let lcm = (&m_int / &g) * d;
    let lcm_abs = lcm.abs();
    Rational::Big(BigRational::from_integer(lcm_abs))
}

/// Compute `ceil(x / m) * m`. Matches Z3's
/// `l = ceil(l); if (!m.is_one()) l = m*ceil(l/m);` combined into one step.
fn ceil_inf_to_modulus(x: &InfRational, m: &Rational) -> InfRational {
    let xr = x.x_rational();
    let eps = x.epsilon();
    // If the epsilon component is strictly positive, an open-lower bound at
    // integer value c means x_j > c, so the minimum feasible integer is c+1.
    let raw_ceil = xr.ceil();
    let mut integer_l = BigInt::from(raw_ceil);
    if !eps.is_zero() && eps.is_positive() && xr.is_integer() {
        integer_l += BigInt::one();
    }
    if m.is_one() {
        return InfRational::from_rational(BigRational::from_integer(integer_l));
    }
    // ceil(integer_l / m) * m.
    let m_br = m.to_big();
    let l_big = BigRational::from_integer(integer_l);
    let q = &l_big / &m_br;
    let k = q.ceil().to_integer();
    let snapped = &m_br * BigRational::from_integer(k);
    InfRational::from_rational(snapped)
}

/// Compute `floor(x / m) * m`, respecting open upper bounds.
fn floor_inf_to_modulus(x: &InfRational, m: &Rational) -> InfRational {
    let xr = x.x_rational();
    let eps = x.epsilon();
    let raw_floor = xr.floor();
    let mut integer_u = BigInt::from(raw_floor);
    if !eps.is_zero() && eps.is_negative() && xr.is_integer() {
        integer_u -= BigInt::one();
    }
    if m.is_one() {
        return InfRational::from_rational(BigRational::from_integer(integer_u));
    }
    let m_br = m.to_big();
    let u_big = BigRational::from_integer(integer_u);
    let q = &u_big / &m_br;
    let k = q.floor().to_integer();
    let snapped = &m_br * BigRational::from_integer(k);
    InfRational::from_rational(snapped)
}

/// Compute `min(floor((u - l) / m), RANGE)` as an i64 step count.
fn integer_range_cap(diff: &Rational, m: &Rational) -> i64 {
    if diff.is_zero() {
        return 0;
    }
    let ratio = diff / m;
    let ratio_big = ratio.to_big();
    let steps = ratio_big.floor().to_integer();
    use num_traits::ToPrimitive;
    match steps.to_i64() {
        Some(k) if k >= 0 => k.min(RANGE),
        _ => RANGE,
    }
}

/// xorshift32 PRNG, same generator as the pivot rng. Advances the caller's
/// state in-place.
fn next_random(state: &mut u32) -> u32 {
    if *state == 0 {
        *state = seed_default();
    }
    let mut x = *state;
    x ^= x << 13;
    x ^= x >> 17;
    x ^= x << 5;
    *state = x;
    x
}

fn seed_default() -> u32 {
    static SEED: OnceLock<u32> = OnceLock::new();
    *SEED.get_or_init(|| 0x9E37_79B9)
}
