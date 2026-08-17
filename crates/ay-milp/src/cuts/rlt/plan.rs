// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Screened and exact RLT candidate construction.

use super::*;

/// THE PLAN for one (row, orientation, bound factor, branch): which face every product term
/// takes, decided once in `f64`, plus the `f64` violation the resulting cut would have at `x*`.
///
/// # Why there is a screen at all
///
/// Every candidate has to be COLLECTED before anyone can tell whether it separates, and the
/// overwhelming majority do not: on qnet1 the family derives roughly six thousand candidates a
/// round and the LARGEST violation among them is `5.4e-13` — every single level-1 RLT statement
/// is tight at that vertex. Paying `BigRational` for all six thousand to learn that is what made
/// the first version of this family cost 0.19s a round on a 0.4s instance (p0201) for two cuts.
///
/// So the collection runs twice: once in `f64` to decide the faces and price the violation, and
/// once in exact rationals for the handful that clear the floor. This is the same two-pass shape
/// `best_over_deltas` uses for the same reason.
///
/// # The screen cannot cost soundness, and that is structural
///
/// The screen decides only WHETHER to derive, and the emitted cut is built entirely from the
/// exact pass. A screen that rounds optimistically wastes one exact derivation; a screen that
/// rounds pessimistically forgoes one cut. Neither can emit an invalid inequality, because the
/// screen never reaches a coefficient. The face TAGS are shared rather than re-decided, so the
/// two passes cannot disagree about which valid inequality they are pricing.
///
/// The screen's floor is deliberately HALF [`MIN_VIOLATION`]: the two passes agree to about
/// `1e-13` on real rows, so half the floor is many orders of margin against ever screening out a
/// cut the exact pass would have admitted.
pub(super) fn rlt_plan(
    model: &Model,
    x: &[f64],
    coeffs: &[(u32, f64)],
    sign: f64,
    rhs_raw: f64,
    i: usize,
    branch_one: bool,
    ov_of: &dyn Fn(usize) -> Option<RltExact>,
    out: &mut Vec<(usize, f64, RltFace)>,
) -> Option<f64> {
    out.clear();
    let b = sign * rhs_raw;
    if !b.is_finite() {
        return None;
    }
    let x_i = *x.get(i)?;
    let at = |j: usize| x.get(j).copied().unwrap_or(0.0);

    let mut a_i = 0.0f64;
    let mut sum_ap = 0.0f64; // P
    let mut konst = 0.0f64; // K
    let mut lhs = 0.0f64; // Σ_{j≠i} (cut coefficient)·x*_j
    let mut n_exact = 0usize;
    let mut n_terms = 0usize;

    for &(c, raw) in coeffs {
        let j = c as usize;
        let a = sign * raw;
        if a == 0.0 || !a.is_finite() {
            if a != 0.0 {
                return None;
            }
            continue;
        }
        if j == i {
            a_i = a;
            out.push((j, raw, RltFace::Zero)); // face unused for the multiplier's own term
            continue;
        }
        // (1a): a_j > 0 ⇒ lower support. (1b): a_j > 0 ⇒ upper support.
        let want_lower = if branch_one { a > 0.0 } else { a < 0.0 };
        let ov = ov_of(j);
        if ov.is_some() {
            n_exact += 1;
        }
        let face = rlt_face(model, x_i, at(j), j, want_lower, ov)?;
        let (lo, up) = model.col_bounds(Col(j as u32));
        let (p, q, r) = face.pqr_f64(lo, up);
        sum_ap += a * p;
        konst += a * r;
        let cj = if branch_one { a * q } else { a * (1.0 - q) };
        if cj != 0.0 {
            lhs += cj * at(j);
            n_terms += 1;
        }
        out.push((j, raw, face));
    }
    // A cut every one of whose product terms was McCormick-RELAXED is, on the models this crate
    // sees, implied by the row it came from. The strength is in the exact substitutions; require
    // at least one, so a generic pass does not flood the pool with dominated rows.
    if n_exact == 0 {
        return None;
    }
    let (coef_i, rhs) = if branch_one {
        (sum_ap + a_i - b, -konst)
    } else {
        (b - sum_ap, b + konst)
    };
    if coef_i != 0.0 {
        lhs += coef_i * x_i;
        n_terms += 1;
    }
    if n_terms < 2 || !lhs.is_finite() || !rhs.is_finite() {
        return None;
    }
    Some(lhs - rhs)
}

/// ONE RLT cut: row `Σ_j a_j·x_j ≤ b` (already oriented and signed) times bound factor `i`,
/// derived in EXACT rationals from the face plan [`rlt_plan`] priced.
///
/// # The derivation, both branches, written out
///
/// Multiplying the row's non-negative slack by the non-negative factor `x_i`:
///
/// ```text
///   (1a)   Σ_j a_j·y_ij  ≤  b·x_i                      y_ij := x_i·x_j
/// ```
///
/// and by the non-negative factor `1 − x_i`:
///
/// ```text
///   (1b)   Σ_j a_j·x_j − Σ_j a_j·y_ij  ≤  b − b·x_i
/// ```
///
/// Both hold for every point of the CONTINUOUS relaxation. Integrality enters at exactly one
/// place, `y_ii = x_i·x_i = x_i` for `x_i ∈ {0,1}` — which is why an RLT cut is valid for the
/// integer hull and may legitimately cut the LP point, and why a brute-force guard on it must
/// enumerate INTEGER points and not sweep the polytope.
///
/// `y` is not a column of the model, so every product term is replaced by a linear support
/// `y_ij ⋛ p_j·x_i + q_j·x_j + r_j`. The DIRECTION is forced, and it is the same rule in both
/// branches — I derived a wrong cut by hand getting this backwards, so it is written out:
///
/// * In (1a) the aggregate `Σ a_j y_ij` stands on the SMALL side of `≤`, so replacing it by
///   anything NO LARGER keeps the inequality implied. Per term: `a_j > 0` needs a LOWER support
///   on `y_ij`; `a_j < 0` needs an UPPER one.
/// * In (1b) the aggregate appears NEGATED on the small side, so it must be replaced by anything
///   NO SMALLER — i.e. per term `a_j > 0` needs an UPPER support, `a_j < 0` a LOWER one.
///
/// The multiplier's own term is exact in both: `a_i·y_ii = a_i·x_i` in (1a), and in (1b) it is
/// `a_i·x_i − a_i·x_i = 0` and cancels outright.
///
/// Collecting, with `P = Σ_{j≠i} a_j·p_j` and `K = Σ_{j≠i} a_j·r_j`:
///
/// ```text
///   (1a)   (P + a_i − b)·x_i  +  Σ_{j≠i} a_j·q_j·x_j        ≤  −K
///   (1b)   (b − P)·x_i        +  Σ_{j≠i} a_j·(1 − q_j)·x_j  ≤  b + K
/// ```
///
/// # Validity is a two-case check, and that is the whole obligation
///
/// The result is linear and `x_i` is binary, so it is valid for the integer hull exactly when its
/// restriction at `x_i = 0` and its restriction at `x_i = 1` are each implied by the row plus the
/// boxes. Every step above is a substitution that is valid at both values of `x_i` separately, so
/// the composition is too. Anything that cannot be discharged this way is not understood well
/// enough to emit.
///
/// # Exactness
///
/// Every coefficient, product and sum is `BigRational` throughout; nothing is computed in `f64`.
/// [`emit_le_cut`] then rounds coefficients DOWN and the right-hand side UP, which on `x ≥ 0`
/// can only RELAX a `≤` cut, and refuses any column with `lo < 0` — the derivation does not lean
/// on that refusal, it just declines to store what it cannot round safely.
pub(super) fn rlt_cut_from_row(
    model: &Model,
    x: &[f64],
    plan: &[(usize, f64, RltFace)],
    sign: f64,
    rhs_raw: f64,
    i: usize,
    branch_one: bool,
) -> Option<Cut> {
    let b = exact(sign * rhs_raw)?;
    let mut a_i = BigRational::zero();
    let mut sum_ap = BigRational::zero(); // P
    let mut konst = BigRational::zero(); // K
    let mut per_col: Vec<(usize, BigRational, BigRational)> = Vec::new(); // (j, a_j, q_j)

    for &(j, raw, face) in plan {
        let a = exact(sign * raw)?;
        if j == i {
            a_i = a;
            continue;
        }
        let (lo, up) = model.col_bounds(Col(j as u32));
        let (p, q, r) = face.pqr(lo, up)?;
        sum_ap += &a * &p;
        konst += &a * &r;
        per_col.push((j, a, q));
    }
    if per_col.is_empty() {
        return None;
    }

    let mut terms: std::collections::BTreeMap<usize, BigRational> =
        std::collections::BTreeMap::new();
    let one: BigRational = One::one();
    let (coef_i, rhs) = if branch_one {
        for (j, a, q) in &per_col {
            if !q.is_zero() {
                *terms.entry(*j).or_insert_with(BigRational::zero) += a * q;
            }
        }
        (&sum_ap + &a_i - &b, -&konst)
    } else {
        for (j, a, q) in &per_col {
            let f = &one - q;
            if !f.is_zero() {
                *terms.entry(*j).or_insert_with(BigRational::zero) += a * &f;
            }
        }
        (&b - &sum_ap, &b + &konst)
    };
    if !coef_i.is_zero() {
        *terms.entry(i).or_insert_with(BigRational::zero) += &coef_i;
    }
    terms.retain(|_, v| !v.is_zero());
    if terms.len() < 2 {
        return None;
    }
    let cut = emit_le_cut(model, &terms, &rhs)?;
    clears_min_violation(&cut, x).then_some(cut)
}
