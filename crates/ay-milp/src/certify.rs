// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The exact rim of the float lane: adjudicate a candidate basis.
//!
//! [`crate::simplex`] searches in `f64` and returns a *basis* — which columns
//! are basic, and which bound each of the others rests on. A basis is a
//! combinatorial object: it is either optimal or it is not, and that question
//! has an exact answer no floating-point error can perturb. So the float lane
//! never reports a number. It proposes, and this module disposes:
//!
//! 1. solve `B x_B = -N x_N` in exact rationals and check every basic variable
//!    lies within its bounds (primal feasibility);
//! 2. solve `Bᵀ y = c_B` in exact rationals and check every non-basic reduced
//!    cost points the right way — `>= 0` at a lower bound, `<= 0` at an upper
//!    one, `== 0` for a free column (dual feasibility);
//! 3. if both hold, the basis IS optimal, and the duals hand us the certificate
//!    for free.
//!
//! A basis that fails either test is discarded and the caller falls back to the
//! exact rim. Rounding error can cost us a re-solve; it cannot cost us
//! correctness.
//!
//! ## The duals ARE the certificate
//!
//! [`OptimalityCertificate`] wants non-negative multipliers on oriented model
//! facts whose combination is exactly `objective − bound`. That is precisely
//! what an optimal dual solution is. Writing `d` for the reduced costs and `y`
//! for the row duals, the combination
//!
//! ```text
//!   Σ_{y_r > 0} y_r (a_r·x − lb_r)  +  Σ_{y_r < 0} (−y_r)(ub_r − a_r·x)
//! + Σ_{d_j > 0} d_j (x_j − l_j)     +  Σ_{d_j < 0} (−d_j)(u_j − x_j)
//! ```
//!
//! has `x`-coefficient `Aᵀy + d = Aᵀy + (c − Aᵀy) = c` — the objective, exactly —
//! and constant `−(Σ y_r β_r + Σ d_j γ_j)`, the negated dual objective, where
//! `β`/`γ` are the bounds those variables rest on. Complementary slackness makes
//! every multiplier land on the side its variable actually sits at, so no
//! multiplier ever references an infinite bound. The identity `cert.verify`
//! re-checks is therefore not an extra construction — it is LP duality itself.

use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive, Zero};

use crate::cert::{BoundSide, FactRef, Multiplier, OptimalityCertificate};
use crate::model::{exact, Col, Model, Row, Sense};
use crate::simplex::{Candidate, FloatLp, NbBound};

/// A basis proven optimal in exact arithmetic.
pub(crate) struct CertifiedOptimum {
    /// The exact optimal point, indexed by structural column.
    pub values: Vec<BigRational>,
    /// The exact optimal objective value, in the model's own sense, EXCLUDING
    /// the constant offset (the session folds that in).
    pub value: BigRational,
    pub cert: OptimalityCertificate,
}

/// Exact dense LU is cubic in the row count with growing numerators, so it is
/// worth doing only while the basis is small enough for that to beat re-solving
/// from scratch on the exact rim. Above this the caller takes the rim directly.
pub(crate) const MAX_EXACT_BASIS_ROWS: usize = 600;

/// Overridable for measurement.
pub(crate) fn max_exact_basis_rows() -> usize {
    std::env::var("AY_MILP_MAX_BASIS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(MAX_EXACT_BASIS_ROWS)
}

/// Solve `A z = b` exactly by Gaussian elimination with partial pivoting on the
/// first non-zero. `A` is consumed. `None` if singular.
///
/// Exact arithmetic needs no numerical pivoting — any non-zero pivot is as good
/// as any other for correctness — so the pivot search stops at the first
/// non-zero rather than hunting for the largest.
/// Solve `A z = b` exactly, with a SPARSE elimination.
///
/// A basis from a real model is sparse -- qnet1's is 503x503 with a few thousand non-zeros -- and a
/// DENSE elimination on it is the wrong algorithm by two orders of magnitude. It is also why the
/// exact replay of a leaf was capped at 400 rows and simply DECLINED above it: `O(d³)` in rationals
/// with growing numerators is not affordable at `d = 500`. On qnet1 that cap rejected every leaf the
/// search found -- 39 of 39 -- so no node was ever settled, and the instance reaches its true
/// optimum as an incumbent and cannot prove it.
///
/// Rows are held sparse, and the pivot is chosen by MARKOWITZ count -- among the rows that have a
/// non-zero in this column, take the one with the fewest non-zeros overall, because that is the row
/// whose elimination creates the least fill-in. Exact arithmetic needs no numerical pivoting (any
/// non-zero pivot is as good as any other for correctness), so the choice is free to be spent
/// entirely on sparsity.
pub(crate) fn solve_sparse(
    rows: Vec<std::collections::HashMap<usize, BigRational>>,
    mut b: Vec<BigRational>,
    deadline: Option<std::time::Instant>,
) -> Option<Vec<BigRational>> {
    use std::collections::hash_map::Entry;
    // How many pivots (or back-sub rows) between deadline checks. Each iteration is
    // heavy bignum work, so a small stride costs nothing (<0.1%) and bounds the
    // overshoot: an exact solve that cannot finish in budget DECLINES (fail-closed —
    // a decline can only cost an incumbent, never mint a verdict). Without this, a
    // single large-basis solve overshot a caller's 60s budget by tens of seconds.
    const DEADLINE_STRIDE: usize = 16;
    let n = b.len();
    let mut a = rows;
    debug_assert_eq!(a.len(), n);

    // FULL MARKOWITZ pivoting, singleton-first. The earlier version pivoted the columns
    // in fixed index order (0..n) and chose only the pivot ROW for sparsity. On a basis
    // whose natural column order is not an elimination order that stays sparse, that
    // fills in badly: an NN big-M basis is a near-triangular DAG (3790 structural rows on
    // the cifar100 w2 window) and fixed-order elimination densified it into a blow-up that
    // never returned. Here the pivot is the (unused row, unsolved column) with the least
    // Markowitz count `(row_nnz-1)·(col_nnz-1)`; a singleton (count 0) creates no fill, so
    // a triangular system is solved as pure substitution with bounded (dyadic) growth.
    // Exact arithmetic makes ANY non-zero pivot correct, so the order is spent entirely on
    // sparsity, never on numerical stability -- and `exact_point`'s result is re-checked by
    // `Model::check_point` regardless, so a mis-solve can only decline, never mislead.
    let mut used_row = vec![false; n];
    let mut solved_col = vec![false; n];
    // Live occurrences: how many not-yet-used rows still carry a non-zero in each column.
    let mut col_nnz = vec![0usize; n];
    for row in &a {
        for &c in row.keys() {
            col_nnz[c] += 1;
        }
    }
    // The k-th pivot's row and column; back-substitution runs these in reverse. A
    // `usize::MAX` row marks an unused slot when the system closes before every row is
    // consumed (dependent rows).
    let mut pivot_row = vec![usize::MAX; n];
    let mut pivot_col = vec![0usize; n];

    let dbg = std::env::var_os("AY_MILP_SOLVE_DBG").is_some();
    let t0 = std::time::Instant::now();

    for k in 0..n {
        if k % DEADLINE_STRIDE == 0 {
            if let Some(d) = deadline {
                if std::time::Instant::now() >= d {
                    return None;
                }
            }
        }
        if dbg && k % 256 == 0 && k > 0 {
            let live_nnz: usize = a
                .iter()
                .enumerate()
                .filter(|(i, _)| !used_row[*i])
                .map(|(_, r)| r.len())
                .sum();
            let max_bits = a
                .iter()
                .flat_map(|r| r.values())
                .map(|v| v.numer().bits().max(v.denom().bits()))
                .max()
                .unwrap_or(0);
            eprintln!(
                "AY_MILP_TRACE solve_sparse pivot {k}/{n} @ {:.1}s: live_nnz={live_nnz} max_bits={max_bits}",
                t0.elapsed().as_secs_f64()
            );
        }
        let mut best: Option<(usize, usize, usize)> = None; // (markowitz, row, col)
        'scan: for i in 0..n {
            if used_row[i] {
                continue;
            }
            let rlen = a[i].len(); // the map holds only non-zeros
            if rlen == 0 {
                // No structural entry left in this row: `0 == b[i]` is a dependent row
                // (harmless); `0 != b[i]` is an inconsistent (singular) basis.
                if !b[i].is_zero() {
                    return None;
                }
                continue;
            }
            for &c in a[i].keys() {
                if solved_col[c] {
                    continue;
                }
                let mark = (rlen - 1) * col_nnz[c].saturating_sub(1);
                if best.is_none_or(|(bm, _, _)| mark < bm) {
                    best = Some((mark, i, c));
                    if mark == 0 {
                        break 'scan; // nothing beats a singleton
                    }
                }
            }
        }
        let Some((_, p, c)) = best else {
            // No admissible pivot. Done if every column is already solved; otherwise the
            // basis is singular and the caller falls back to the exact rim.
            if (0..n).all(|cc| solved_col[cc]) {
                break;
            }
            return None;
        };
        used_row[p] = true;
        solved_col[c] = true;
        pivot_row[k] = p;
        pivot_col[k] = c;

        let pivot = a[p].get(&c)?.clone();
        let prow: Vec<(usize, BigRational)> = a[p].iter().map(|(&cc, v)| (cc, v.clone())).collect();
        // Row p leaves the live set: every column it holds loses one occurrence.
        for (cc, _) in &prow {
            col_nnz[*cc] -= 1;
        }
        let pb = b[p].clone();
        for i in 0..n {
            if used_row[i] {
                continue;
            }
            let Some(aic) = a[i].get(&c).cloned() else {
                continue;
            };
            let f = &aic / &pivot;
            for (cc, v) in &prow {
                match a[i].entry(*cc) {
                    Entry::Occupied(mut e) => {
                        *e.get_mut() -= &f * v;
                        if e.get().is_zero() {
                            e.remove();
                            col_nnz[*cc] -= 1;
                        }
                    }
                    Entry::Vacant(e) => {
                        let nv = -(&f * v);
                        if !nv.is_zero() {
                            e.insert(nv);
                            col_nnz[*cc] += 1;
                        }
                    }
                }
            }
            b[i] -= &f * &pb;
        }
    }

    // Back-substitute in reverse pivot order: row p keeps its pivot column plus columns
    // pivoted LATER, whose z is already known by the time we reach this step.
    if dbg {
        eprintln!(
            "AY_MILP_TRACE solve_sparse forward done @ {:.2}s; back-substituting",
            t0.elapsed().as_secs_f64()
        );
    }
    let mut z = vec![BigRational::zero(); n];
    for (done, k) in (0..n).rev().enumerate() {
        if done % DEADLINE_STRIDE == 0 {
            if let Some(d) = deadline {
                if std::time::Instant::now() >= d {
                    return None;
                }
            }
        }
        let p = pivot_row[k];
        if p == usize::MAX {
            continue; // slot the early close left unused
        }
        let c = pivot_col[k];
        // COMMON-DENOMINATOR ACCUMULATION. The obvious `acc -= v * &z[cc]` costs up
        // to FIVE Stein gcds per term at solution bit-size (num-rational's Mul runs
        // two cross-gcds plus a wasted coprime reduce; SubAssign with unequal
        // denominators runs an lcm-gcd plus a full reduce), and a ~1kbit gcd costs
        // hundreds of same-size multiplies — measured, gcds were ~80-90% of this
        // loop. Accumulate one BigInt numerator over a running denominator instead:
        // raw integer multiplies on the fast paths (equal or dividing denominators —
        // the common case, since a row's term denominators come from the same
        // elimination chain), one denominators-only gcd on the slow path, and defer
        // ALL reduction to a single `BigRational::new` per row. Every path computes
        // exactly `b[p] - Σ v·z[cc]`; the differential suite (800 systems, byte-vs-
        // `solve_dense`, exactly-zero residuals) is the net.
        let mut num: num_bigint::BigInt = b[p].numer().clone();
        let mut den: num_bigint::BigInt = b[p].denom().clone();
        for (&cc, v) in &a[p] {
            if cc == c || z[cc].is_zero() {
                continue;
            }
            let tn = v.numer() * z[cc].numer();
            let td = v.denom() * z[cc].denom();
            if den == td {
                num -= tn;
            } else if (&td % &den).is_zero() {
                // den | td: adopt the finer denominator.
                num = &num * (&td / &den) - tn;
                den = td;
            } else if (&den % &td).is_zero() {
                // td | den: scale the term up.
                num -= tn * (&den / &td);
            } else {
                // Unrelated denominators: one gcd, on the denominators only.
                use num_integer::Integer;
                let g = den.gcd(&td);
                let l = &den / &g * &td;
                num = &num * (&l / &den) - tn * (&l / &td);
                den = l;
            }
        }
        z[c] = BigRational::new(num, den) / a[p].get(&c)?;
        if dbg && done % 256 == 0 && done > 0 {
            let zbits = z
                .iter()
                .map(|v| v.numer().bits().max(v.denom().bits()))
                .max()
                .unwrap_or(0);
            eprintln!(
                "AY_MILP_TRACE solve_sparse back-sub {done}/{n} @ {:.1}s: max_z_bits={zbits}",
                t0.elapsed().as_secs_f64()
            );
        }
    }
    Some(z)
}

pub(crate) fn solve_dense(
    mut a: Vec<Vec<BigRational>>,
    mut b: Vec<BigRational>,
) -> Option<Vec<BigRational>> {
    let n = b.len();
    debug_assert!(a.len() == n && a.iter().all(|r| r.len() == n));
    for k in 0..n {
        let piv = (k..n).find(|&i| !a[i][k].is_zero())?;
        if piv != k {
            a.swap(k, piv);
            b.swap(k, piv);
        }
        // Eliminate below.
        for i in (k + 1)..n {
            if a[i][k].is_zero() {
                continue;
            }
            let f = &a[i][k] / &a[k][k];
            for j in k..n {
                let sub = &f * &a[k][j];
                a[i][j] -= sub;
            }
            let sub = &f * &b[k];
            b[i] -= sub;
        }
    }
    // Back-substitute.
    let mut z = vec![BigRational::zero(); n];
    for k in (0..n).rev() {
        let mut acc = b[k].clone();
        for j in (k + 1)..n {
            acc -= &a[k][j] * &z[j];
        }
        z[k] = acc / &a[k][k];
    }
    Some(z)
}

/// The exact `M`-column of `j` as `(row, coeff)` pairs: the CSC column for a
/// structural, `-e_r` for a logical.
pub(crate) fn m_column(lp: &FloatLp, j: usize) -> Vec<(usize, BigRational)> {
    if j < lp.n {
        lp.column(j)
            .map(|(r, a)| (r, exact(a).expect("finite coefficient")))
            .collect()
    } else {
        vec![(j - lp.n, -BigRational::from_integer(1.into()))]
    }
}

/// The exact primal point of a basis under `lower`/`upper`, with no certificate.
///
/// A branch-and-bound leaf cannot use [`certify_bounded`]: that builds a
/// certificate whose multipliers reference the MODEL's column bounds, while the
/// leaf lives inside a branched box, so the identity legitimately fails to close.
/// What the leaf actually needs is the exact POINT — which the caller then
/// re-checks against the model itself (`Model::check_point`, integrality
/// included). Returns `None` if the basis is singular or primal-infeasible.
/// How much wall clock the exact rim actually costs the search, and how often it is asked.
pub(crate) static EXACT_NANOS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
pub(crate) static EXACT_CALLS: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

pub(crate) fn exact_point(
    lp: &FloatLp,
    cand: &Candidate,
    lower: &[f64],
    upper: &[f64],
    deadline: Option<std::time::Instant>,
) -> Option<Vec<BigRational>> {
    use std::sync::atomic::Ordering::Relaxed;
    EXACT_CALLS.fetch_add(1, Relaxed);
    let _t = std::time::Instant::now();
    let out = exact_point_inner(lp, cand, lower, upper, deadline);
    EXACT_NANOS.fetch_add(_t.elapsed().as_nanos() as u64, Relaxed);
    out
}

fn exact_point_inner(
    lp: &FloatLp,
    cand: &Candidate,
    lower: &[f64],
    upper: &[f64],
    deadline: Option<std::time::Instant>,
) -> Option<Vec<BigRational>> {
    let z = exact_vertex_full(lp, cand, lower, upper, deadline)?;
    // Reject the vertex if any BASIC variable lands outside its bound: the float
    // basis's exact vertex is then infeasible and the caller must fall back.
    // Nonbasics sit exactly on a bound by construction, so only basics can violate.
    let trace = std::env::var_os("AY_MILP_TRACE").is_some();
    for &j in &cand.basis {
        if let Some(lo) = exact(lower[j]) {
            if z[j] < lo {
                if trace {
                    let d = (&lo - &z[j]).to_f64().unwrap_or(f64::NAN);
                    eprintln!(
                        "AY_MILP_TRACE !! exact_point: basic col {j} below its lower bound by {d:.3e}"
                    );
                }
                return None;
            }
        }
        if let Some(hi) = exact(upper[j]) {
            if z[j] > hi {
                if trace {
                    let d = (&z[j] - &hi).to_f64().unwrap_or(f64::NAN);
                    eprintln!(
                        "AY_MILP_TRACE !! exact_point: basic col {j} above its upper bound by {d:.3e}"
                    );
                }
                return None;
            }
        }
    }
    Some(z[..lp.n].to_vec())
}

/// Reconstruct a float basis's EXACT vertex — the full `cols`-length point
/// (structural then logical), nonbasics pinned to their resting bound, basics
/// solved exactly from `B·x_B = rhs`. Unlike [`exact_point`], it does NOT reject
/// an out-of-bounds basic: it returns the raw vertex so a caller can measure the
/// exact bound violations (the input to iterative refinement — float violations
/// sit below the simplex's own tolerance and miss ~1e-8 exact infeasibility).
/// `None` only on a non-basis, the row cap, a singular solve, or the deadline.
/// Soundness is unaffected: any point derived from it is re-checked exactly by
/// `Model::check_point` before it can become an incumbent.
pub(crate) fn exact_vertex_full(
    lp: &FloatLp,
    cand: &Candidate,
    lower: &[f64],
    upper: &[f64],
    deadline: Option<std::time::Instant>,
) -> Option<Vec<BigRational>> {
    exact_vertex_with_rest(lp, cand, lower, upper, None, None, deadline)
}

/// As [`exact_vertex_full`], but a column nonbasic at `NbBound::Zero` (a FREE
/// column, resting at 0 in the frame the basis was solved in) takes its value
/// from `zero_rest` when provided. Iterative refinement needs this: its refining
/// LP lives in the shifted frame `w = Δ(x − z*)`, where a free column resting at
/// `w = 0` means `x = z*_j` — pinning it to 0 reconstructs a DIFFERENT (weaker)
/// vertex. Every consumer's result is still re-checked by `check_point`.
pub(crate) fn exact_vertex_with_rest(
    lp: &FloatLp,
    cand: &Candidate,
    lower: &[f64],
    upper: &[f64],
    zero_rest: Option<&[BigRational]>,
    max_rows: Option<usize>,
    deadline: Option<std::time::Instant>,
) -> Option<Vec<BigRational>> {
    let m = lp.m;
    let mut is_basic = vec![false; lp.cols];
    for &j in &cand.basis {
        if j >= lp.cols || is_basic[j] {
            return None;
        }
        is_basic[j] = true;
    }
    // ELIMINATE THE BASIC LOGICALS FIRST -- they are free pivots.
    //
    // The basis is `m x m`, and solving it densely in rationals is cubic. But a logical's
    // column in `M = [A | -I]` is `-e_r`: ONE entry, in its own row. So a basic logical
    // pivots its own row for nothing, and every row it pivots drops out of the system: once
    // the structural basics are known, that row DEFINES the logical by back-substitution.
    //
    // What is left is square (|structural basics| = |rows whose logical is nonbasic|) and is
    // the only part that needs elimination. On a real model most rows are slack at a vertex,
    // so this is the difference between a 503x503 rational solve and a small one -- which is
    // the difference between qnet1 getting one node in twenty seconds and getting a search.
    //
    // Split (and cap-check) BEFORE the rhs build below: a cap decline used to cost the
    // whole rhs pass (~2s on the cifar100 w2 model) at every declined leaf.
    let mut logical_of_row: Vec<Option<usize>> = vec![None; m]; // row -> basis slot
    let mut structural: Vec<usize> = Vec::new(); // basis slots holding structural columns
    for (k, &j) in cand.basis.iter().enumerate() {
        if j >= lp.n {
            let r = j - lp.n;
            if r >= m || logical_of_row[r].is_some() {
                return None; // not a basis
            }
            logical_of_row[r] = Some(k);
        } else {
            structural.push(k);
        }
    }
    let rest: Vec<usize> = (0..m).filter(|&r| logical_of_row[r].is_none()).collect();
    if rest.len() != structural.len() {
        return None; // not a basis: the shapes must match
    }
    if std::env::var_os("AY_MILP_TRACE").is_some() {
        eprintln!(
            "AY_MILP_TRACE exact_point: structural basis {} (cap {}), {} rows",
            structural.len(),
            max_rows.unwrap_or_else(max_exact_basis_rows),
            m
        );
    }
    // The cap was always a COST proxy (exact elimination used to blow up on large
    // bases); a caller that threads a deadline may substitute a larger cap — the
    // deadline is the true bound now that the solve self-limits. `None` keeps the
    // measured default.
    if structural.len() > max_rows.unwrap_or_else(max_exact_basis_rows) {
        return None;
    }
    let mut z = vec![BigRational::zero(); lp.cols];
    for j in 0..lp.cols {
        if is_basic[j] {
            continue;
        }
        z[j] = match cand.at[j] {
            NbBound::Lower => exact(lower[j])?,
            NbBound::Upper => exact(upper[j])?,
            NbBound::Zero => match zero_rest {
                Some(rest) => rest[j].clone(),
                None => BigRational::zero(),
            },
        };
    }
    let dbg = std::env::var_os("AY_MILP_SOLVE_DBG").is_some();
    let t0 = std::time::Instant::now();
    if m > 0 {
        let mut rhs = vec![BigRational::zero(); m];
        for j in 0..lp.cols {
            // Deadline-guarded like the logical back-sub below: with zero_rest set
            // (refinement rounds ≥ 2 and every reconstruct-in-original-frame call)
            // the z[j].is_zero() short-circuit stops firing and this is a full
            // O(nnz) BigRational pass — 7.47M nnz on the cifar100 w5 window. A
            // decline is advice-lane fail-closed: the caller loses a candidate,
            // never gains a wrong one.
            if j % 256 == 0 {
                if let Some(d) = deadline {
                    if std::time::Instant::now() >= d {
                        return None;
                    }
                }
            }
            if is_basic[j] || z[j].is_zero() {
                continue;
            }
            for (r, a) in m_column(lp, j) {
                rhs[r] -= a * &z[j];
            }
        }

        let mut xb = vec![BigRational::zero(); m];
        if !structural.is_empty() {
            // SPARSE. The basis of a real model is sparse, and eliminating it densely is the wrong
            // algorithm by two orders of magnitude -- it is what forced the 400-row cap above, and
            // that cap rejected EVERY leaf qnet1's search found (39 of 39), so no node was ever
            // settled and the instance reaches its true optimum without being able to prove it.
            let d = structural.len();
            let mut brows: Vec<std::collections::HashMap<usize, BigRational>> =
                vec![std::collections::HashMap::new(); d];
            let mut brhs = vec![BigRational::zero(); d];
            let mut row_at: Vec<Option<usize>> = vec![None; m];
            for (i, &r) in rest.iter().enumerate() {
                row_at[r] = Some(i);
                brhs[i] = rhs[r].clone();
            }
            for (c, &k) in structural.iter().enumerate() {
                // Same guard as the rhs pass above: one f64→BigRational conversion
                // per basis-column nonzero, unbounded by any cap at w5 scale.
                if c % 256 == 0 {
                    if let Some(d) = deadline {
                        if std::time::Instant::now() >= d {
                            return None;
                        }
                    }
                }
                for (r, a) in m_column(lp, cand.basis[k]) {
                    if a.is_zero() {
                        continue;
                    }
                    if let Some(i) = row_at[r] {
                        brows[i].insert(c, a);
                    }
                }
            }
            if dbg {
                eprintln!(
                    "AY_MILP_TRACE exact_point brows built @ {:.2}s (d={d}); solve_sparse begins",
                    t0.elapsed().as_secs_f64()
                );
            }
            let sol = solve_sparse(brows, brhs, deadline)?;
            for (c, &k) in structural.iter().enumerate() {
                xb[k] = sol[c].clone();
            }
        }
        if dbg {
            eprintln!(
                "AY_MILP_TRACE exact_point solve done @ {:.2}s; logical back-sub begins ({} logical rows x {} structurals)",
                t0.elapsed().as_secs_f64(),
                logical_of_row.iter().filter(|l| l.is_some()).count(),
                structural.len()
            );
        }
        // Back-substitute each basic logical from the row it pivots:
        //   -x_{n+r} + sum over structural basics in row r  =  rhs[r]
        //
        // COLUMN-MAJOR, one walk per structural column. The obvious row-major form
        // (for each logical row, scan every structural basic's column for that row)
        // re-materializes every column — a Vec allocation plus an f64→BigRational
        // conversion PER ENTRY — `L × d` times: on the cifar100 w2 basis that is
        // 1021 × 3224 columns ≈ 10⁹ conversions to find one entry each, and it, not
        // the exact elimination, was the 200s+ wall in `exact_point` (the cost is
        // basis-DEPENDENT: L, the basic-logical count, varies wildly between bases).
        // Walking each column once and scattering into per-row accumulators visits
        // each nonzero exactly once; for any fixed row the contributions still arrive
        // in the same `structural` order, so the exact sum is IDENTICAL term-for-term.
        {
            let mut acc: Vec<Option<BigRational>> = vec![None; m];
            for r in 0..m {
                if logical_of_row[r].is_some() {
                    acc[r] = Some(-rhs[r].clone());
                }
            }
            for (walked, &ks) in structural.iter().enumerate() {
                if walked % 256 == 0 {
                    if let Some(d) = deadline {
                        if std::time::Instant::now() >= d {
                            return None;
                        }
                    }
                }
                if xb[ks].is_zero() {
                    continue;
                }
                for (rr, a) in m_column(lp, cand.basis[ks]) {
                    if let Some(av) = acc[rr].as_mut() {
                        *av += a * &xb[ks];
                    }
                }
            }
            for r in 0..m {
                let Some(k) = logical_of_row[r] else { continue };
                xb[k] = acc[r].take().expect("initialized above");
            }
        }

        if dbg {
            eprintln!(
                "AY_MILP_TRACE exact_point logical back-sub done @ {:.2}s; bound check begins",
                t0.elapsed().as_secs_f64()
            );
        }
        for (k, &j) in cand.basis.iter().enumerate() {
            z[j] = xb[k].clone();
        }
    }
    Some(z)
}

/// Adjudicate `cand` against `model`. `None` means "not proven optimal" — the
/// caller must fall back, never guess.
pub(crate) fn certify(model: &Model, lp: &FloatLp, cand: &Candidate) -> Option<CertifiedOptimum> {
    certify_bounded(model, lp, cand, &lp.lower, &lp.upper)
}

/// As [`certify`], but under a branch-and-bound node's tightened bounds.
///
/// The certificate is still checked against the ORIGINAL `model`, so a node's
/// certificate proves a statement about the node, not about the model — the
/// caller is responsible for only ever using it that way.
pub(crate) fn certify_bounded(
    model: &Model,
    lp: &FloatLp,
    cand: &Candidate,
    lower: &[f64],
    upper: &[f64],
) -> Option<CertifiedOptimum> {
    let n = lp.n;
    let m = lp.m;
    if m > MAX_EXACT_BASIS_ROWS {
        return None;
    }
    // The engine minimizes; a Maximize model was negated on the way in. Work in
    // that same minimize frame and un-negate at the end, so every sign rule here
    // is the textbook one.
    let minimize_cost = |j: usize| -> Option<BigRational> { exact(lp.cost[j]) };

    // O(1) basic test; `basis.contains` would make every sweep below quadratic.
    let mut is_basic = vec![false; lp.cols];
    for &j in &cand.basis {
        if j >= lp.cols || is_basic[j] {
            return None; // malformed basis: duplicate or out-of-range column
        }
        is_basic[j] = true;
    }

    // --- Non-basic values (exact). A column resting on a bound must HAVE that
    //     bound; a free column rests at zero. ---
    let mut z = vec![BigRational::zero(); lp.cols]; // full [x ; s]
    for j in 0..lp.cols {
        if is_basic[j] {
            continue; // basic; filled in below
        }
        let v = match cand.at[j] {
            NbBound::Lower => exact(lower[j])?,
            NbBound::Upper => exact(upper[j])?,
            NbBound::Zero => BigRational::zero(),
        };
        z[j] = v;
    }

    // --- Primal: B x_B = -N x_N. ---
    if m > 0 {
        let mut rhs = vec![BigRational::zero(); m];
        for j in 0..lp.cols {
            if is_basic[j] || z[j].is_zero() {
                continue;
            }
            for (r, a) in m_column(lp, j) {
                rhs[r] -= a * &z[j];
            }
        }
        let mut bmat = vec![vec![BigRational::zero(); m]; m];
        for (k, &j) in cand.basis.iter().enumerate() {
            for (r, a) in m_column(lp, j) {
                bmat[r][k] = a;
            }
        }
        let xb = solve_dense(bmat, rhs)?;
        for (k, &j) in cand.basis.iter().enumerate() {
            z[j] = xb[k].clone();
        }
        // Primal feasibility of the basics. (Non-basics sit on their bounds by
        // construction.)
        let trace = std::env::var_os("AY_MILP_TRACE").is_some();
        for &j in &cand.basis {
            if let Some(lo) = exact(lower[j]) {
                if z[j] < lo {
                    if trace {
                        let d = (&lo - &z[j]).to_f64().unwrap_or(f64::NAN);
                        eprintln!("AY_MILP_TRACE !! exact_point: basic col {j} below its lower bound by {d:.3e}");
                    }
                    return None;
                }
            }
            if let Some(hi) = exact(upper[j]) {
                if z[j] > hi {
                    if trace {
                        let d = (&z[j] - &hi).to_f64().unwrap_or(f64::NAN);
                        eprintln!("AY_MILP_TRACE !! exact_point: basic col {j} above its upper bound by {d:.3e}");
                    }
                    return None;
                }
            }
        }
    }

    // --- Dual: Bᵀ y = c_B. ---
    let mut y = vec![BigRational::zero(); m];
    if m > 0 {
        let mut bt = vec![vec![BigRational::zero(); m]; m];
        for (k, &j) in cand.basis.iter().enumerate() {
            for (r, a) in m_column(lp, j) {
                bt[k][r] = a; // transpose
            }
        }
        let cb: Option<Vec<BigRational>> = cand.basis.iter().map(|&j| minimize_cost(j)).collect();
        y = solve_dense(bt, cb?)?;
    }

    // --- Reduced costs, and dual feasibility. ---
    // d_j = c_j - y·M_j. A logical's column is -e_r with zero cost, so its
    // reduced cost is simply y_r.
    let mut d = vec![BigRational::zero(); lp.cols];
    for j in 0..lp.cols {
        let mut dot = BigRational::zero();
        for (r, a) in m_column(lp, j) {
            dot += a * &y[r];
        }
        d[j] = minimize_cost(j)? - dot;
    }
    for j in 0..lp.cols {
        if is_basic[j] {
            continue;
        }
        match cand.at[j] {
            NbBound::Lower if d[j].is_negative() => return None,
            NbBound::Upper if d[j].is_positive() => return None,
            NbBound::Zero if !d[j].is_zero() => return None,
            _ => {}
        }
    }

    // --- The certificate: the duals, oriented onto model facts. ---
    let mut multipliers: Vec<Multiplier> = Vec::new();
    for j in 0..lp.cols {
        if is_basic[j] {
            continue; // a basic column's reduced cost is zero by construction
        }
        let coeff = &d[j];
        if coeff.is_zero() {
            continue; // zero multipliers are not facts; cert.verify rejects them
        }
        let (fact, mag) = if j < n {
            let col = Col(j as u32);
            if coeff.is_positive() {
                (
                    FactRef::ColBound {
                        col,
                        side: BoundSide::Lower,
                    },
                    coeff.clone(),
                )
            } else {
                (
                    FactRef::ColBound {
                        col,
                        side: BoundSide::Upper,
                    },
                    -coeff.clone(),
                )
            }
        } else {
            let row = Row((j - n) as u32);
            // d_{n+r} = y_r. A positive row dual binds the row's LOWER side.
            if coeff.is_positive() {
                (
                    FactRef::RowBound {
                        row,
                        side: BoundSide::Lower,
                    },
                    coeff.clone(),
                )
            } else {
                (
                    FactRef::RowBound {
                        row,
                        side: BoundSide::Upper,
                    },
                    -coeff.clone(),
                )
            }
        };
        multipliers.push(Multiplier { fact, coeff: mag });
    }

    // --- The objective, back in the CALLER's sense. `lp.cost` is the minimize
    //     form, so a Maximize objective is the negation of what was asked for.
    //     Negating an f64 is exact, so this recovers the caller's coefficients
    //     bit for bit. ---
    let flip = matches!(lp.sense, Sense::Maximize);
    let user_coeff = |j: usize| -> f64 {
        if flip {
            -lp.cost[j]
        } else {
            lp.cost[j]
        }
    };
    let mut obj = BigRational::zero();
    for j in 0..n {
        let c = user_coeff(j);
        if c != 0.0 {
            obj += exact(c)? * &z[j];
        }
    }

    let cert = OptimalityCertificate {
        sense: lp.sense,
        objective: (0..n)
            .filter(|&j| user_coeff(j) != 0.0)
            .filter_map(|j| exact(user_coeff(j)).map(|c| (j as u32, c)))
            .collect(),
        bound: obj.clone(),
        multipliers,
    };

    // The certificate must convince the INDEPENDENT checker, not us. If the
    // identity does not close, the basis was not what we thought it was and the
    // caller takes the exact rim — the one outcome we never permit is shipping
    // an optimum whose evidence does not check out.
    cert.verify(model).ok()?;

    Some(CertifiedOptimum {
        values: z[..n].to_vec(),
        value: obj,
        cert,
    })
}

/// An exact LU factorization of a dense rational matrix, reusable across
/// right-hand sides.
///
/// [`solve_dense`] re-runs the whole elimination for every right-hand side, which
/// is O(m^3) EACH. Gomory separation needs one solve per cut row against the SAME
/// matrix, so paying the elimination once and back-solving per cut turns
/// O(cuts · m^3) into O(m^3 + cuts · m^2) — the difference between the cut loop
/// dominating the solve and being free.
/// The arithmetic runs on [`ay_lra::rational::Rational`] (inline `i64/i64`
/// with an exact arbitrary-precision fallback): Gomory bases are sparse and
/// their entries small, so the inline fast path carries almost every operation
/// that `BigRational` used to route through allocating gcd normalization.
/// Exact either way — same factors, same solutions. Exact-zero terms are
/// skipped (subtracting `f·0` is a no-op).
pub(crate) struct ExactLu {
    lu: Vec<Vec<ay_lra::rational::Rational>>,
    perm: Vec<usize>,
    n: usize,
}

/// Kill switch (shared with the GMI separator's fused arithmetic) for the
/// clone-elided form of the exact triangular solve. When `AY_MILP_NO_CUT_FMA`
/// is set the solve falls back to the literal `acc -= lu.clone() * &y` form for
/// an A/B byte-identity check. Cached once per process: the O(n²) solve must not
/// pay a syscall per term. `&lu * &y` runs the identical `Mul for &Rational` the
/// clone form did — same canonical value, minus a heap clone of a wide rational.
#[inline]
fn exact_lu_fma_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("AY_MILP_NO_CUT_FMA").is_none())
}

impl ExactLu {
    /// Factor `a` (consumed). `None` if singular — or if `deadline` passes
    /// mid-elimination. Rational elimination has no useful cost model up
    /// front: bit growth depends on the matrix, and a 468-row covering basis
    /// (domset mw19) was measured grinding 72s inside this loop while the
    /// caller's per-cut deadline checks sat OUTSIDE it, unable to fire. One
    /// check per pivot column is n checks total — noise against n³ rational
    /// ops.
    pub(crate) fn factor_with_deadline(
        mut a: Vec<Vec<ay_lra::rational::Rational>>,
        deadline: Option<std::time::Instant>,
    ) -> Option<Self> {
        let n = a.len();
        let fused = exact_lu_fma_enabled();
        let mut perm: Vec<usize> = (0..n).collect();
        for k in 0..n {
            if deadline.is_some_and(|d| std::time::Instant::now() >= d) {
                return None;
            }
            let piv = (k..n).find(|&i| !a[i][k].is_zero())?;
            if piv != k {
                a.swap(k, piv);
                perm.swap(k, piv);
            }
            for i in (k + 1)..n {
                if a[i][k].is_zero() {
                    continue;
                }
                let f = &a[i][k] / &a[k][k];
                for j in (k + 1)..n {
                    if a[k][j].is_zero() {
                        continue;
                    }
                    // `&f * &a[k][j]` is the same `Mul for &Rational`; the clone of the
                    // multiplier `f` (constant across this inner O(n) sweep) is pure waste.
                    let sub = if fused {
                        &f * &a[k][j]
                    } else {
                        f.clone() * &a[k][j]
                    };
                    a[i][j] -= sub;
                }
                a[i][k] = f; // store the multiplier: L below the diagonal
            }
        }
        Some(Self { lu: a, perm, n })
    }

    /// Solve `A z = b` using the stored factors.
    pub(crate) fn solve(
        &self,
        b: &[ay_lra::rational::Rational],
    ) -> Vec<ay_lra::rational::Rational> {
        use ay_lra::rational::Rational;
        let n = self.n;
        let fused = exact_lu_fma_enabled();
        let mut y = vec![Rational::zero(); n];
        for i in 0..n {
            let mut acc = b[self.perm[i]].clone();
            for j in 0..i {
                if !(self.lu[i][j].is_zero() || y[j].is_zero()) {
                    acc -= if fused {
                        &self.lu[i][j] * &y[j]
                    } else {
                        self.lu[i][j].clone() * &y[j]
                    };
                }
            }
            y[i] = acc;
        }
        let mut z = vec![Rational::zero(); n];
        for i in (0..n).rev() {
            let mut acc = y[i].clone();
            for j in (i + 1)..n {
                if !(self.lu[i][j].is_zero() || z[j].is_zero()) {
                    acc -= if fused {
                        &self.lu[i][j] * &z[j]
                    } else {
                        self.lu[i][j].clone() * &z[j]
                    };
                }
            }
            z[i] = &acc / &self.lu[i][i];
        }
        z
    }
}

#[cfg(test)]
mod solve_sparse_diff_tests {
    use super::{solve_dense, solve_sparse};
    use num_rational::BigRational;
    use num_traits::Zero;
    use std::collections::HashMap;

    fn rat(n: i64, d: i64) -> BigRational {
        BigRational::new(n.into(), d.into())
    }

    /// Deterministic LCG — the workflow forbids `Math.random`/`Date::now`, and a
    /// fixed seed makes any failure reproducible.
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            self.0 >> 16
        }
        fn range(&mut self, lo: i64, hi: i64) -> i64 {
            lo + (self.next() % ((hi - lo + 1) as u64)) as i64
        }
    }

    fn to_sparse(dense: &[Vec<BigRational>]) -> Vec<HashMap<usize, BigRational>> {
        dense
            .iter()
            .map(|row| {
                row.iter()
                    .enumerate()
                    .filter(|(_, v)| !v.is_zero())
                    .map(|(c, v)| (c, v.clone()))
                    .collect()
            })
            .collect()
    }

    /// `solve_sparse` must return the SAME exact solution as `solve_dense`, and that
    /// solution must have an exactly-zero residual against the original system.
    fn assert_agrees(dense: &[Vec<BigRational>], b: &[BigRational]) {
        let zd = solve_dense(dense.to_vec(), b.to_vec());
        let zs = solve_sparse(to_sparse(dense), b.to_vec(), None);
        assert_eq!(zd.is_some(), zs.is_some(), "solvability disagreement");
        if let (Some(zd), Some(zs)) = (zd, zs) {
            assert_eq!(zd, zs, "solution disagreement");
            for (i, row) in dense.iter().enumerate() {
                let mut acc = BigRational::zero();
                for (c, v) in row.iter().enumerate() {
                    acc += v * &zs[c];
                }
                assert_eq!(acc, b[i], "row {i} residual is nonzero");
            }
        }
    }

    #[test]
    fn matches_dense_on_random_dominant_systems() {
        let mut rng = Lcg(0x1234_5678_9abc_def0);
        for _ in 0..400 {
            let n = rng.range(1, 9) as usize;
            let mut a: Vec<Vec<BigRational>> = (0..n)
                .map(|_| {
                    (0..n)
                        .map(|_| rat(rng.range(-4, 4), rng.range(1, 4)))
                        .collect()
                })
                .collect();
            // Big diagonal => strictly diagonally dominant => nonsingular.
            for (i, row) in a.iter_mut().enumerate() {
                row[i] = rat(100 + rng.range(0, 9), 1);
            }
            let b: Vec<BigRational> = (0..n)
                .map(|_| rat(rng.range(-6, 6), rng.range(1, 3)))
                .collect();
            assert_agrees(&a, &b);
        }
    }

    #[test]
    fn matches_dense_on_column_permuted_triangular_systems() {
        // The case that broke the fixed-order pivoter: a triangular DAG whose natural
        // index order is NOT the elimination order. Row-permute a lower-triangular
        // matrix so pivots must be chosen by structure, not index.
        let mut rng = Lcg(0x0bad_c0de_dead_beef);
        for _ in 0..400 {
            let n = rng.range(2, 14) as usize;
            let mut a: Vec<Vec<BigRational>> = vec![vec![BigRational::zero(); n]; n];
            for i in 0..n {
                a[i][i] = rat(rng.range(1, 6), 1); // nonzero diagonal
                for j in 0..i {
                    if rng.range(0, 2) == 0 {
                        a[i][j] = rat(rng.range(-3, 3), 1);
                    }
                }
            }
            for i in (1..n).rev() {
                let j = rng.range(0, i as i64) as usize;
                a.swap(i, j);
            }
            let b: Vec<BigRational> = (0..n).map(|_| rat(rng.range(-5, 5), 1)).collect();
            assert_agrees(&a, &b);
        }
    }

    #[test]
    fn inconsistent_singular_declines() {
        let dense = vec![vec![rat(1, 1), rat(2, 1)], vec![rat(2, 1), rat(4, 1)]];
        let b = vec![rat(1, 1), rat(3, 1)]; // 2*(row0) != row1's rhs
        assert!(solve_sparse(to_sparse(&dense), b, None).is_none());
    }
}
