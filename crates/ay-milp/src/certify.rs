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

use ay_lra::rational::Rational as FastRational;
use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive, Zero};

use crate::cert::{BoundSide, CertifiedRow, FactRef, Multiplier, OptimalityCertificate};
use crate::model::{exact, exact_small, Col, Model, Row, Sense};
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

/// Turn an arbitrary finite float row-dual vector into an exact, independently
/// checked weak-duality row for the minimize-form objective `q`.
///
/// No optimality, feasibility, or sign property of `row_duals` is trusted.
/// Each finite component is first snapped to an exact `2^-30` dyadic (the
/// established [`crate::bab`] weak-bound grid), and
///
/// ```text
/// d = q - Aᵀy
/// beta = Σ_r y_r b_r + Σ_j d_j B_j
/// ```
///
/// is recomputed over the model's TRUE rational matrix/row-bound side-store.
/// A positive coefficient selects a lower bound and a negative coefficient an
/// upper bound. A row-dual component whose selected row side is infinite is
/// safely replaced by zero (any `y` is legal for weak duality); a structural
/// residual whose selected column side is infinite makes this particular
/// proposal unusable. The resulting positive fact multipliers must convince
/// [`CertifiedRow::verify`] before the row can leave this function.
///
/// Thus bad, stale, sign-reversed, or merely inaccurate float duals can only
/// weaken the returned bound or make this function decline. They cannot mint
/// an invalid inequality. `deadline` is advisory work control: expiry declines
/// rather than returning a partially constructed proof.
pub(crate) fn certified_weak_dual_row(
    model: &Model,
    q: &[f64],
    row_duals: &[f64],
    deadline: Option<std::time::Instant>,
) -> Option<CertifiedRow> {
    let row = weak_dual_row_proposal(model, q, row_duals, deadline)?;
    // This is the authority. The construction is only a proposal; the public
    // certificate checker independently recombines true model facts.
    row.verify(model).ok()?;
    (!deadline.is_some_and(|limit| std::time::Instant::now() >= limit)).then_some(row)
}

/// Build the weak-duality proposal without independently recombining it.
///
/// Keeping construction separate from verification lets the ignored
/// performance characterization time the two exact-arithmetic phases
/// independently. All production callers still go through
/// [`certified_weak_dual_row`] and therefore cannot bypass verification.
fn weak_dual_row_proposal(
    model: &Model,
    q: &[f64],
    row_duals: &[f64],
    deadline: Option<std::time::Instant>,
) -> Option<CertifiedRow> {
    const ROW_DEADLINE_STRIDE: usize = 64;
    const NNZ_DEADLINE_STRIDE: usize = 1024;
    const COL_DEADLINE_STRIDE: usize = 256;

    let expired = || deadline.is_some_and(|limit| std::time::Instant::now() >= limit);
    let n = model.num_cols();
    let m = model.num_rows();
    if q.len() != n
        || row_duals.len() != m
        || q.iter().chain(row_duals).any(|v| !v.is_finite())
        || expired()
    {
        return None;
    }

    // Dense and canonical: every residual sign decision below is exact, with
    // no epsilon dropping and no duplicate-column ambiguity.
    let objective: Option<Vec<FastRational>> = q.iter().map(|&v| exact_small(v)).collect();
    let objective = objective?;
    let mut residual = objective.clone();
    let mut beta = FastRational::zero();
    let mut multipliers = Vec::with_capacity(m + n);
    let mut visited_nnz = 0usize;
    // Weak duality is valid for ANY y, so retaining all 53 bits of a noisy
    // float dual is needless and expensive: tiny values can carry 2^110
    // denominators into every later gcd. This is intentionally the same grid
    // and overflow guard as `bab::exact_bound`.
    const DUAL_GRID: i64 = 1 << 30;
    let snap_dual = |v: f64| -> Option<FastRational> {
        let scaled = (v * DUAL_GRID as f64).round();
        if !scaled.is_finite() || scaled.abs() > 9.0e18 {
            return None;
        }
        Some(FastRational::new(scaled as i64, DUAL_GRID))
    };

    for r in 0..m {
        if r % ROW_DEADLINE_STRIDE == 0 && expired() {
            return None;
        }
        let (coeffs, lb, ub) = model.row(Row(r as u32));
        let y = snap_dual(row_duals[r])?;
        if y.is_zero() {
            continue;
        }

        // An unavailable side does not poison the whole proposal: replacing
        // just this arbitrary dual component by exact zero remains a valid
        // weak-duality choice and may still leave a useful certified row.
        let (fact, selected_bound, magnitude) = if y.is_positive() {
            let Some(bound) = model.row_lb_exact_small(r, lb) else {
                continue;
            };
            (
                FactRef::RowBound {
                    row: Row(r as u32),
                    side: BoundSide::Lower,
                },
                bound,
                y.to_big(),
            )
        } else {
            let Some(bound) = model.row_ub_exact_small(r, ub) else {
                continue;
            };
            (
                FactRef::RowBound {
                    row: Row(r as u32),
                    side: BoundSide::Upper,
                },
                bound,
                (-&y).to_big(),
            )
        };

        beta.mul_add_assign(&y, &selected_bound);
        multipliers.push(Multiplier {
            fact,
            coeff: magnitude,
        });
        let neg_y = -&y;
        for &(c, a) in coeffs {
            visited_nnz += 1;
            if visited_nnz.is_multiple_of(NNZ_DEADLINE_STRIDE) && expired() {
                return None;
            }
            let a = model.row_coeff_exact_small(r, c, a);
            residual[c as usize].mul_add_assign(&a, &neg_y);
        }
    }

    for (j, d) in residual.iter().enumerate() {
        if j % COL_DEADLINE_STRIDE == 0 && expired() {
            return None;
        }
        if d.is_zero() {
            continue;
        }
        let col = Col(j as u32);
        let (lb, ub) = model.col_bounds(col);
        let (fact, selected_bound, magnitude) = if d.is_positive() {
            (
                FactRef::ColBound {
                    col,
                    side: BoundSide::Lower,
                },
                exact_small(lb)?,
                d.to_big(),
            )
        } else {
            (
                FactRef::ColBound {
                    col,
                    side: BoundSide::Upper,
                },
                exact_small(ub)?,
                (-d).to_big(),
            )
        };
        beta.mul_add_assign(d, &selected_bound);
        multipliers.push(Multiplier {
            fact,
            coeff: magnitude,
        });
    }

    if expired() {
        return None;
    }
    let cert = OptimalityCertificate {
        sense: Sense::Minimize,
        objective: objective
            .into_iter()
            .enumerate()
            .filter(|(_, coeff)| !coeff.is_zero())
            .map(|(j, coeff)| (j as u32, coeff.to_big()))
            .collect(),
        bound: beta.to_big(),
        multipliers,
    };
    Some(cert.into_certified_row())
}

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
mod weak_dual_row_tests {
    use super::*;
    use crate::cert::tests::{combine_bounded_big_reference, combine_bounded_fast_for_benchmark};
    use num_bigint::BigInt;
    use num_traits::One;
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    use std::time::Duration;

    fn rat(n: i64, d: i64) -> BigRational {
        BigRational::new(n.into(), d.into())
    }

    /// The pre-fast-path implementation, retained only as a differential
    /// oracle. It deliberately performs every accumulation with
    /// `BigRational`; production uses `FastRational` and must return the exact
    /// same proof object or decline for the same mathematical reason.
    fn certified_weak_dual_row_big_reference(
        model: &Model,
        q: &[f64],
        row_duals: &[f64],
        deadline: Option<std::time::Instant>,
    ) -> Option<CertifiedRow> {
        let row = certified_weak_dual_row_big_reference_proposal(model, q, row_duals, deadline)?;
        row.verify(model).ok()?;
        (!deadline.is_some_and(|limit| std::time::Instant::now() >= limit)).then_some(row)
    }

    fn certified_weak_dual_row_big_reference_proposal(
        model: &Model,
        q: &[f64],
        row_duals: &[f64],
        deadline: Option<std::time::Instant>,
    ) -> Option<CertifiedRow> {
        const ROW_DEADLINE_STRIDE: usize = 64;
        const NNZ_DEADLINE_STRIDE: usize = 1024;
        const COL_DEADLINE_STRIDE: usize = 256;

        let expired = || deadline.is_some_and(|limit| std::time::Instant::now() >= limit);
        let n = model.num_cols();
        let m = model.num_rows();
        if q.len() != n
            || row_duals.len() != m
            || q.iter().chain(row_duals).any(|v| !v.is_finite())
            || expired()
        {
            return None;
        }

        let objective: Option<Vec<BigRational>> = q.iter().map(|&v| exact(v)).collect();
        let objective = objective?;
        let mut residual = objective.clone();
        let mut beta = BigRational::zero();
        let mut multipliers = Vec::with_capacity(m + n);
        let mut visited_nnz = 0usize;
        const DUAL_GRID: i64 = 1 << 30;
        let snap_dual = |v: f64| -> Option<BigRational> {
            let scaled = (v * DUAL_GRID as f64).round();
            if !scaled.is_finite() || scaled.abs() > 9.0e18 {
                return None;
            }
            Some(BigRational::new((scaled as i64).into(), DUAL_GRID.into()))
        };

        for r in 0..m {
            if r % ROW_DEADLINE_STRIDE == 0 && expired() {
                return None;
            }
            let (coeffs, lb, ub) = model.row(Row(r as u32));
            let y = snap_dual(row_duals[r])?;
            if y.is_zero() {
                continue;
            }
            let (fact, selected_bound, magnitude) = if y.is_positive() {
                let Some(bound) = model.row_lb_exact(r, lb) else {
                    continue;
                };
                (
                    FactRef::RowBound {
                        row: Row(r as u32),
                        side: BoundSide::Lower,
                    },
                    bound,
                    y.clone(),
                )
            } else {
                let Some(bound) = model.row_ub_exact(r, ub) else {
                    continue;
                };
                (
                    FactRef::RowBound {
                        row: Row(r as u32),
                        side: BoundSide::Upper,
                    },
                    bound,
                    -y.clone(),
                )
            };

            beta += &y * selected_bound;
            multipliers.push(Multiplier {
                fact,
                coeff: magnitude,
            });
            for &(c, a) in coeffs {
                visited_nnz += 1;
                if visited_nnz.is_multiple_of(NNZ_DEADLINE_STRIDE) && expired() {
                    return None;
                }
                residual[c as usize] -= model.row_coeff_exact(r, c, a) * &y;
            }
        }

        for (j, d) in residual.iter().enumerate() {
            if j % COL_DEADLINE_STRIDE == 0 && expired() {
                return None;
            }
            if d.is_zero() {
                continue;
            }
            let col = Col(j as u32);
            let (lb, ub) = model.col_bounds(col);
            let (fact, selected_bound, magnitude) = if d.is_positive() {
                (
                    FactRef::ColBound {
                        col,
                        side: BoundSide::Lower,
                    },
                    exact(lb)?,
                    d.clone(),
                )
            } else {
                (
                    FactRef::ColBound {
                        col,
                        side: BoundSide::Upper,
                    },
                    exact(ub)?,
                    -d.clone(),
                )
            };
            beta += d * selected_bound;
            multipliers.push(Multiplier {
                fact,
                coeff: magnitude,
            });
        }

        if expired() {
            return None;
        }
        Some(
            OptimalityCertificate {
                sense: Sense::Minimize,
                objective: objective
                    .into_iter()
                    .enumerate()
                    .filter(|(_, coeff)| !coeff.is_zero())
                    .map(|(j, coeff)| (j as u32, coeff))
                    .collect(),
                bound: beta,
                multipliers,
            }
            .into_certified_row(),
        )
    }

    fn assert_matches_big_reference(model: &Model, q: &[f64], row_duals: &[f64]) -> CertifiedRow {
        let fast = certified_weak_dual_row(model, q, row_duals, None);
        let reference = certified_weak_dual_row_big_reference(model, q, row_duals, None);
        assert_eq!(fast, reference, "inline and BigRational builders diverged");
        fast.expect("finite boxed differential case must construct")
    }

    #[test]
    fn exact_row_dual_proves_fractional_equality_bound() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 10.0);
        model.add_row(3.0, 3.0, &[(x, 2.0)]);

        let row = assert_matches_big_reference(&model, &[1.0], &[0.5]);
        row.verify(&model).expect("proof must independently verify");
        assert_eq!(row.coeffs, vec![(x.0, BigRational::one())]);
        assert_eq!(row.lb, rat(3, 2));

        let mut tampered = row;
        tampered.lb += BigRational::one();
        assert!(
            tampered.verify(&model).is_err(),
            "changing the proved bound must invalidate the exact identity"
        );
    }

    #[test]
    fn unavailable_row_side_is_zeroed_without_weakening_soundness() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        model.add_row(f64::NEG_INFINITY, 0.5, &[(x, 1.0)]);

        // Positive y asks for the absent lower row side. The constructor is
        // allowed to replace arbitrary y by zero, leaving the valid box proof
        // x >= 0.
        let row = certified_weak_dual_row(&model, &[1.0], &[4.0], None)
            .expect("bounded structural residual still proves a row");
        row.verify(&model).unwrap();
        assert_eq!(row.lb, BigRational::zero());
    }

    #[test]
    fn infinity_nonfinite_and_expired_inputs_decline() {
        let mut free_model = Model::new();
        free_model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        assert!(
            certified_weak_dual_row(&free_model, &[1.0], &[], None).is_none(),
            "positive residual cannot cite a missing structural lower bound"
        );

        let mut model = Model::new();
        let x = model.add_col(-1.0, 1.0);
        model.add_row(0.0, 0.0, &[(x, 1.0)]);
        assert!(certified_weak_dual_row(&model, &[f64::NAN], &[0.0], None).is_none());
        assert!(certified_weak_dual_row(&model, &[1.0], &[f64::INFINITY], None).is_none());
        assert!(
            certified_weak_dual_row(&model, &[1.0], &[f64::MAX], None).is_none(),
            "a finite but unsnappable corrupted dual must fail closed"
        );
        assert!(
            certified_weak_dual_row(&model, &[1.0], &[0.0], Some(std::time::Instant::now()))
                .is_none()
        );
        assert!(
            certified_weak_dual_row_big_reference(
                &model,
                &[1.0],
                &[0.0],
                Some(std::time::Instant::now())
            )
            .is_none(),
            "the fast path preserves the reference deadline decline"
        );
    }

    #[test]
    fn maximize_lower_form_reorients_exactly() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 2.0);
        // max x is represented by q=-x. The lower-form row -x >= -2 is
        // exactly the public upper bound x <= 2.
        let row = certified_weak_dual_row(&model, &[-1.0], &[], None).unwrap();
        row.verify(&model).unwrap();
        assert_eq!(row.coeffs, vec![(x.0, -BigRational::one())]);
        assert_eq!(row.lb, rat(-2, 1));
    }

    #[test]
    fn uses_true_rational_side_store_not_float_proxies() {
        let mut model = Model::new();
        let x = model.add_col(-10.0, 10.0);
        let row_handle = model.add_row(2.0 / 3.0, 2.0 / 3.0, &[(x, 1.0 / 3.0)]);
        model.record_inexact_row_coeff(row_handle, x.0, rat(1, 3));
        model.record_inexact_row_bound(row_handle, true, rat(2, 3));
        model.record_inexact_row_bound(row_handle, false, rat(2, 3));

        // Over the TRUE row (1/3)x = 2/3, y=3 has zero residual and proves
        // x >= 2. Replaying rounded proxies would not close this identity.
        let row = assert_matches_big_reference(&model, &[1.0], &[3.0]);
        row.verify(&model).unwrap();
        assert_eq!(row.coeffs, vec![(x.0, BigRational::one())]);
        assert_eq!(row.lb, rat(2, 1));
    }

    #[test]
    fn promotion_extremes_and_large_side_store_match_big_reference() {
        let mut dyadic = Model::new();
        let cols: Vec<Col> = (0..4).map(|_| dyadic.add_col(-1.0, 1.0)).collect();
        let coeffs = [
            f64::from_bits(1),
            f64::MIN_POSITIVE,
            f64::MAX,
            -f64::from_bits((1022_u64 << 52) | 1),
        ];
        for (&col, &coeff) in cols.iter().zip(&coeffs) {
            dyadic.add_row(0.0, 0.0, &[(col, coeff)]);
        }
        let row = assert_matches_big_reference(
            &dyadic,
            &[1.0, -1.0, f64::MIN_POSITIVE, f64::from_bits(1)],
            &[1.0, -0.5, 0.75, -1.25],
        );
        row.verify(&dyadic).unwrap();

        let mut side_store = Model::new();
        let x = side_store.add_col(-3.0, 5.0);
        let proxy = side_store.add_row(2.0, 2.0, &[(x, 1.0)]);
        let numerator = (BigInt::from(1_u8) << 180) + BigInt::from(17_u8);
        let denominator = (BigInt::from(1_u8) << 100) + BigInt::from(3_u8);
        let exact_coeff = BigRational::new(numerator, denominator);
        let exact_bound = &exact_coeff + &exact_coeff;
        side_store.record_inexact_row_coeff(proxy, x.0, exact_coeff.clone());
        side_store.record_inexact_row_bound(proxy, true, exact_bound.clone());
        side_store.record_inexact_row_bound(proxy, false, exact_bound);

        let row = assert_matches_big_reference(&side_store, &[0.0], &[1.0]);
        row.verify(&side_store).unwrap();
        assert_eq!(row.lb, -(&exact_coeff + &exact_coeff + exact_coeff));
    }

    fn sealed_mix(mut value: u64) -> u64 {
        value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
        value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        value ^ (value >> 31)
    }

    fn timed<T>(f: impl FnOnce() -> T) -> (Duration, T) {
        let start = std::time::Instant::now();
        let value = f();
        (start.elapsed(), value)
    }

    fn median(mut samples: Vec<Duration>) -> Duration {
        samples.sort_unstable();
        samples[samples.len() / 2]
    }

    fn certified_row_hash(row: &CertifiedRow) -> u64 {
        let mut hasher = DefaultHasher::new();
        row.coeffs.hash(&mut hasher);
        row.lb.hash(&mut hasher);
        row.multipliers.len().hash(&mut hasher);
        for multiplier in &row.multipliers {
            multiplier.fact.hash(&mut hasher);
            multiplier.coeff.hash(&mut hasher);
        }
        hasher.finish()
    }

    fn combination_hash(coeffs: &[BigRational], constant: &BigRational) -> u64 {
        let mut hasher = DefaultHasher::new();
        coeffs.hash(&mut hasher);
        constant.hash(&mut hasher);
        hasher.finish()
    }

    /// One-process characterization at the sealed VNN-COMP instance's exact
    /// sparse dimensions. This deliberately excludes model construction and
    /// solver setup: both implementations see the same warm, immutable model,
    /// objective, snapped duals, multiplier list, and rational side-store.
    ///
    /// The shape is representative, but the synthetic adjacency, coefficient
    /// distribution, and one-hot objective are not a replay of the confidential
    /// network. Alternating order and medians reduce (but cannot eliminate)
    /// shared-host frequency and scheduling noise.
    #[test]
    #[ignore = "sealed-scale exact-arithmetic performance characterization"]
    fn sealed_scale_rational_weak_row_benchmark() {
        const NUM_COLS: usize = 7_593;
        const NUM_ROWS: usize = 4_846;
        const NUM_NNZ: usize = 502_260;
        const EXTRA_NNZ_ROWS: usize = NUM_NNZ - NUM_ROWS * 103;
        const SIDE_STORE_COEFFS: usize = 8;
        const SIDE_STORE_BOUNDS: usize = 8;
        const ROUNDS: usize = 5;

        let mut model = Model::new();
        let cols: Vec<Col> = (0..NUM_COLS)
            .map(|j| {
                let lb = -7.0 - (j % 3) as f64;
                let ub = 11.0 + (j % 5) as f64;
                model.add_col(lb, ub)
            })
            .collect();
        let mut duals = Vec::with_capacity(NUM_ROWS);
        let mut actual_nnz = 0usize;

        for r in 0..NUM_ROWS {
            let degree = 103 + usize::from(r < EXTRA_NNZ_ROWS);
            let mut coeffs = Vec::with_capacity(degree);
            for k in 0..degree {
                // gcd(67, 7593) == 1, so every row is duplicate-free.
                let col = cols[(r * 131 + k * 67) % NUM_COLS];
                let bits = sealed_mix(((r as u64) << 32) | k as u64);
                let numerator = ((bits >> 8) % 2_047 + 1) as f64;
                let denominator = (1_u64 << (8 + (bits as u32 % 5))) as f64;
                let sign = if bits & 1 == 0 { 1.0 } else { -1.0 };
                coeffs.push((col, sign * numerator / denominator));
            }
            actual_nnz += coeffs.len();

            let row = model.add_row(-3.0, 4.0, &coeffs);
            if r < SIDE_STORE_BOUNDS {
                let exact_lb = if r == 0 {
                    let numerator = -((BigInt::from(1_u8) << 115_usize) + BigInt::from(17_u8));
                    let denominator = (BigInt::from(1_u8) << 75_usize) + BigInt::from(3_u8);
                    BigRational::new(numerator, denominator)
                } else {
                    rat(-((2 * r + 1) as i64), 3)
                };
                model.record_inexact_row_bound(row, true, exact_lb);
            }
            if (SIDE_STORE_BOUNDS..SIDE_STORE_BOUNDS + SIDE_STORE_COEFFS).contains(&r) {
                let exact_coeff = if r == SIDE_STORE_BOUNDS {
                    let numerator = (BigInt::from(1_u8) << 113_usize) + BigInt::from(29_u8);
                    let denominator = (BigInt::from(1_u8) << 73_usize) + BigInt::from(5_u8);
                    BigRational::new(numerator, denominator)
                } else {
                    rat((2 * r + 1) as i64, 3)
                };
                let overridden_col = coeffs[0].0;
                model.record_inexact_row_coeff(row, overridden_col.0, exact_coeff);
            }

            let bits = sealed_mix(0xd1b5_4a32_d192_ed03 ^ r as u64);
            let numerator = ((bits >> 12) % ((1_u64 << 29) - 1) + 1) as f64;
            let sign = if r < SIDE_STORE_BOUNDS + SIDE_STORE_COEFFS || bits & 1 == 0 {
                1.0
            } else {
                -1.0
            };
            duals.push(sign * numerator / (1_u64 << 30) as f64);
        }
        assert_eq!(actual_nnz, NUM_NNZ);

        let mut q = vec![0.0; NUM_COLS];
        q[NUM_COLS - 1] = 1.0;

        // Untimed warm-up also establishes the shared proof and Combination
        // input before collecting any samples.
        let fast_warm =
            weak_dual_row_proposal(&model, &q, &duals, None).expect("finite box must build");
        let big_warm = certified_weak_dual_row_big_reference_proposal(&model, &q, &duals, None)
            .expect("BigRational oracle must build");
        assert_eq!(fast_warm, big_warm);
        fast_warm
            .verify(&model)
            .expect("warm proposal must independently verify");
        let multipliers = fast_warm.multipliers.clone();

        combine_bounded_big_reference(&multipliers, &model, None)
            .expect("BigRational Combination warm-up must succeed");
        let (fast_coeffs, fast_constant) =
            combine_bounded_fast_for_benchmark(&multipliers, &model, None)
                .expect("production Combination must succeed");
        let (big_coeffs, big_constant) = combine_bounded_big_reference(&multipliers, &model, None)
            .expect("BigRational Combination oracle must succeed");
        assert_eq!(
            fast_coeffs
                .iter()
                .map(FastRational::to_big)
                .collect::<Vec<_>>(),
            big_coeffs
        );
        assert_eq!(fast_constant.to_big(), big_constant);
        let expected_row_hash = certified_row_hash(&fast_warm);
        let expected_combination_hash = combination_hash(&big_coeffs, &big_constant);

        let mut builder_fast = Vec::with_capacity(ROUNDS);
        let mut builder_big = Vec::with_capacity(ROUNDS);
        let mut combination_fast = Vec::with_capacity(ROUNDS);
        let mut combination_big = Vec::with_capacity(ROUNDS);
        let mut final_big_slots = None;

        for round in 0..ROUNDS {
            let (fast_time, fast_row, big_time, big_row) = if round % 2 == 0 {
                let (fast_time, fast_row) = timed(|| {
                    weak_dual_row_proposal(&model, &q, &duals, None)
                        .expect("production proposal must build")
                });
                let (big_time, big_row) = timed(|| {
                    certified_weak_dual_row_big_reference_proposal(&model, &q, &duals, None)
                        .expect("BigRational proposal must build")
                });
                (fast_time, fast_row, big_time, big_row)
            } else {
                let (big_time, big_row) = timed(|| {
                    certified_weak_dual_row_big_reference_proposal(&model, &q, &duals, None)
                        .expect("BigRational proposal must build")
                });
                let (fast_time, fast_row) = timed(|| {
                    weak_dual_row_proposal(&model, &q, &duals, None)
                        .expect("production proposal must build")
                });
                (fast_time, fast_row, big_time, big_row)
            };
            assert_eq!(fast_row, big_row);
            assert_eq!(certified_row_hash(&fast_row), expected_row_hash);
            assert_eq!(certified_row_hash(&big_row), expected_row_hash);
            builder_fast.push(fast_time);
            builder_big.push(big_time);
            drop(fast_row);
            drop(big_row);

            let (fast_time, fast_combination, big_time, big_combination) = if round % 2 == 0 {
                let (fast_time, fast_combination) = timed(|| {
                    combine_bounded_fast_for_benchmark(&multipliers, &model, None)
                        .expect("production Combination must succeed")
                });
                let (big_time, big_combination) = timed(|| {
                    combine_bounded_big_reference(&multipliers, &model, None)
                        .expect("BigRational Combination oracle must succeed")
                });
                (fast_time, fast_combination, big_time, big_combination)
            } else {
                let (big_time, big_combination) = timed(|| {
                    combine_bounded_big_reference(&multipliers, &model, None)
                        .expect("BigRational Combination oracle must succeed")
                });
                let (fast_time, fast_combination) = timed(|| {
                    combine_bounded_fast_for_benchmark(&multipliers, &model, None)
                        .expect("production Combination must succeed")
                });
                (fast_time, fast_combination, big_time, big_combination)
            };

            // Conversion and final storage-state inspection are deliberately
            // outside the Combination timer.
            let (fast_coeffs, fast_constant) = fast_combination;
            let round_big_slots = fast_coeffs.iter().filter(|value| !value.is_small()).count()
                + usize::from(!fast_constant.is_small());
            assert_eq!(
                *final_big_slots.get_or_insert(round_big_slots),
                round_big_slots
            );
            let fast_big_coeffs = fast_coeffs
                .iter()
                .map(FastRational::to_big)
                .collect::<Vec<_>>();
            let fast_big_constant = fast_constant.to_big();
            let (big_coeffs, big_constant) = big_combination;
            assert_eq!(fast_big_coeffs, big_coeffs);
            assert_eq!(fast_big_constant, big_constant);
            assert_eq!(
                combination_hash(&fast_big_coeffs, &fast_big_constant),
                expected_combination_hash
            );
            assert_eq!(
                combination_hash(&big_coeffs, &big_constant),
                expected_combination_hash
            );
            combination_fast.push(fast_time);
            combination_big.push(big_time);
        }

        let combined_fast = builder_fast
            .iter()
            .zip(&combination_fast)
            .map(|(builder, combination)| *builder + *combination)
            .collect::<Vec<_>>();
        let combined_big = builder_big
            .iter()
            .zip(&combination_big)
            .map(|(builder, combination)| *builder + *combination)
            .collect::<Vec<_>>();
        let builder_fast_median = median(builder_fast);
        let builder_big_median = median(builder_big);
        let combination_fast_median = median(combination_fast);
        let combination_big_median = median(combination_big);
        let combined_fast_median = median(combined_fast);
        let combined_big_median = median(combined_big);
        let millis = |duration: Duration| duration.as_secs_f64() * 1_000.0;
        let speedup = |old: Duration, new: Duration| old.as_secs_f64() / new.as_secs_f64();

        println!(
            "sealed_scale_rational_weak_row_benchmark \
             cols={NUM_COLS} rows={NUM_ROWS} nnz={NUM_NNZ} rounds={ROUNDS} \
             objective_nnz=1 multipliers={} side_store_entries={} forced_big_inputs=2 \
             builder_fast_median_ms={:.3} builder_big_median_ms={:.3} \
             builder_speedup={:.3}x \
             combination_fast_median_ms={:.3} combination_big_median_ms={:.3} \
             combination_speedup={:.3}x \
             combined_fast_median_ms={:.3} combined_big_median_ms={:.3} \
             combined_speedup={:.3}x final_big_slots={} \
             row_hash={expected_row_hash:016x} combination_hash={expected_combination_hash:016x}",
            multipliers.len(),
            SIDE_STORE_COEFFS + SIDE_STORE_BOUNDS,
            millis(builder_fast_median),
            millis(builder_big_median),
            speedup(builder_big_median, builder_fast_median),
            millis(combination_fast_median),
            millis(combination_big_median),
            speedup(combination_big_median, combination_fast_median),
            millis(combined_fast_median),
            millis(combined_big_median),
            speedup(combined_big_median, combined_fast_median),
            final_big_slots.expect("at least one round"),
        );
    }

    /// Deterministic LCG: arbitrary and often wrong-signed dual advice must
    /// still either decline or emit a row accepted by the independent checker.
    struct Lcg(u64);
    impl Lcg {
        fn next(&mut self) -> u64 {
            self.0 = self
                .0
                .wrapping_mul(6_364_136_223_846_793_005)
                .wrapping_add(1_442_695_040_888_963_407);
            self.0
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }

        fn int(&mut self, lo: i64, hi: i64) -> i64 {
            lo + self.below((hi - lo + 1) as u64) as i64
        }
    }

    #[test]
    fn random_adversarial_duals_always_verify() {
        let mut rng = Lcg(0x6a09_e667_f3bc_c909);
        for case in 0..200 {
            let n = (rng.below(6) + 1) as usize;
            let m = rng.below(9) as usize;
            let mut model = Model::new();
            let cols: Vec<Col> = (0..n).map(|_| model.add_col(-5.0, 5.0)).collect();
            for _ in 0..m {
                let mut coeffs = Vec::new();
                for &col in &cols {
                    let a = rng.int(-3, 3);
                    if a != 0 {
                        coeffs.push((col, a as f64));
                    }
                }
                if coeffs.is_empty() {
                    coeffs.push((cols[rng.below(n as u64) as usize], 1.0));
                }
                let base = rng.int(-4, 4) as f64;
                let (lb, ub) = match rng.below(4) {
                    0 => (base, base),
                    1 => (base, base + (rng.below(4) + 1) as f64),
                    2 => (base, f64::INFINITY),
                    _ => (f64::NEG_INFINITY, base),
                };
                model.add_row(lb, ub, &coeffs);
            }
            let q: Vec<f64> = (0..n).map(|_| rng.int(-3, 3) as f64).collect();
            let y: Vec<f64> = (0..m).map(|_| rng.int(-16, 16) as f64 / 4.0).collect();
            let row = assert_matches_big_reference(&model, &q, &y);
            row.verify(&model)
                .unwrap_or_else(|err| panic!("case {case} failed verification: {err}"));
            let expected: Vec<(u32, BigRational)> = q
                .iter()
                .enumerate()
                .filter(|(_, a)| **a != 0.0)
                .map(|(j, &a)| (j as u32, exact(a).unwrap()))
                .collect();
            assert_eq!(row.coeffs, expected, "case {case} objective drift");
        }
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
