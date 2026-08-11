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

// Measurement scaffold and BigRational differential oracle for the two
// exact-arithmetic phases below; see the module doc.
pub(crate) mod sealed_scale;

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
    deadline
        .is_none_or(|limit| std::time::Instant::now() < limit)
        .then_some(row)
}

/// Build the weak-duality proposal without independently recombining it.
///
/// Keeping construction separate from verification lets the [`sealed_scale`]
/// characterization — run on demand through the
/// `sealed_scale_rational_weak_row` example — time the two exact-arithmetic
/// phases independently. All production callers still go through
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

/// The pre-fast-path builder, retained only as a differential oracle. It
/// deliberately performs every accumulation with `BigRational`; production uses
/// `FastRational` and must return the exact same proof object or decline for the
/// same mathematical reason.
///
/// Like [`weak_dual_row_proposal`] this hands back a proposal that has NOT been
/// independently recombined, so it stays `pub(crate)`: its only callers are the
/// `#[cfg(test)]` verifying wrapper and the [`sealed_scale`] characterization,
/// both of which verify or compare before trusting anything.
pub(crate) fn certified_weak_dual_row_big_reference_proposal(
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

/// Unbudgeted exact dense solve. TEST-ONLY: every shipping caller must pass a
/// deadline through [`solve_dense_by`], for the reason documented there.
#[cfg(test)]
pub(crate) fn solve_dense(
    a: Vec<Vec<BigRational>>,
    b: Vec<BigRational>,
) -> Option<Vec<BigRational>> {
    solve_dense_by(a, b, None)
}

/// Exact dense Gaussian elimination, with a deadline polled throughout
/// elimination and back-substitution.
///
/// # Why this needed a deadline at all
///
/// This is exact dense Gaussian elimination over `BigRational` on a basis of up
/// to [`MAX_EXACT_BASIS_ROWS`] rows, and the numerators grow as it runs, so its
/// cost is not bounded by anything the caller can see from the row count. It
/// had no interruption point of any kind, which made it an ATOMIC unit of work
/// LARGER THAN A WHOLE SOLVE.
///
/// MEASURED, release binary, `control30-3-2-3` (510 rows after presolve),
/// `--time-limit 3`, three serial runs:
///
/// ```text
///   default routing               UNKNOWN Timeout @ 15.9 s   ZERO nodes searched
///   AY_MILP_NO_STRUCTURE_ROUTE=1  FEASIBLE 5.9594  @  2.8 s   141 nodes
/// ```
///
/// A 5.3x overrun of the caller's own deadline, with branch-and-bound never
/// entered. `sample(1)` put 100% of the process here: `hybrid_pb_lp::try_solve_certified`
/// -> `certify_bounded_by` -> `solve_dense`. The lane was passed a correct 600 ms
/// slice and simply could not observe it.
///
/// A deadline that a lane cannot poll is not a budget, it is a wish. Polling at
/// bounded loop intervals keeps every large pass interruptible, and a `None`
/// return is already the "no certificate" path every caller handles.
pub(crate) fn solve_dense_by(
    mut a: Vec<Vec<BigRational>>,
    mut b: Vec<BigRational>,
    deadline: Option<std::time::Instant>,
) -> Option<Vec<BigRational>> {
    let n = b.len();
    debug_assert!(a.len() == n && a.iter().all(|r| r.len() == n));
    for k in 0..n {
        if deadline.is_some_and(|limit| std::time::Instant::now() >= limit) {
            return None;
        }
        let piv = (k..n).find(|&i| !a[i][k].is_zero())?;
        if piv != k {
            a.swap(k, piv);
            b.swap(k, piv);
        }
        // Eliminate below.
        for i in (k + 1)..n {
            if i & 0xf == 0 && deadline.is_some_and(|limit| std::time::Instant::now() >= limit) {
                return None;
            }
            if a[i][k].is_zero() {
                continue;
            }
            let f = &a[i][k] / &a[k][k];
            for j in k..n {
                if j & 0x3f == 0 && deadline.is_some_and(|limit| std::time::Instant::now() >= limit)
                {
                    return None;
                }
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
        if deadline.is_some_and(|limit| std::time::Instant::now() >= limit) {
            return None;
        }
        let mut acc = b[k].clone();
        for j in (k + 1)..n {
            if j & 0x3f == 0 && deadline.is_some_and(|limit| std::time::Instant::now() >= limit) {
                return None;
            }
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
/// A branch-and-bound leaf cannot use [`certify_bounded_by`]: that builds a
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
    certify_bounded_by(model, lp, cand, &lp.lower, &lp.upper, None)
}

/// As [`certify`], but every matrix construction/elimination pass shares one
/// absolute deadline. A miss is only a declined advice basis.
pub(crate) fn certify_with_deadline(
    model: &Model,
    lp: &FloatLp,
    cand: &Candidate,
    deadline: Option<std::time::Instant>,
) -> Option<CertifiedOptimum> {
    certify_bounded_by(model, lp, cand, &lp.lower, &lp.upper, deadline)
}

/// Adjudicate a float lane's combinatorial basis against `model`'s TRUE data.
///
/// Unlike [`certify_with_deadline`], this entry does not read any numeric data
/// back from [`FloatLp`].  `basis` and `at` are advice-only indices/statuses;
/// the matrix, row bounds, column bounds, objective, and objective sense are
/// reconstructed from [`Model`], including every authoritative exact-rational
/// side-store override.  This makes the adjudicator usable by any route that
/// lowers a model to a float LP but must not grant rounded proxy coefficients
/// proof authority.
///
/// The result is deliberately fail-closed.  A malformed or singular basis, an
/// exactly infeasible vertex, a wrong reduced-cost sign, an expired deadline,
/// or a final certificate that the independent checker rejects all return
/// `None`.  The objective value excludes the model's constant offset, matching
/// [`CertifiedOptimum`] and [`OptimalityCertificate`].
pub(crate) fn certify_model_basis_with_deadline(
    model: &Model,
    basis: &[usize],
    at: &[NbBound],
    deadline: Option<std::time::Instant>,
) -> Option<CertifiedOptimum> {
    const INDEX_DEADLINE_STRIDE: usize = 256;
    const ROW_DEADLINE_STRIDE: usize = 64;

    let expired = || deadline.is_some_and(|limit| std::time::Instant::now() >= limit);
    model.validate().ok()?;
    let n = model.num_cols();
    let m = model.num_rows();
    let cols = n.checked_add(m)?;
    if m > MAX_EXACT_BASIS_ROWS || basis.len() != m || at.len() != cols || expired() {
        return None;
    }

    // A basis is exactly one distinct computational column per model row.
    // Keep the reverse map so every later membership test is O(1).
    let mut basis_position = vec![None; cols];
    for (position, &column) in basis.iter().enumerate() {
        if position.is_multiple_of(INDEX_DEADLINE_STRIDE) && expired() {
            return None;
        }
        let slot = basis_position.get_mut(column)?;
        if slot.is_some() {
            return None;
        }
        *slot = Some(position);
    }

    // Exact bounds in computational-column order: structural columns first,
    // then one logical per row.  A logical carries the TRUE row bounds, not the
    // rounded `f64` proxies copied into FloatLp.
    let mut lower = Vec::with_capacity(cols);
    let mut upper = Vec::with_capacity(cols);
    for column in 0..n {
        if column.is_multiple_of(INDEX_DEADLINE_STRIDE) && expired() {
            return None;
        }
        let (lb, ub) = model.col_bounds(Col(column as u32));
        lower.push(exact(lb));
        upper.push(exact(ub));
    }
    for row in 0..m {
        if row.is_multiple_of(ROW_DEADLINE_STRIDE) && expired() {
            return None;
        }
        let (_, lb, ub) = model.row(Row(row as u32));
        lower.push(model.row_lb_exact(row, lb));
        upper.push(model.row_ub_exact(row, ub));
    }

    // Recover both the caller's objective and the minimize-form objective used
    // for reduced costs.  Objective side-store entries remain authoritative
    // even when their rounded advice coefficient is zero.
    let mut user_cost = Vec::with_capacity(n);
    for column in 0..n {
        if column.is_multiple_of(INDEX_DEADLINE_STRIDE) && expired() {
            return None;
        }
        let col = Col(column as u32);
        user_cost.push(model.obj_coeff_exact_at(column as u32, model.obj_coeff(col)));
    }
    let flip = matches!(model.sense(), Sense::Maximize);
    let mut minimize_cost = Vec::with_capacity(cols);
    minimize_cost.extend(user_cost.iter().map(|coefficient| {
        if flip {
            -coefficient
        } else {
            coefficient.clone()
        }
    }));
    minimize_cost.resize(cols, BigRational::zero());

    // Pin each nonbasic to the exact bound named by the float basis. `Zero` is
    // the free-column state, not a license to place a bounded column at an
    // arbitrary interior value.
    let mut z = vec![BigRational::zero(); cols];
    for column in 0..cols {
        if column.is_multiple_of(INDEX_DEADLINE_STRIDE) && expired() {
            return None;
        }
        if basis_position[column].is_some() {
            continue;
        }
        z[column] = match at[column] {
            NbBound::Lower => lower[column].clone()?,
            NbBound::Upper => upper[column].clone()?,
            NbBound::Zero if lower[column].is_none() && upper[column].is_none() => {
                BigRational::zero()
            }
            NbBound::Zero => return None,
        };
    }

    // Build B and `-N x_N` directly from the model's true matrix. The
    // computational matrix is M=[A|-I], so a nonbasic logical contributes its
    // value positively to the right-hand side.
    let mut bmat = vec![vec![BigRational::zero(); m]; m];
    let mut rhs = vec![BigRational::zero(); m];
    for row in 0..m {
        if row.is_multiple_of(ROW_DEADLINE_STRIDE) && expired() {
            return None;
        }
        let (coefficients, _, _) = model.row(Row(row as u32));
        for (entry, &(column, rounded)) in coefficients.iter().enumerate() {
            if entry.is_multiple_of(INDEX_DEADLINE_STRIDE) && expired() {
                return None;
            }
            let coefficient = model.row_coeff_exact(row, column, rounded);
            if let Some(position) = basis_position[column as usize] {
                bmat[row][position] = coefficient;
            } else if !z[column as usize].is_zero() {
                rhs[row] -= coefficient * &z[column as usize];
            }
        }
        let logical = n + row;
        if let Some(position) = basis_position[logical] {
            bmat[row][position] = -BigRational::from_integer(1.into());
        } else if !z[logical].is_zero() {
            rhs[row] += &z[logical];
        }
    }

    // Solve both exact basis systems.  The float solution/duals are not read:
    // only the combinatorial basis survives into this proof lane.
    let mut transpose = vec![vec![BigRational::zero(); m]; m];
    for row in 0..m {
        if row.is_multiple_of(ROW_DEADLINE_STRIDE) && expired() {
            return None;
        }
        for column in 0..m {
            transpose[column][row] = bmat[row][column].clone();
        }
    }
    let basic_cost: Vec<BigRational> = basis
        .iter()
        .map(|&column| minimize_cost[column].clone())
        .collect();
    let basic_values = solve_dense_by(bmat, rhs, deadline)?;
    let row_duals = solve_dense_by(transpose, basic_cost, deadline)?;
    for (position, &column) in basis.iter().enumerate() {
        z[column] = basic_values[position].clone();
    }

    // Check every computational bound, including the nonbasics. This catches
    // corrupted resting statuses as well as float-feasible/exact-infeasible
    // basic values.
    for column in 0..cols {
        if column.is_multiple_of(INDEX_DEADLINE_STRIDE) && expired() {
            return None;
        }
        if lower[column]
            .as_ref()
            .is_some_and(|bound| z[column] < *bound)
            || upper[column]
                .as_ref()
                .is_some_and(|bound| z[column] > *bound)
        {
            return None;
        }
    }

    // Independently recompute Mz and every reduced cost from the TRUE matrix.
    // Besides detecting a bad solve, `activity == logical` proves the returned
    // structural point satisfies every exact model row.
    let mut reduced = minimize_cost;
    for row in 0..m {
        if row.is_multiple_of(ROW_DEADLINE_STRIDE) && expired() {
            return None;
        }
        let (coefficients, _, _) = model.row(Row(row as u32));
        let mut activity = BigRational::zero();
        for (entry, &(column, rounded)) in coefficients.iter().enumerate() {
            if entry.is_multiple_of(INDEX_DEADLINE_STRIDE) && expired() {
                return None;
            }
            let coefficient = model.row_coeff_exact(row, column, rounded);
            if !z[column as usize].is_zero() {
                activity += &coefficient * &z[column as usize];
            }
            if !row_duals[row].is_zero() {
                reduced[column as usize] -= coefficient * &row_duals[row];
            }
        }
        if activity != z[n + row] {
            return None;
        }
        // c_logical=0 and M_logical=-e_r, hence d_logical=y_r.
        reduced[n + row] += &row_duals[row];
    }

    // A true basis has exactly-zero basic reduced costs.  Nonbasic signs are
    // the exact textbook optimality conditions in the minimize frame.
    for &column in basis {
        if !reduced[column].is_zero() {
            return None;
        }
    }
    for column in 0..cols {
        if column.is_multiple_of(INDEX_DEADLINE_STRIDE) && expired() {
            return None;
        }
        if basis_position[column].is_some() {
            continue;
        }
        // A fixed column has no feasible direction, so either reduced-cost
        // sign is dual feasible.  The proof below cites the lower or upper
        // fact selected by that sign; both are tight at this vertex.  Decide
        // fixedness in exact arithmetic because a rounded equality may be a
        // genuine range (or vice versa) in the model side store.
        if lower[column]
            .as_ref()
            .zip(upper[column].as_ref())
            .is_some_and(|(lb, ub)| lb == ub)
        {
            continue;
        }
        match at[column] {
            NbBound::Lower if reduced[column].is_negative() => return None,
            NbBound::Upper if reduced[column].is_positive() => return None,
            NbBound::Zero if !reduced[column].is_zero() => return None,
            _ => {}
        }
    }

    // Orient non-zero reduced costs onto public model facts. The final replay
    // below is the authority: construction alone never licenses a verdict.
    let mut multipliers = Vec::new();
    for column in 0..cols {
        if column.is_multiple_of(INDEX_DEADLINE_STRIDE) && expired() {
            return None;
        }
        if basis_position[column].is_some() || reduced[column].is_zero() {
            continue;
        }
        let coefficient = &reduced[column];
        let (fact, magnitude) = if column < n {
            let col = Col(column as u32);
            if coefficient.is_positive() {
                (
                    FactRef::ColBound {
                        col,
                        side: BoundSide::Lower,
                    },
                    coefficient.clone(),
                )
            } else {
                (
                    FactRef::ColBound {
                        col,
                        side: BoundSide::Upper,
                    },
                    -coefficient.clone(),
                )
            }
        } else {
            let row = Row((column - n) as u32);
            if coefficient.is_positive() {
                (
                    FactRef::RowBound {
                        row,
                        side: BoundSide::Lower,
                    },
                    coefficient.clone(),
                )
            } else {
                (
                    FactRef::RowBound {
                        row,
                        side: BoundSide::Upper,
                    },
                    -coefficient.clone(),
                )
            }
        };
        multipliers.push(Multiplier {
            fact,
            coeff: magnitude,
        });
    }

    let mut value = BigRational::zero();
    for (column, coefficient) in user_cost.iter().enumerate() {
        if column.is_multiple_of(INDEX_DEADLINE_STRIDE) && expired() {
            return None;
        }
        if !coefficient.is_zero() && !z[column].is_zero() {
            value += coefficient * &z[column];
        }
    }
    let cert = OptimalityCertificate {
        sense: model.sense(),
        objective: user_cost
            .into_iter()
            .enumerate()
            .filter(|(_, coefficient)| !coefficient.is_zero())
            .map(|(column, coefficient)| (column as u32, coefficient))
            .collect(),
        bound: value.clone(),
        multipliers,
    };
    if expired() {
        return None;
    }
    cert.verify_with_deadline(model, deadline).ok()?;
    if expired() {
        return None;
    }

    Some(CertifiedOptimum {
        values: z[..n].to_vec(),
        value,
        cert,
    })
}

#[cfg(test)]
mod true_model_basis_tests {
    use super::*;
    use num_traits::One;

    fn rat(numerator: i64, denominator: i64) -> BigRational {
        BigRational::new(numerator.into(), denominator.into())
    }

    #[test]
    fn exact_side_stores_own_the_vertex_objective_and_certificate() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 10.0);
        let row = model.add_row(2.0 / 3.0, 2.0 / 3.0, &[(x, 1.0 / 3.0)]);
        model.record_inexact_row_coeff(row, x.0, rat(1, 3));
        model.record_inexact_row_bound(row, true, rat(2, 3));
        model.record_inexact_row_bound(row, false, rat(2, 3));
        model.set_objective(&[(x, 5.0 / 7.0)], Sense::Minimize);
        model.record_inexact_obj_coeff(x.0, rat(5, 7));
        // CertifiedOptimum and the certificate deliberately exclude offsets.
        model.set_objective_offset(11.0);

        // x is basic; the equality logical is nonbasic at its lower side.
        let proven = certify_model_basis_with_deadline(
            &model,
            &[x.index()],
            &[NbBound::Zero, NbBound::Lower],
            None,
        )
        .expect("the exact true-model basis is optimal");

        assert_eq!(proven.values, vec![rat(2, 1)]);
        assert_eq!(proven.value, rat(10, 7));
        assert_eq!(proven.cert.objective, vec![(x.0, rat(5, 7))]);
        assert_eq!(proven.cert.bound, rat(10, 7));
        proven
            .cert
            .verify(&model)
            .expect("the public checker must accept the emitted identity");
        model
            .check_point(&proven.values)
            .expect("the reconstructed point must satisfy the true row");
    }

    #[test]
    fn maximize_basis_is_certified_in_the_callers_sense() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 2.0);
        model.set_objective(&[(x, 1.0)], Sense::Maximize);

        let proven = certify_model_basis_with_deadline(&model, &[], &[NbBound::Upper], None)
            .expect("max x over [0,2] has an exact upper-bound proof");
        assert_eq!(proven.values, vec![rat(2, 1)]);
        assert_eq!(proven.value, rat(2, 1));
        assert_eq!(proven.cert.sense, Sense::Maximize);
        proven.cert.verify(&model).unwrap();
    }

    #[test]
    fn fixed_nonbasic_may_use_either_exact_bound_side() {
        let mut model = Model::new();
        let x = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        model.add_row(1.0, 1.0, &[(x, 1.0)]);
        model.set_objective(&[(x, -1.0)], Sense::Minimize);

        // The equality logical is fixed at 1 and stored as `Lower`, while its
        // exact reduced cost is negative. It has no feasible direction; the
        // valid proof therefore uses the same fixed fact's upper orientation.
        let proven = certify_model_basis_with_deadline(
            &model,
            &[x.index()],
            &[NbBound::Zero, NbBound::Lower],
            None,
        )
        .expect("a fixed nonbasic accepts either reduced-cost sign");
        assert_eq!(proven.values, vec![BigRational::one()]);
        assert_eq!(proven.value, -BigRational::one());
        assert!(matches!(
            proven.cert.multipliers.as_slice(),
            [Multiplier {
                fact: FactRef::RowBound {
                    side: BoundSide::Upper,
                    ..
                },
                ..
            }]
        ));
        proven.cert.verify(&model).unwrap();
    }

    #[test]
    fn malformed_basis_and_resting_vectors_decline() {
        let mut model = Model::new();
        let x = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let y = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        model.add_row(0.0, 0.0, &[(x, 1.0)]);
        model.add_row(0.0, 0.0, &[(y, 1.0)]);
        let at = [NbBound::Zero, NbBound::Zero, NbBound::Lower, NbBound::Lower];

        assert!(certify_model_basis_with_deadline(&model, &[x.index()], &at, None).is_none());
        assert!(
            certify_model_basis_with_deadline(&model, &[x.index(), x.index()], &at, None).is_none()
        );
        assert!(certify_model_basis_with_deadline(&model, &[x.index(), 4], &at, None).is_none());
        assert!(
            certify_model_basis_with_deadline(&model, &[x.index(), y.index()], &at[..3], None)
                .is_none()
        );
    }

    #[test]
    fn true_singular_basis_declines() {
        let mut model = Model::new();
        let x = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let y = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let row = model.add_row(0.0, 0.0, &[(x, 1.0)]);
        model.record_inexact_row_coeff(row, x.0, BigRational::zero());
        model.add_row(0.0, 0.0, &[(y, 1.0)]);
        let at = [NbBound::Zero, NbBound::Zero, NbBound::Lower, NbBound::Lower];

        assert!(
            certify_model_basis_with_deadline(&model, &[x.index(), y.index()], &at, None).is_none(),
            "the rounded proxy is nonsingular, but the authoritative zero is not"
        );
    }

    #[test]
    fn exactly_primal_infeasible_basis_declines() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        model.add_row(2.0, 2.0, &[(x, 1.0)]);

        assert!(
            certify_model_basis_with_deadline(
                &model,
                &[x.index()],
                &[NbBound::Zero, NbBound::Lower],
                None,
            )
            .is_none(),
            "the basis equation puts x=2 outside its true column box"
        );
        assert!(
            certify_model_basis_with_deadline(
                &model,
                &[model.num_cols()],
                &[NbBound::Zero, NbBound::Zero],
                None,
            )
            .is_none(),
            "a bounded nonbasic cannot masquerade as a free column at zero"
        );
    }

    #[test]
    fn exactly_dual_infeasible_basis_declines() {
        let mut model = Model::new();
        let x = model.add_col(0.0, 1.0);
        model.set_objective(&[(x, 1.0)], Sense::Minimize);
        assert!(
            certify_model_basis_with_deadline(&model, &[], &[NbBound::Upper], None).is_none(),
            "positive reduced cost at an upper bound is not dual feasible"
        );

        // The rounded objective says lower is optimal; the exact objective says
        // upper is. The side store, not the float advice, must decide.
        model.record_inexact_obj_coeff(x.0, -BigRational::one());
        assert!(
            certify_model_basis_with_deadline(&model, &[], &[NbBound::Lower], None).is_none(),
            "a proxy-optimal basis must decline under the true objective"
        );
    }

    #[test]
    fn expired_deadline_declines_before_certification() {
        let mut model = Model::new();
        model.add_col(0.0, 1.0);
        assert!(certify_model_basis_with_deadline(
            &model,
            &[],
            &[NbBound::Lower],
            Some(std::time::Instant::now()),
        )
        .is_none());
    }
}

/// As [`certify`], but under a branch-and-bound node's tightened bounds and a
/// caller deadline.
///
/// The certificate is checked against the original `model`; it proves a
/// statement about the node, so callers must use it only for that node. The
/// two exact dense solves inside are the whole cost, and until this
/// existed neither could be interrupted — see [`solve_dense_by`] for the
/// measured `control30-3-2-3` overrun that made a 600 ms lane slice into a
/// 15.9 s one on a 3 s budget. Expiry returns `None`, which is the ordinary
/// "no certificate available" answer every caller already handles.
pub(crate) fn certify_bounded_by(
    model: &Model,
    lp: &FloatLp,
    cand: &Candidate,
    lower: &[f64],
    upper: &[f64],
    deadline: Option<std::time::Instant>,
) -> Option<CertifiedOptimum> {
    let expired = || deadline.is_some_and(|limit| std::time::Instant::now() >= limit);
    let n = lp.n;
    let m = lp.m;
    if m > MAX_EXACT_BASIS_ROWS || expired() {
        return None;
    }
    // The engine minimizes; a Maximize model was negated on the way in. Work in
    // that same minimize frame and un-negate at the end, so every sign rule here
    // is the textbook one.
    let minimize_cost = |j: usize| -> Option<BigRational> { exact(lp.cost[j]) };

    // O(1) basic test; `basis.contains` would make every sweep below quadratic.
    let mut is_basic = vec![false; lp.cols];
    for (index, &j) in cand.basis.iter().enumerate() {
        if index & 0x3f == 0 && expired() {
            return None;
        }
        if j >= lp.cols || is_basic[j] {
            return None; // malformed basis: duplicate or out-of-range column
        }
        is_basic[j] = true;
    }

    // --- Non-basic values (exact). A column resting on a bound must HAVE that
    //     bound; a free column rests at zero. ---
    let mut z = vec![BigRational::zero(); lp.cols]; // full [x ; s]
    for j in 0..lp.cols {
        if j & 0xff == 0 && expired() {
            return None;
        }
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
            if j & 0xff == 0 && expired() {
                return None;
            }
            if is_basic[j] || z[j].is_zero() {
                continue;
            }
            for (r, a) in m_column(lp, j) {
                rhs[r] -= a * &z[j];
            }
        }
        let mut bmat = vec![vec![BigRational::zero(); m]; m];
        for (k, &j) in cand.basis.iter().enumerate() {
            if k & 0x3f == 0 && expired() {
                return None;
            }
            for (r, a) in m_column(lp, j) {
                bmat[r][k] = a;
            }
        }
        let xb = solve_dense_by(bmat, rhs, deadline)?;
        for (k, &j) in cand.basis.iter().enumerate() {
            if k & 0x3f == 0 && expired() {
                return None;
            }
            z[j] = xb[k].clone();
        }
        // Primal feasibility of the basics. (Non-basics sit on their bounds by
        // construction.)
        let trace = std::env::var_os("AY_MILP_TRACE").is_some();
        for (index, &j) in cand.basis.iter().enumerate() {
            if index & 0x3f == 0 && expired() {
                return None;
            }
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
            if k & 0x3f == 0 && expired() {
                return None;
            }
            for (r, a) in m_column(lp, j) {
                bt[k][r] = a; // transpose
            }
        }
        let cb: Option<Vec<BigRational>> = cand.basis.iter().map(|&j| minimize_cost(j)).collect();
        y = solve_dense_by(bt, cb?, deadline)?;
    }

    // --- Reduced costs, and dual feasibility. ---
    // d_j = c_j - y·M_j. A logical's column is -e_r with zero cost, so its
    // reduced cost is simply y_r.
    let mut d = vec![BigRational::zero(); lp.cols];
    for j in 0..lp.cols {
        if j & 0xff == 0 && expired() {
            return None;
        }
        let mut dot = BigRational::zero();
        for (r, a) in m_column(lp, j) {
            dot += a * &y[r];
        }
        d[j] = minimize_cost(j)? - dot;
    }
    for j in 0..lp.cols {
        if j & 0xff == 0 && expired() {
            return None;
        }
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
        if j & 0xff == 0 && expired() {
            return None;
        }
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
        if j & 0xff == 0 && expired() {
            return None;
        }
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
    if expired() {
        return None;
    }
    cert.verify_with_deadline(model, deadline).ok()?;
    if expired() {
        return None;
    }

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

/// The same exact factorization as [`ExactLu`], held SPARSE.
///
/// ## Why this exists: `m` was never a time budget, it was a MEMORY budget
///
/// [`ExactLu`] consumes a DENSE `Vec<Vec<Rational>>`, and the GMI separator built
/// one unconditionally — `vec![vec![Rational::zero(); m]; m]`, m² rationals to
/// hold a basis with `O(nnz)` non-zeros in it, and allocated BEFORE the deadline
/// was consulted, so an ALREADY-EXPIRED deadline still paid for it in full.
/// Measured peak RSS, dense against this, **3 repetitions each** (the root cut
/// loop is DEADLINE-bound, so a single observation of anything is worthless on a
/// contended box — see the note on the digest below):
///
/// ```text
///   instance          m      sparse MB (x3)      dense MB (x3)           ratio
///   haprp         1,048   18.8 / 18.7 / 19.7   49.7 /   50.4 /   49.7     2.7x
///   railway_8_1_0 2,527   16.8 / 16.6 / 18.1  186.2 /  348.9 /  186.3      11x
///   h80x6320d     6,558   53.2 / 65.1 / 57.2 1146.8 / 2124.6 / 1861.4      32x
///   decomp2      10,765   73.5 / 84.3 / 77.7 3128.9 / 4423.1 / 3329.5      43x
/// ```
///
/// The sparse arm is essentially FLAT in `m` — 17 MB to 78 MB across a 10x range,
/// and most of that is the model, not the factorization. The dense arm goes 50 MB
/// to 3.3 GB over the same range, 66x for 10.3x in `m`, and its own spread comes
/// from completing a different NUMBER of cut rounds (each round allocates a fresh
/// `m²` at a slightly larger `m`). It gets worse than `24·m²` per entry as bit
/// growth boxes the rationals; extrapolated to the corpus's largest model (169,576
/// rows) it is ~1 PB.
///
/// The 600-row cap in `cuts.rs` documented itself as a TIME budget ("its LU is
/// dense and cubic and runs once per cut round"), and a cost-curve study over 173
/// uncapped calls refuted that. Spearman rho of factor seconds against `m` is
/// +0.82, but `m` is useless for MAGNITUDE — within `m ∈ [900,1400]` the
/// factorisation spans 0.0007s to 0.2897s (414x), the single most expensive
/// factorisation in the sweep was at m=996 (1.0437s), and m=2313 factored in
/// 0.0232s. Every expensive factorisation sits BELOW any middling cap, so the cap
/// never protected against one. The DEADLINE governs the time and was measured
/// doing it: 28 of those 173 calls aborted inside `factor_with_deadline`, worst
/// overrun anywhere 1.0437s. What `m` governed was the allocation above — remove
/// it and the cap has nothing left to protect.
///
/// ## Markowitz, not the natural order
///
/// [`ExactLu`] pivots on the first non-zero in column order. That rule is free
/// only because it runs on a dense array, where fill-in costs nothing that was
/// not already paid; on a sparse representation the pivot order is exactly what
/// decides whether the factors STAY sparse. [`solve_sparse`] already measured
/// what fixed-order elimination does to a real basis — a near-triangular big-M
/// DAG "densified it into a blow-up that never returned" — so the pivot here is
/// the least Markowitz count `(row_nnz−1)·(col_nnz−1)`, the same rule and for the
/// same reason.
///
/// ## Why the cuts do not move
///
/// A simplex basis is NON-SINGULAR, so `Bᵀ u = e_i` has exactly one solution, and
/// this arithmetic is exact — no rounding exists for two pivot orders to disagree
/// about, so any non-zero pivot sequence reaches that same `u`. The pivot order is
/// therefore free: it buys sparsity and cannot buy a different answer. A singular
/// basis declines either way (no admissible pivot here, no non-zero in the column
/// there). None of this is left as an argument: `AY_MILP_DENSE_GMI_LU=1` restores
/// the dense path, the tests below require byte-equal solutions from both over
/// random, near-triangular and deliberately fill-prone systems, and the corpus A/B
/// was run with the switch as the only difference.
pub(crate) struct SparseExactLu {
    /// Step `k`'s multipliers as `(earlier step, f)`, ascending in step. The unit
    /// diagonal is implicit, exactly as [`ExactLu`]'s below-diagonal storage is.
    l: Vec<Vec<(u32, ay_lra::rational::Rational)>>,
    /// Step `k`'s reduced pivot row MINUS its pivot entry — by construction only
    /// columns pivoted LATER survive there, which is what makes the back-solve a
    /// back-solve.
    u: Vec<Vec<(u32, ay_lra::rational::Rational)>>,
    /// Step `k`'s pivot entry, lifted out of `u[k]` so the back-solve never
    /// searches a row for its own diagonal.
    diag: Vec<ay_lra::rational::Rational>,
    /// Original row / column index of step `k`'s pivot: the two permutations.
    pivot_row: Vec<u32>,
    pivot_col: Vec<u32>,
    n: usize,
}

/// How many candidate rows the Markowitz search examines before settling for the
/// best it has seen. FULL Markowitz — [`solve_sparse`]'s rule — rescans every live
/// non-zero at every pivot, which is `O(n · nnz)` over a factorization and was
/// affordable there only because that lane is capped at a few hundred rows. This
/// path is meant to run at m in the thousands, so the search is bounded: rows are
/// visited in increasing length (the cheapest rows to eliminate with, and the ones
/// Markowitz prefers anyway), a singleton wins immediately, and eight candidates
/// is where the search stops. Correctness is indifferent — any non-zero pivot is
/// exact — so this trades nothing but fill.
const MARKOWITZ_CANDIDATES: usize = 8;

/// Rows between deadline checks inside ONE pivot's elimination sweep. [`ExactLu`]
/// checks once per pivot column, which was proportionate when a pivot touched at
/// most 600 rows; at m in the thousands a single sweep is long enough to overrun a
/// round on its own. `Instant::now` against a rational row update is noise.
const SPARSE_LU_DEADLINE_STRIDE: usize = 64;

/// The FILL BUDGET: stored non-zeros this factorization may hold, across the live
/// rows and both factors, before it declines.
///
/// This is the guard the 600-row cap was a PROXY for, stated directly. The
/// deadline bounds the TIME and cannot bound the memory: fill-in is allocated as
/// it is created, and a factorization that blows up to `O(m²)` reaches the
/// blow-up before it reaches a clock check. A row count cannot bound it either —
/// that is the same "cheap quantity stands in for the real cost" shape
/// the development design notes names, and the
/// reason a 600-row time budget was denying the primary cut family to 63% of the
/// corpus while the genuinely expensive factorisations sat below it.
///
/// So the budget counts the thing it is protecting: entries. At 32 bytes for a
/// `(u32, Rational)` slot this is 512 MiB of table on an inline-rational
/// factorization, and MEASURED FILL on real bases is nowhere near it — Markowitz
/// keeps these factorizations essentially fill-free:
///
/// ```text
///   instance    m       basis nnz   factor nnz   fill    m² (the dense array)
///   air05        426        2,387        3,819   1.60x            181,476
///   haprp      1,048        2,450        2,450   1.00x          1,098,304
///   h80x6320d  6,558        7,012        7,012   1.00x         43,007,364
///   decomp2   10,765       24,928       25,073   1.01x        115,885,225
/// ```
///
/// decomp2's factorization is **4,623x smaller than the array the dense path
/// allocated for the same basis**, and the budget is 669x above it. What the
/// budget adds is not headroom, it is a BOUND: fill has no cheap a-priori model
/// either, so the only honest guard is to count the entries as they are created
/// and stop. Declining is FAIL-CLOSED — it costs the round its GMI cuts, never a
/// wrong one.
const SPARSE_LU_MAX_NNZ: usize = 16_777_216;

impl SparseExactLu {
    /// Factor `rows` (consumed; row `i` given as `(column, value)` pairs in any
    /// order, duplicates resolved LAST-WINS to match the dense builder's repeated
    /// `bt[k][r] = a` store). `None` if singular — or if `deadline` passes
    /// mid-elimination.
    pub(crate) fn factor_with_deadline(
        rows: Vec<Vec<(u32, ay_lra::rational::Rational)>>,
        deadline: Option<std::time::Instant>,
    ) -> Option<Self> {
        Self::factor_with_limits(rows, deadline, SPARSE_LU_MAX_NNZ)
    }

    /// [`Self::factor_with_deadline`] with the fill budget spelled out, so a test
    /// can reach the decline without building half a gigabyte of matrix.
    pub(crate) fn factor_with_limits(
        rows: Vec<Vec<(u32, ay_lra::rational::Rational)>>,
        deadline: Option<std::time::Instant>,
        max_nnz: usize,
    ) -> Option<Self> {
        use ay_lra::rational::Rational;
        let n = rows.len();
        // Rows held SORTED by column, non-zeros only: a lookup is a binary search,
        // an update is a linear merge, and the iteration order is DETERMINISTIC.
        // (A `HashMap` row — what `solve_sparse` uses — would make the Markowitz
        // tie-break depend on the process's hash seed, and nodes-to-proof is a
        // determinism contract in this engine, not a nicety.)
        let mut a: Vec<Vec<(u32, Rational)>> = Vec::with_capacity(n);
        for mut row in rows {
            row.sort_by_key(|(c, _)| *c);
            // Keep the LAST of each run of equal columns, in place and still
            // ascending — the dense builder's last write to `bt[k][r]` won.
            let mut w = 0;
            for i in 0..row.len() {
                if i + 1 < row.len() && row[i + 1].0 == row[i].0 {
                    continue;
                }
                row.swap(w, i);
                w += 1;
            }
            row.truncate(w);
            // A stored exact zero is the same matrix as an absent entry, and the
            // sparse invariant is that only non-zeros are present.
            row.retain(|(c, v)| {
                debug_assert!((*c as usize) < n, "column out of range");
                !v.is_zero()
            });
            if row.is_empty() {
                return None; // an all-zero row is a singular basis
            }
            a.push(row);
        }

        // Live occurrences per column, and which rows hold them. `col_rows` is
        // allowed to go STALE (a row that cancelled its entry away stays listed);
        // every consumer re-checks with a binary search, and the alternative —
        // deleting from the middle of an occurrence list — costs more than the
        // occasional wasted probe.
        let mut col_nnz = vec![0u32; n];
        let mut col_rows: Vec<Vec<u32>> = vec![Vec::new(); n];
        // Stored non-zeros, against [`SPARSE_LU_MAX_NNZ`]. Live rows plus the two
        // factors: a pivot row's entries simply move from one to the other, so the
        // running total is exactly what is resident.
        let mut nnz: usize = 0;
        for (i, row) in a.iter().enumerate() {
            nnz += row.len();
            for (c, _) in row {
                col_nnz[*c as usize] += 1;
                col_rows[*c as usize].push(i as u32);
            }
        }
        if nnz > max_nnz {
            return None;
        }
        // Rows bucketed by length, so the Markowitz search reaches the cheapest
        // rows without scanning the live set. Stale entries are dropped lazily by
        // the search itself.
        let mut by_len: Vec<Vec<u32>> = vec![Vec::new(); n + 1];
        for (i, row) in a.iter().enumerate() {
            by_len[row.len()].push(i as u32);
        }
        let mut min_len = 1usize;

        let mut used = vec![false; n];
        // Row `i`'s multipliers as they accrue; moved into `l` when `i` is pivoted.
        let mut lmul: Vec<Vec<(u32, Rational)>> = vec![Vec::new(); n];
        // Guards against a row listed twice in one occurrence list (cancel, then
        // fill back in) being eliminated twice at the same pivot.
        let mut stamp = vec![u32::MAX; n];

        let mut l = Vec::with_capacity(n);
        let mut u = Vec::with_capacity(n);
        let mut diag = Vec::with_capacity(n);
        let mut pivot_row = Vec::with_capacity(n);
        let mut pivot_col = Vec::with_capacity(n);

        for k in 0..n {
            if deadline.is_some_and(|d| std::time::Instant::now() >= d) {
                return None;
            }
            // --- Pivot: least Markowitz count among a bounded number of the
            //     shortest live rows.
            let mut best: Option<(usize, u32, u32)> = None; // (count, row, column)
            let mut seen = 0usize;
            let mut first_live = min_len;
            let mut len = min_len;
            'search: while len <= n {
                let mut idx = 0;
                while idx < by_len[len].len() {
                    let r = by_len[len][idx] as usize;
                    if used[r] || a[r].len() != len {
                        by_len[len].swap_remove(idx);
                        continue;
                    }
                    if seen == 0 {
                        first_live = len;
                    }
                    for (c, _) in &a[r] {
                        // `saturating_sub` for the same reason `solve_sparse` uses
                        // it: a live row holding `c` guarantees `col_nnz[c] >= 1`,
                        // and a mis-scored pivot must cost FILL, never a panic.
                        let mark = (len - 1) * (col_nnz[*c as usize] as usize).saturating_sub(1);
                        if best.is_none_or(|(bm, _, _)| mark < bm) {
                            best = Some((mark, r as u32, *c));
                        }
                    }
                    seen += 1;
                    if best.is_some_and(|(bm, _, _)| bm == 0) || seen >= MARKOWITZ_CANDIDATES {
                        break 'search;
                    }
                    idx += 1;
                }
                len += 1;
            }
            min_len = first_live;
            // No live row left to pivot on: the remaining submatrix has no
            // non-zero, i.e. the basis is singular.
            let (_, p, c) = best?;

            used[p as usize] = true;
            let prow = std::mem::take(&mut a[p as usize]);
            // The pivot row leaves the live set: every column it holds loses one
            // live occurrence.
            for (cc, _) in &prow {
                col_nnz[*cc as usize] -= 1;
            }
            let dpos = prow.binary_search_by_key(&c, |(cc, _)| *cc).ok()?;
            let pivot = prow[dpos].1.clone();

            // --- Eliminate column `c` from every other live row that holds it.
            let holders = std::mem::take(&mut col_rows[c as usize]);
            let mut swept = 0usize;
            for &ri in &holders {
                let r = ri as usize;
                if used[r] || stamp[r] == k as u32 {
                    continue;
                }
                let Ok(pos) = a[r].binary_search_by_key(&c, |(cc, _)| *cc) else {
                    continue; // stale listing: the entry cancelled away earlier
                };
                stamp[r] = k as u32;
                if swept.is_multiple_of(SPARSE_LU_DEADLINE_STRIDE)
                    && deadline.is_some_and(|d| std::time::Instant::now() >= d)
                {
                    return None;
                }
                swept += 1;

                let f = &a[r][pos].1 / &pivot;
                // row_r := row_r − f·row_p, as a merge of two ascending runs. One
                // allocation per elimination, against the m² the dense path paid
                // before it read its first coefficient.
                let mut old = std::mem::take(&mut a[r]);
                let mut new: Vec<(u32, Rational)> = Vec::with_capacity(old.len() + prow.len());
                let (mut ia, mut ip) = (0usize, 0usize);
                while ia < old.len() && ip < prow.len() {
                    let (ca, cp) = (old[ia].0, prow[ip].0);
                    if ca == cp {
                        if ca == c {
                            // The pivot column cancels EXACTLY —
                            // `a_rc − (a_rc/pivot)·pivot` — so it is dropped, never
                            // computed.
                            col_nnz[c as usize] -= 1;
                        } else {
                            let v = &old[ia].1 - &(&f * &prow[ip].1);
                            if v.is_zero() {
                                col_nnz[ca as usize] -= 1;
                            } else {
                                new.push((ca, v));
                            }
                        }
                        ia += 1;
                        ip += 1;
                    } else if ca < cp {
                        new.push((ca, std::mem::take(&mut old[ia].1)));
                        ia += 1;
                    } else {
                        // Fill-in. `f` and `prow[ip].1` are both non-zero, so this
                        // term cannot be a zero worth testing for.
                        new.push((cp, -(&f * &prow[ip].1)));
                        col_nnz[cp as usize] += 1;
                        col_rows[cp as usize].push(ri);
                        ip += 1;
                    }
                }
                while ia < old.len() {
                    new.push((old[ia].0, std::mem::take(&mut old[ia].1)));
                    ia += 1;
                }
                while ip < prow.len() {
                    new.push((prow[ip].0, -(&f * &prow[ip].1)));
                    col_nnz[prow[ip].0 as usize] += 1;
                    col_rows[prow[ip].0 as usize].push(ri);
                    ip += 1;
                }
                if new.is_empty() {
                    return None; // a live row with nothing in it: singular
                }
                // Fill accounting: the row's own delta, plus the multiplier that
                // just joined L. Checked per row, not per pivot — one runaway sweep
                // is all it takes.
                nnz = nnz + new.len() + 1 - old.len();
                if nnz > max_nnz {
                    return None;
                }
                by_len[new.len()].push(ri);
                min_len = min_len.min(new.len());
                a[r] = new;
                lmul[r].push((k as u32, f));
            }

            let mut urow = prow;
            let d = urow.remove(dpos).1;
            l.push(std::mem::take(&mut lmul[p as usize]));
            u.push(urow);
            diag.push(d);
            pivot_row.push(p);
            pivot_col.push(c);
        }

        Some(Self {
            l,
            u,
            diag,
            pivot_row,
            pivot_col,
            n,
        })
    }

    /// Solve `A z = b` using the stored factors. `b` and the returned `z` are both
    /// in ORIGINAL index space — the two permutations stay inside.
    pub(crate) fn solve(
        &self,
        b: &[ay_lra::rational::Rational],
    ) -> Vec<ay_lra::rational::Rational> {
        use ay_lra::rational::Rational;
        let n = self.n;
        let fused = exact_lu_fma_enabled();
        // Forward: y_k = b[pivot_row[k]] − Σ_{k'<k} L[k][k']·y_{k'}.
        let mut y = vec![Rational::zero(); n];
        for k in 0..n {
            let mut acc = b[self.pivot_row[k] as usize].clone();
            for (kk, f) in &self.l[k] {
                let yv = &y[*kk as usize];
                if !yv.is_zero() {
                    acc -= if fused { f * yv } else { f.clone() * yv };
                }
            }
            y[k] = acc;
        }
        // Back: z[pivot_col[k]] = (y_k − Σ U[k]·z) / diag_k, over columns pivoted
        // later — whose `z` this loop has therefore already produced.
        let mut z = vec![Rational::zero(); n];
        for k in (0..n).rev() {
            let mut acc = std::mem::take(&mut y[k]);
            for (cc, v) in &self.u[k] {
                let zv = &z[*cc as usize];
                if !zv.is_zero() {
                    acc -= if fused { v * zv } else { v.clone() * zv };
                }
            }
            z[self.pivot_col[k] as usize] = &acc / &self.diag[k];
        }
        z
    }

    /// Stored non-zeros across both factors — what the dense path spent `m²` on.
    /// Diagnostic (`AY_MILP_TRACE`), and the number the row cap's replacement
    /// argument rests on.
    pub(crate) fn factor_nnz(&self) -> usize {
        self.l.iter().map(Vec::len).sum::<usize>()
            + self.u.iter().map(Vec::len).sum::<usize>()
            + self.n
    }
}

#[cfg(test)]
mod sparse_exact_lu_tests {
    use super::{ExactLu, SparseExactLu};
    use ay_lra::rational::Rational;
    use num_traits::Zero;

    /// Deterministic LCG — a fixed seed makes any failure reproducible, and this
    /// crate's workflow forbids wall-clock or OS entropy in a test.
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

    fn to_sparse(dense: &[Vec<Rational>]) -> Vec<Vec<(u32, Rational)>> {
        dense
            .iter()
            .map(|row| {
                row.iter()
                    .enumerate()
                    .filter(|(_, v)| !v.is_zero())
                    .map(|(c, v)| (c as u32, v.clone()))
                    .collect()
            })
            .collect()
    }

    /// THE IDENTITY BAR. The sparse factorization must reach the SAME solvability
    /// verdict and, when it solves, byte-identical rationals — and that solution
    /// must have an exactly-zero residual against the original system, so the two
    /// cannot agree on a wrong answer.
    fn assert_agrees(dense: &[Vec<Rational>], b: &[Rational]) {
        let d = ExactLu::factor_with_deadline(dense.to_vec(), None);
        let s = SparseExactLu::factor_with_deadline(to_sparse(dense), None);
        assert_eq!(
            d.is_some(),
            s.is_some(),
            "dense and sparse disagreed on singularity"
        );
        let (Some(d), Some(s)) = (d, s) else { return };
        let zd = d.solve(b);
        let zs = s.solve(b);
        assert_eq!(zd, zs, "dense and sparse solutions differ");
        for (i, row) in dense.iter().enumerate() {
            let mut acc = Rational::zero();
            for (c, v) in row.iter().enumerate() {
                if !v.is_zero() && !zs[c].is_zero() {
                    acc += v * &zs[c];
                }
            }
            assert_eq!(acc, b[i], "row {i} residual is not exactly zero");
        }
    }

    fn rat(n: i64, d: i64) -> Rational {
        Rational::new(n, d)
    }

    #[test]
    fn matches_dense_on_random_dominant_systems() {
        let mut rng = Lcg(0x5eed_0000_0000_0001);
        for _ in 0..300 {
            let n = rng.range(1, 9) as usize;
            let mut a: Vec<Vec<Rational>> = (0..n)
                .map(|_| {
                    (0..n)
                        .map(|_| rat(rng.range(-4, 4), rng.range(1, 4)))
                        .collect()
                })
                .collect();
            // Big diagonal ⇒ strictly diagonally dominant ⇒ non-singular.
            for (i, row) in a.iter_mut().enumerate() {
                row[i] = rat(100 + rng.range(0, 9), 1);
            }
            let b: Vec<Rational> = (0..n)
                .map(|_| rat(rng.range(-6, 6), rng.range(1, 3)))
                .collect();
            assert_agrees(&a, &b);
        }
    }

    /// The shape the separator actually hands it: a simplex basis is mostly
    /// LOGICAL columns (a single −1) with a minority of structural ones. This is
    /// also the shape where the two pivot rules diverge most — the dense rule
    /// takes the first non-zero in column order, Markowitz takes the singletons
    /// first — so it is the strongest place to insist the answers agree.
    #[test]
    fn matches_dense_on_basis_shaped_systems() {
        let mut rng = Lcg(0xba51_5000_0000_000d);
        for _ in 0..300 {
            let n = rng.range(2, 24) as usize;
            let mut a: Vec<Vec<Rational>> = vec![vec![Rational::zero(); n]; n];
            for (k, row) in a.iter_mut().enumerate() {
                if rng.range(0, 3) == 0 {
                    // A structural column: a handful of entries anywhere.
                    let nz = rng.range(1, 4) as usize;
                    for _ in 0..nz {
                        let c = rng.range(0, n as i64 - 1) as usize;
                        row[c] = rat(rng.range(-5, 5), rng.range(1, 3));
                    }
                    // Keep the diagonal occupied so the basis stays non-singular
                    // far more often than not; the singular draws are covered by
                    // the agreement assertion either way.
                    row[k] = rat(rng.range(1, 9), 1);
                } else {
                    row[k] = rat(-1, 1); // a logical column
                }
            }
            let b: Vec<Rational> = (0..n)
                .map(|_| rat(rng.range(-9, 9), rng.range(1, 4)))
                .collect();
            assert_agrees(&a, &b);
        }
    }

    /// The blow-up shape `solve_sparse` documents: a near-triangular DAG whose
    /// NATURAL column order fills in badly. The dense reference still has to agree
    /// with it, which is the point — the pivot order is free, the answer is not.
    #[test]
    fn matches_dense_on_arrow_and_reversed_triangular_systems() {
        let n = 40;
        // Reversed triangular: the natural first-non-zero rule pivots on the
        // densest column available, Markowitz pivots on the singleton.
        let mut a: Vec<Vec<Rational>> = vec![vec![Rational::zero(); n]; n];
        for (i, row) in a.iter_mut().enumerate() {
            row[i] = rat(1, 1);
            for (j, cell) in row.iter_mut().enumerate().take(i) {
                *cell = rat((i + j) as i64 % 3 - 1, 2);
            }
        }
        a.reverse();
        let b: Vec<Rational> = (0..n).map(|i| rat(i as i64 - 7, 3)).collect();
        assert_agrees(&a, &b);

        // Arrow: a full last row and column over a diagonal. Eliminating in the
        // natural order fills the whole trailing block; a Markowitz order does not.
        let mut arrow: Vec<Vec<Rational>> = vec![vec![Rational::zero(); n]; n];
        for i in 0..n {
            arrow[i][i] = rat(3, 1);
            arrow[i][n - 1] = rat(1, 1);
            arrow[n - 1][i] = rat(1, 1);
        }
        arrow[n - 1][n - 1] = rat(n as i64 + 5, 1);
        assert_agrees(&arrow, &b);
    }

    #[test]
    fn singular_systems_decline_on_both_paths() {
        // A duplicated row.
        let a = vec![
            vec![rat(1, 1), rat(2, 1), rat(3, 1)],
            vec![rat(1, 1), rat(2, 1), rat(3, 1)],
            vec![rat(0, 1), rat(1, 1), rat(1, 1)],
        ];
        assert_agrees(&a, &[rat(1, 1), rat(1, 1), rat(1, 1)]);
        assert!(SparseExactLu::factor_with_deadline(to_sparse(&a), None).is_none());

        // An all-zero row, and a zero COLUMN (nothing to pivot on at the end).
        let zrow = vec![vec![rat(1, 1), rat(1, 1)], vec![rat(0, 1), rat(0, 1)]];
        assert_agrees(&zrow, &[rat(1, 1), rat(0, 1)]);
        let zcol = vec![vec![rat(1, 1), rat(0, 1)], vec![rat(2, 1), rat(0, 1)]];
        assert_agrees(&zcol, &[rat(1, 1), rat(0, 1)]);

        // Rank-deficient only AFTER elimination: the cancellation has to be seen,
        // not predicted from the pattern.
        let late = vec![
            vec![rat(1, 1), rat(1, 1), rat(0, 1)],
            vec![rat(2, 1), rat(2, 1), rat(1, 1)],
            vec![rat(3, 1), rat(3, 1), rat(1, 1)],
        ];
        assert_agrees(&late, &[rat(1, 1), rat(1, 1), rat(2, 1)]);
        assert!(SparseExactLu::factor_with_deadline(to_sparse(&late), None).is_none());
    }

    /// An exact zero handed in as a stored entry is the same matrix as an absent
    /// one, and a repeated column resolves LAST-WINS — the semantics of the dense
    /// builder's repeated `bt[k][r] = a` store, which the sparse assembly replaced.
    #[test]
    fn stored_zeros_and_duplicate_columns_match_the_dense_store() {
        let rows = vec![
            vec![(1u32, rat(5, 1)), (0, rat(9, 1)), (0, rat(2, 1))],
            vec![(0u32, rat(0, 1)), (1, rat(4, 1))],
        ];
        let f = SparseExactLu::factor_with_deadline(rows, None).expect("non-singular");
        let z = f.solve(&[rat(1, 1), rat(1, 1)]);
        // Last write wins: row 0 is `2·x0 + 5·x1`, not `9·x0 + 5·x1`.
        let dense = vec![
            vec![rat(2, 1), rat(5, 1)],
            vec![Rational::zero(), rat(4, 1)],
        ];
        let d = ExactLu::factor_with_deadline(dense, None).expect("non-singular");
        assert_eq!(z, d.solve(&[rat(1, 1), rat(1, 1)]));
    }

    /// THE MEMORY GUARD, stated directly rather than proxied by a row count. The
    /// deadline cannot do this job: fill is allocated as it is created, so a
    /// blow-up arrives before the next clock check. Declining is fail-closed — the
    /// round loses its GMI cuts, never gets a wrong one.
    #[test]
    fn the_fill_budget_declines_instead_of_allocating() {
        // A dense 30x30: 900 live entries before a single pivot.
        let dense: Vec<Vec<(u32, Rational)>> = (0..30)
            .map(|i| {
                (0..30)
                    .map(|j| (j as u32, rat(if i == j { 40 } else { 1 }, 1)))
                    .collect()
            })
            .collect();
        assert!(
            SparseExactLu::factor_with_limits(dense.clone(), None, 899).is_none(),
            "an input that already exceeds the budget must decline, not allocate"
        );
        assert!(
            SparseExactLu::factor_with_limits(dense.clone(), None, usize::MAX).is_some(),
            "the same matrix factors when the budget allows it"
        );
        // A CIRCULANT, which no pivot order keeps sparse: a budget between the
        // input size and the factored size has to fire MID-elimination, which is
        // the case a check-on-entry would miss and the one that matters.
        let n = 60;
        let circ: Vec<Vec<(u32, Rational)>> = (0..n)
            .map(|i| {
                let mut row = vec![
                    (i as u32, rat(5, 1)),
                    (((i + 1) % n) as u32, rat(1, 1)),
                    (((i + 7) % n) as u32, rat(-2, 1)),
                ];
                row.sort_by_key(|(c, _)| *c);
                row
            })
            .collect();
        let input_nnz: usize = circ.iter().map(Vec::len).sum();
        let full = SparseExactLu::factor_with_limits(circ.clone(), None, usize::MAX)
            .expect("non-singular");
        assert!(
            full.factor_nnz() > 2 * input_nnz,
            "test is vacuous unless the factorization actually fills in (got {} from {input_nnz})",
            full.factor_nnz()
        );
        assert!(
            SparseExactLu::factor_with_limits(circ, None, input_nnz + 8).is_none(),
            "a budget below the factored size must fire mid-elimination"
        );
    }

    #[test]
    fn an_expired_deadline_declines_before_any_elimination() {
        let a = vec![vec![rat(2, 1), rat(1, 1)], vec![rat(1, 1), rat(3, 1)]];
        assert!(SparseExactLu::factor_with_deadline(
            to_sparse(&a),
            Some(std::time::Instant::now())
        )
        .is_none());
        assert!(SparseExactLu::factor_with_deadline(to_sparse(&a), None).is_some());
    }

    /// The reason the change exists: the factors must be `O(nnz)`, not `O(m²)`.
    /// A logical-only basis is the extreme case (`m` singletons), and a diagonal
    /// plus one dense row is the case a natural-order elimination would densify.
    #[test]
    fn factor_stays_sparse_where_the_dense_array_would_not() {
        let n = 200;
        let mut logicals: Vec<Vec<(u32, Rational)>> = Vec::new();
        for i in 0..n {
            logicals.push(vec![(i as u32, rat(-1, 1))]);
        }
        let f = SparseExactLu::factor_with_deadline(logicals, None).expect("non-singular");
        assert_eq!(
            f.factor_nnz(),
            n,
            "a permutation must factor to its diagonal"
        );

        let mut arrow: Vec<Vec<(u32, Rational)>> = Vec::new();
        for i in 0..n - 1 {
            arrow.push(vec![(i as u32, rat(3, 1)), ((n - 1) as u32, rat(1, 1))]);
        }
        arrow.push((0..n).map(|c| (c as u32, rat(1, 1))).collect());
        let f = SparseExactLu::factor_with_deadline(arrow, None).expect("non-singular");
        assert!(
            f.factor_nnz() < n * n / 4,
            "arrow factored to {} non-zeros; the dense array would hold {}",
            f.factor_nnz(),
            n * n
        );
    }
}

#[cfg(test)]
mod weak_dual_row_tests {
    use super::*;
    use num_bigint::BigInt;
    use num_traits::One;

    fn rat(n: i64, d: i64) -> BigRational {
        BigRational::new(n.into(), d.into())
    }

    /// [`certified_weak_dual_row_big_reference_proposal`] behind the same
    /// verify-before-return contract [`certified_weak_dual_row`] enforces, so
    /// the differential comparison covers the decline conditions too.
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

/// Force every lazily-cached environment read in this module to happen NOW.
///
/// # The race this closes
///
/// `tune.rs` states the property the crate is supposed to have: *"The environment
/// layer is read **once**, into `EnvSnapshot`, and never again — so no accessor on
/// the solve path touches `std::env`."* That is true of the `tune` layer and FALSE
/// of the crate: 1 accessors here cache their value in a `OnceLock` and call
/// `env::var` **lazily**, inside `get_or_init`, the first time the solve path
/// happens to reach them — at an arbitrary point, on an arbitrary thread.
///
/// That is the exact hazard `EngineEconomics` was built to remove.
/// the development design notes records the consumer's mitigation:
/// it *"rewrites the same constant values before every window solve"*, so a
/// `set_var` on one thread can land while another thread is mid-solve taking its
/// first `getenv` here. `std::env::set_var` racing a concurrent `getenv` is why it
/// is `unsafe` in edition 2024.
///
/// Priming collapses those windows into ONE, at solve entry, before any worker is
/// spawned. It changes no value: the same `OnceLock`s resolve to the same bytes.
/// It only moves *when* they are read, from "scattered across the solve" to "once,
/// at a point the caller controls".
pub(crate) fn prime_env() {
    let _ = exact_lu_fma_enabled();
}
